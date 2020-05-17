use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::ast::{
    ADTDefinition, CaseRule, Expression, FunctionBody, FunctionDefinition, FunctionRule, Import,
    MatchExpression, RecordDefinition,
};
use crate::inferencer::TypedModule;

pub struct RuntimeModule {
    pub name: Rc<String>,
    pub functions: HashMap<Rc<String>, Rc<FunctionDefinition>>,
}

struct RewriteState {
    used_functions: HashSet<Rc<String>>,
    original_modules: HashMap<Rc<String>, Rc<TypedModule>>,
    rewritten_modules: HashMap<Rc<String>, Rc<TypedModule>>,

    variables_stack: Vec<HashSet<Rc<String>>>,
}

/*

Rewriting steps:

1. For all modules:
    a. Resolve all function calls to either a local function or an imported module
        i. There shouldn't be any conflicts due to the inferencer.
        ii. Prefix the call name with the respective module name.
        iii. Record that a function in a module is used at least once.
    b. Resolve and prefix all type constructors with their respective module

2. For all modules:
    a. Prefix defined functions with the module name
    b. Prefix defined types and type constructors with the module name
 */

impl RewriteState {
    fn new(original_modules: HashMap<Rc<String>, Rc<TypedModule>>) -> Self {
        RewriteState {
            used_functions: HashSet::new(),
            original_modules,
            rewritten_modules: HashMap::new(),

            variables_stack: Vec::new(),
        }
    }
    fn rewrite_module(&mut self, module: Rc<TypedModule>) -> Rc<TypedModule> {
        if self.rewritten_modules.contains_key(&module.module_name) {
            return Rc::clone(self.rewritten_modules.get(&module.module_name).unwrap());
        }

        let imported_modules: Vec<Rc<TypedModule>> = module
            .imports
            .iter()
            .map(|import| {
                let import_module_name = to_import_module_name(import);
                self.rewrite_module(Rc::clone(
                    self.original_modules.get(&import_module_name).unwrap(),
                ))
            })
            .collect();

        let module_aliases: HashMap<Rc<String>, Rc<String>> = module
            .imports
            .iter()
            .filter_map(|import| match import.borrow() {
                Import::ImportModule(_l, name, Some(alias)) => {
                    Some((Rc::clone(alias), Rc::clone(name)))
                }
                _ => None,
            })
            .collect();

        let rewritten_module = Rc::new(TypedModule {
            module_name: Rc::clone(&module.module_name),
            module_file_name: Rc::clone(&module.module_file_name),
            imports: module.imports.iter().map(Rc::clone).collect(),
            function_name_to_definition: module
                .function_name_to_definition
                .iter()
                .map(|(n, d)| {
                    (
                        prefix_name(n, &module.module_name),
                        self.rewrite_function_definition(
                            d,
                            true,
                            &module.module_name,
                            &imported_modules,
                            &module_aliases,
                        ),
                    )
                })
                .collect(),
            adt_name_to_definition: module
                .adt_name_to_definition
                .iter()
                .map(|(n, d)| (Rc::clone(n), Rc::clone(d)))
                .collect(),
            record_name_to_definition: module
                .record_name_to_definition
                .iter()
                .map(|(n, d)| (Rc::clone(n), Rc::clone(d)))
                .collect(),
        });
        self.rewritten_modules
            .insert(Rc::clone(&module.module_name), Rc::clone(&rewritten_module));
        return rewritten_module;
    }

    fn rewrite_adt_definition(
        &self,
        adt_definition: &Rc<ADTDefinition>,
        current_module_name: &Rc<String>,
        imported_modules: &Vec<Rc<TypedModule>>,
    ) -> Rc<ADTDefinition> {
        Rc::new(ADTDefinition {
            name: Rc::clone(&adt_definition.name),
            location: Rc::clone(&adt_definition.location),
            type_variables: adt_definition
                .type_variables
                .iter()
                .map(Rc::clone)
                .collect(),
            constructors: adt_definition
                .constructors
                .iter()
                .map(|(constructor_name, constructor_definition)| {
                    (
                        prefix_name(constructor_name, current_module_name),
                        Rc::clone(constructor_definition),
                    )
                })
                .collect(),
        })
    }

    fn rewrite_adt_constructor_name(
        &self,
        type_constructor_name: &Rc<String>,
        current_module_name: &Rc<String>,
        imported_modules: &Vec<Rc<TypedModule>>,
    ) -> Rc<String> {
        for m in imported_modules {
            let local_name = prefix_name(type_constructor_name, &m.module_name);
            for (_, adtd) in &m.adt_name_to_definition {
                for (n, _) in &adtd.constructors {
                    if n == &local_name {
                        return local_name;
                    }
                }
            }
        }

        // Not found in imported modules.. Must be a adt constructor in the current module.
        prefix_name(type_constructor_name, current_module_name)
    }

    fn rewrite_record_name(
        &self,
        type_constructor_name: &Rc<String>,
        current_module_name: &Rc<String>,
        imported_modules: &Vec<Rc<TypedModule>>,
    ) -> Rc<String> {
        for m in imported_modules {
            let local_name = prefix_name(type_constructor_name, &m.module_name);
            for (n, _) in &m.record_name_to_definition {
                if n == &local_name {
                    return local_name;
                }
            }
        }

        // Not found in imported modules.. Must be a record definition in the current module.
        prefix_name(type_constructor_name, current_module_name)
    }

    fn rewrite_record_definition(
        &self,
        record_definition: &Rc<RecordDefinition>,
        current_module_name: &Rc<String>,
        imported_modules: &Vec<Rc<TypedModule>>,
    ) -> Rc<RecordDefinition> {
        Rc::new(RecordDefinition {
            name: Rc::clone(&record_definition.name),
            location: Rc::clone(&record_definition.location),
            type_variables: record_definition.type_variables.clone(),
            fields: record_definition
                .fields
                .iter()
                .map(|(n, t)| (prefix_name(n, current_module_name), Rc::clone(t)))
                .collect(),
        })
    }

    fn rewrite_function_definition(
        &mut self,
        function_definition: &Rc<FunctionDefinition>,
        rewrite_definition_names: bool,
        current_module_name: &Rc<String>,
        imported_modules: &Vec<Rc<TypedModule>>,
        module_aliases: &HashMap<Rc<String>, Rc<String>>,
    ) -> Rc<FunctionDefinition> {
        Rc::new(FunctionDefinition {
            location: Rc::clone(&function_definition.location),
            name: if rewrite_definition_names {
                prefix_name(&function_definition.name, current_module_name)
            } else {
                Rc::clone(&function_definition.name)
            },
            function_type: function_definition.function_type.clone(),
            function_bodies: function_definition
                .function_bodies
                .iter()
                .map(|b| {
                    self.rewrite_function_body(
                        b,
                        current_module_name,
                        imported_modules,
                        module_aliases,
                    )
                })
                .collect(),
        })
    }

    fn rewrite_function_name(
        &self,
        function_name: &Rc<String>,
        current_module_name: &Rc<String>,
        imported_modules: &Vec<Rc<TypedModule>>,
        module_aliases: &HashMap<Rc<String>, Rc<String>>,
    ) -> Rc<String> {
        // Local function definitions do not need to be rewritten.
        for vars in self.variables_stack.iter().rev() {
            if vars.contains(function_name) {
                return Rc::clone(function_name);
            }
        }

        // Is already a qualified name so should be an alias for an exiting module name.
        if function_name.contains("::") {
            let mut splitter = function_name.split("::");
            let module_prefix: Rc<String> = Rc::new(splitter.next().unwrap().to_string());
            let function_name: Rc<String> = Rc::new(splitter.next().unwrap().to_string());

            let module_name = module_aliases.get(&module_prefix).unwrap();
            let mut qualified_name = String::new();
            qualified_name.push_str(module_name);
            qualified_name.push_str("::");
            qualified_name.push_str(&function_name);
            return Rc::new(qualified_name);
        }
        for m in imported_modules {
            // If the module is alias as import we should not consider it for rewriting here.
            if module_aliases.values().any(|e| e == &m.module_name) {
                continue;
            }
            let local_name = prefix_name(function_name, &m.module_name);
            for (n, _) in &m.function_name_to_definition {
                println!("Function name: {}", n);
                if n == &local_name {
                    println!(
                        "Rewriting function reference {} in module {} to {}",
                        function_name, current_module_name, local_name
                    );
                    return local_name;
                }
            }
        }

        // Not found in imported modules.. Must be a record definition in the current module.
        println!(
            "Rewriting function reference {} in module {} to {}",
            function_name,
            current_module_name,
            prefix_name(function_name, current_module_name)
        );
        prefix_name(function_name, current_module_name)
    }

    fn rewrite_function_body(
        &mut self,
        function_body: &Rc<FunctionBody>,
        current_module_name: &Rc<String>,
        imported_modules: &Vec<Rc<TypedModule>>,
        module_aliases: &HashMap<Rc<String>, Rc<String>>,
    ) -> Rc<FunctionBody> {
        self.variables_stack.push(
            function_body
                .match_expressions
                .iter()
                .flat_map(|me| me.variables().into_iter())
                .chain(
                    function_body
                        .local_function_definitions
                        .iter()
                        .map(|d| Rc::clone(&d.name)),
                )
                .collect(),
        );
        let res = Rc::new(FunctionBody {
            name: Rc::clone(&function_body.name),
            location: Rc::clone(&function_body.location),
            match_expressions: function_body
                .match_expressions
                .iter()
                .map(|me| self.rewrite_match_expression(me, current_module_name, imported_modules))
                .collect(),
            rules: function_body
                .rules
                .iter()
                .map(|rule| {
                    self.rewrite_function_body_rule(
                        rule,
                        current_module_name,
                        imported_modules,
                        module_aliases,
                    )
                })
                .collect(),
            local_function_definitions: function_body
                .local_function_definitions
                .iter()
                .map(|fd| {
                    self.rewrite_function_definition(
                        fd,
                        false,
                        current_module_name,
                        imported_modules,
                        module_aliases,
                    )
                })
                .collect(),
            local_adt_definitions: function_body
                .local_adt_definitions
                .iter()
                .map(|adtd| {
                    self.rewrite_adt_definition(adtd, current_module_name, imported_modules)
                })
                .collect(),
            local_record_definitions: function_body
                .local_record_definitions
                .iter()
                .map(|rd| self.rewrite_record_definition(rd, current_module_name, imported_modules))
                .collect(),
        });
        self.variables_stack.pop();
        res
    }
    fn rewrite_function_body_rule(
        &mut self,
        function_body_rule: &Rc<FunctionRule>,
        current_module_name: &Rc<String>,
        imported_modules: &Vec<Rc<TypedModule>>,
        module_aliases: &HashMap<Rc<String>, Rc<String>>,
    ) -> Rc<FunctionRule> {
        Rc::new(match function_body_rule.borrow() {
            FunctionRule::ConditionalRule(l, c, e) => FunctionRule::ConditionalRule(
                Rc::clone(l),
                self.rewrite_expression(c, current_module_name, imported_modules, module_aliases),
                self.rewrite_expression(e, current_module_name, imported_modules, module_aliases),
            ),
            FunctionRule::ExpressionRule(l, e) => FunctionRule::ExpressionRule(
                Rc::clone(l),
                self.rewrite_expression(e, current_module_name, imported_modules, module_aliases),
            ),
            FunctionRule::LetRule(l, me, e) => {
                self.variables_stack
                    .last_mut()
                    .unwrap()
                    .extend(me.variables().into_iter());
                let res = FunctionRule::LetRule(
                    Rc::clone(l),
                    self.rewrite_match_expression(me, current_module_name, imported_modules),
                    self.rewrite_expression(
                        e,
                        current_module_name,
                        imported_modules,
                        module_aliases,
                    ),
                );
                res
            }
        })
    }

    fn rewrite_expression(
        &mut self,
        expression: &Rc<Expression>,
        current_module_name: &Rc<String>,
        imported_modules: &Vec<Rc<TypedModule>>,
        module_aliases: &HashMap<Rc<String>, Rc<String>>,
    ) -> Rc<Expression> {
        Rc::new(match expression.borrow() {
            Expression::BoolLiteral(l, b) => Expression::BoolLiteral(Rc::clone(l), *b),
            Expression::StringLiteral(l, s) => {
                Expression::StringLiteral(Rc::clone(l), Rc::clone(s))
            }
            Expression::CharacterLiteral(l, c) => Expression::CharacterLiteral(Rc::clone(l), *c),
            Expression::IntegerLiteral(l, i) => Expression::IntegerLiteral(Rc::clone(l), *i),
            Expression::FloatLiteral(l, f) => Expression::FloatLiteral(Rc::clone(l), *f),

            Expression::TupleLiteral(l, es) => Expression::TupleLiteral(
                Rc::clone(l),
                es.iter()
                    .map(|e| {
                        self.rewrite_expression(
                            e,
                            current_module_name,
                            imported_modules,
                            module_aliases,
                        )
                    })
                    .collect(),
            ),
            Expression::EmptyListLiteral(l) => Expression::EmptyListLiteral(Rc::clone(l)),
            Expression::ShorthandListLiteral(l, es) => Expression::ShorthandListLiteral(
                Rc::clone(l),
                es.iter()
                    .map(|e| {
                        self.rewrite_expression(
                            e,
                            current_module_name,
                            imported_modules,
                            module_aliases,
                        )
                    })
                    .collect(),
            ),
            Expression::LonghandListLiteral(l, he, te) => Expression::LonghandListLiteral(
                Rc::clone(l),
                self.rewrite_expression(he, current_module_name, imported_modules, module_aliases),
                self.rewrite_expression(te, current_module_name, imported_modules, module_aliases),
            ),
            Expression::ADTTypeConstructor(l, name, es) => Expression::ADTTypeConstructor(
                Rc::clone(l),
                Rc::clone(name),
                es.iter()
                    .map(|e| {
                        self.rewrite_expression(
                            e,
                            current_module_name,
                            imported_modules,
                            module_aliases,
                        )
                    })
                    .collect(),
            ),
            Expression::Record(l, n, fields) => Expression::Record(
                Rc::clone(l),
                Rc::clone(n),
                fields
                    .iter()
                    .map(|(n, e)| {
                        (
                            Rc::clone(n),
                            self.rewrite_expression(
                                e,
                                current_module_name,
                                imported_modules,
                                module_aliases,
                            ),
                        )
                    })
                    .collect(),
            ),
            Expression::Case(l, e, rules) => Expression::Case(
                Rc::clone(l),
                self.rewrite_expression(e, current_module_name, imported_modules, module_aliases),
                rules
                    .iter()
                    .map(|r| {
                        self.variables_stack.push(r.case_rule.variables());
                        let res = Rc::new(CaseRule {
                            loc_info: Rc::clone(&r.loc_info),
                            case_rule: self.rewrite_match_expression(
                                &r.case_rule,
                                current_module_name,
                                imported_modules,
                            ),
                            result_rule: self.rewrite_expression(
                                &r.result_rule,
                                current_module_name,
                                imported_modules,
                                module_aliases,
                            ),
                        });
                        self.variables_stack.pop();
                        res
                    })
                    .collect(),
            ),
            Expression::Call(l, function_name, es) => Expression::Call(
                Rc::clone(l),
                self.rewrite_function_name(
                    function_name,
                    current_module_name,
                    imported_modules,
                    module_aliases,
                ),
                es.iter()
                    .map(|e| {
                        self.rewrite_expression(
                            e,
                            current_module_name,
                            imported_modules,
                            module_aliases,
                        )
                    })
                    .collect(),
            ),
            Expression::Variable(l, v) => Expression::Variable(Rc::clone(l), Rc::clone(v)),
            Expression::Negation(l, e) => Expression::Negation(
                Rc::clone(l),
                self.rewrite_expression(e, current_module_name, imported_modules, module_aliases),
            ),
            Expression::Minus(l, e) => Expression::Minus(
                Rc::clone(l),
                self.rewrite_expression(e, current_module_name, imported_modules, module_aliases),
            ),
            Expression::Times(l, el, er) => Expression::Times(
                Rc::clone(l),
                self.rewrite_expression(el, current_module_name, imported_modules, module_aliases),
                self.rewrite_expression(er, current_module_name, imported_modules, module_aliases),
            ),
            Expression::Divide(l, el, er) => Expression::Divide(
                Rc::clone(l),
                self.rewrite_expression(el, current_module_name, imported_modules, module_aliases),
                self.rewrite_expression(er, current_module_name, imported_modules, module_aliases),
            ),
            Expression::Modulo(l, el, er) => Expression::Modulo(
                Rc::clone(l),
                self.rewrite_expression(el, current_module_name, imported_modules, module_aliases),
                self.rewrite_expression(er, current_module_name, imported_modules, module_aliases),
            ),
            Expression::Add(l, el, er) => Expression::Add(
                Rc::clone(l),
                self.rewrite_expression(el, current_module_name, imported_modules, module_aliases),
                self.rewrite_expression(er, current_module_name, imported_modules, module_aliases),
            ),
            Expression::Subtract(l, el, er) => Expression::Subtract(
                Rc::clone(l),
                self.rewrite_expression(el, current_module_name, imported_modules, module_aliases),
                self.rewrite_expression(er, current_module_name, imported_modules, module_aliases),
            ),
            Expression::ShiftLeft(l, el, er) => Expression::ShiftLeft(
                Rc::clone(l),
                self.rewrite_expression(el, current_module_name, imported_modules, module_aliases),
                self.rewrite_expression(er, current_module_name, imported_modules, module_aliases),
            ),
            Expression::ShiftRight(l, el, er) => Expression::ShiftRight(
                Rc::clone(l),
                self.rewrite_expression(el, current_module_name, imported_modules, module_aliases),
                self.rewrite_expression(er, current_module_name, imported_modules, module_aliases),
            ),
            Expression::Greater(l, el, er) => Expression::Greater(
                Rc::clone(l),
                self.rewrite_expression(el, current_module_name, imported_modules, module_aliases),
                self.rewrite_expression(er, current_module_name, imported_modules, module_aliases),
            ),
            Expression::Greq(l, el, er) => Expression::Greq(
                Rc::clone(l),
                self.rewrite_expression(el, current_module_name, imported_modules, module_aliases),
                self.rewrite_expression(er, current_module_name, imported_modules, module_aliases),
            ),
            Expression::Leq(l, el, er) => Expression::Leq(
                Rc::clone(l),
                self.rewrite_expression(el, current_module_name, imported_modules, module_aliases),
                self.rewrite_expression(er, current_module_name, imported_modules, module_aliases),
            ),
            Expression::Lesser(l, el, er) => Expression::Lesser(
                Rc::clone(l),
                self.rewrite_expression(el, current_module_name, imported_modules, module_aliases),
                self.rewrite_expression(er, current_module_name, imported_modules, module_aliases),
            ),
            Expression::Eq(l, el, er) => Expression::Eq(
                Rc::clone(l),
                self.rewrite_expression(el, current_module_name, imported_modules, module_aliases),
                self.rewrite_expression(er, current_module_name, imported_modules, module_aliases),
            ),
            Expression::Neq(l, el, er) => Expression::Neq(
                Rc::clone(l),
                self.rewrite_expression(el, current_module_name, imported_modules, module_aliases),
                self.rewrite_expression(er, current_module_name, imported_modules, module_aliases),
            ),
            Expression::And(l, el, er) => Expression::And(
                Rc::clone(l),
                self.rewrite_expression(el, current_module_name, imported_modules, module_aliases),
                self.rewrite_expression(er, current_module_name, imported_modules, module_aliases),
            ),
            Expression::Or(l, el, er) => Expression::Or(
                Rc::clone(l),
                self.rewrite_expression(el, current_module_name, imported_modules, module_aliases),
                self.rewrite_expression(er, current_module_name, imported_modules, module_aliases),
            ),
            Expression::RecordFieldAccess(l, re, fe) => Expression::RecordFieldAccess(
                Rc::clone(l),
                self.rewrite_expression(re, current_module_name, imported_modules, module_aliases),
                self.rewrite_expression(fe, current_module_name, imported_modules, module_aliases),
            ),
            Expression::Lambda(l, es, e) => Expression::Lambda(
                Rc::clone(l),
                es.iter()
                    .map(|e| {
                        self.rewrite_match_expression(e, current_module_name, imported_modules)
                    })
                    .collect(),
                self.rewrite_expression(e, current_module_name, imported_modules, module_aliases),
            ),
        })
    }

    fn rewrite_match_expression(
        &self,
        match_expression: &Rc<MatchExpression>,
        current_module_name: &Rc<String>,
        imported_modules: &Vec<Rc<TypedModule>>,
    ) -> Rc<MatchExpression> {
        Rc::new(match match_expression.borrow() {
            MatchExpression::IntLiteral(l, i) => MatchExpression::IntLiteral(Rc::clone(l), *i),
            MatchExpression::CharLiteral(l, c) => MatchExpression::CharLiteral(Rc::clone(l), *c),
            MatchExpression::StringLiteral(l, s) => {
                MatchExpression::StringLiteral(Rc::clone(l), Rc::clone(s))
            }
            MatchExpression::BoolLiteral(l, b) => MatchExpression::BoolLiteral(Rc::clone(l), *b),
            MatchExpression::Identifier(l, id) => {
                MatchExpression::Identifier(Rc::clone(l), Rc::clone(id))
            }
            MatchExpression::Tuple(l, mes) => MatchExpression::Tuple(
                Rc::clone(l),
                mes.iter()
                    .map(|me| {
                        self.rewrite_match_expression(me, current_module_name, imported_modules)
                    })
                    .collect(),
            ),
            MatchExpression::ShorthandList(l, mes) => MatchExpression::ShorthandList(
                Rc::clone(l),
                mes.iter()
                    .map(|me| {
                        self.rewrite_match_expression(me, current_module_name, imported_modules)
                    })
                    .collect(),
            ),
            MatchExpression::LonghandList(l, hme, tme) => MatchExpression::LonghandList(
                Rc::clone(l),
                self.rewrite_match_expression(hme, current_module_name, imported_modules),
                self.rewrite_match_expression(tme, current_module_name, imported_modules),
            ),
            MatchExpression::Wildcard(l) => MatchExpression::Wildcard(Rc::clone(l)),
            MatchExpression::ADT(l, constructor_name, mes) => MatchExpression::ADT(
                Rc::clone(l),
                Rc::clone(constructor_name),
                mes.iter()
                    .map(|me| {
                        self.rewrite_match_expression(me, current_module_name, imported_modules)
                    })
                    .collect(),
            ),
            MatchExpression::Record(l, record_name, fields) => {
                MatchExpression::Record(Rc::clone(l), Rc::clone(record_name), fields.clone())
            }
        })
    }
}

fn to_import_module_name(import: &Rc<Import>) -> Rc<String> {
    match import.borrow() {
        Import::ImportMembers(_, module_name, _) => Rc::clone(module_name),
        Import::ImportModule(_, module_name, _) => Rc::clone(module_name),
    }
}

fn prefix_name(name: &Rc<String>, module_name: &Rc<String>) -> Rc<String> {
    let mut s = String::new();
    s.push_str(module_name);
    s.push_str("::");
    s.push_str(name);
    Rc::new(s)
}

pub fn rewrite(
    main_module: TypedModule,
    modules_by_name: HashMap<Rc<String>, Rc<TypedModule>>,
) -> Rc<RuntimeModule> {
    println!("Building runtime module..");
    let mut state = RewriteState::new(modules_by_name);
    let rewritten_main_module = state.rewrite_module(Rc::new(main_module));
    let mut functions = HashMap::new();
    functions.extend(
        rewritten_main_module
            .function_name_to_definition
            .iter()
            .map(|(n, d)| (Rc::clone(n), Rc::clone(d))),
    );
    for (_, m) in &state.rewritten_modules {
        functions.extend(
            m.function_name_to_definition
                .iter()
                .map(|(n, d)| (Rc::clone(n), Rc::clone(d))),
        )
    }

    Rc::new(RuntimeModule {
        name: Rc::clone(&rewritten_main_module.module_name),
        functions,
    })
}

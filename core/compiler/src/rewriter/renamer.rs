use super::*;
use crate::ast::ADTConstructor;

struct RenamerState {
    original_modules: HashMap<Rc<String>, Rc<Module>>,
    rewritten_modules: HashMap<Rc<String>, Rc<Module>>,

    variables_stack: Vec<HashSet<Rc<String>>>,
    local_functions_stack: Vec<(Rc<String>, HashSet<Rc<String>>)>,
    local_records_stack: Vec<(Rc<String>, HashSet<Rc<String>>)>,
    local_adts_stack: Vec<(Rc<String>, HashMap<Rc<String>, HashSet<Rc<String>>>)>,
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

pub fn rename(
    main_module: Module,
    modules_by_name: HashMap<Rc<String>, Rc<Module>>,
) -> (
    HashMap<Rc<String>, Rc<FunctionDefinition>>,
    HashMap<Rc<String>, Rc<ADTDefinition>>,
    HashMap<Rc<String>, Rc<RecordDefinition>>,
) {
    let mut state = RenamerState::new(modules_by_name);
    let renamed_main_module = state.rename(Rc::new(main_module));
    let mut functions: HashMap<Rc<String>, Rc<FunctionDefinition>> = HashMap::new();
    let mut records: HashMap<Rc<String>, Rc<RecordDefinition>> = HashMap::new();
    let mut adts: HashMap<Rc<String>, Rc<ADTDefinition>> = HashMap::new();
    functions.extend(
        renamed_main_module
            .function_name_to_definition
            .iter()
            .map(|(n, d)| (Rc::clone(n), Rc::clone(d))),
    );
    records.extend(
        renamed_main_module
            .record_name_to_definition
            .iter()
            .map(|(n, d)| (Rc::clone(n), Rc::clone(d)))
            .collect::<HashMap<Rc<String>, Rc<RecordDefinition>>>(),
    );
    adts.extend(
        renamed_main_module
            .adt_name_to_definition
            .iter()
            .map(|(n, d)| (Rc::clone(n), Rc::clone(d)))
            .collect::<HashMap<Rc<String>, Rc<ADTDefinition>>>(),
    );
    for (_, m) in &state.rewritten_modules {
        functions.extend(
            m.function_name_to_definition
                .iter()
                .map(|(n, d)| (Rc::clone(n), Rc::clone(d))),
        );
        records.extend(
            m.record_name_to_definition
                .iter()
                .map(|(n, d)| (Rc::clone(n), Rc::clone(d)))
                .collect::<HashMap<Rc<String>, Rc<RecordDefinition>>>(),
        );
        adts.extend(
            m.adt_name_to_definition
                .iter()
                .map(|(n, d)| (Rc::clone(n), Rc::clone(d)))
                .collect::<HashMap<Rc<String>, Rc<ADTDefinition>>>(),
        );
    }

    (functions, adts, records)
}

impl RenamerState {
    fn new(original_modules: HashMap<Rc<String>, Rc<Module>>) -> Self {
        RenamerState {
            original_modules,
            rewritten_modules: HashMap::new(),
            variables_stack: Vec::new(),
            local_functions_stack: Vec::new(),
            local_records_stack: Vec::new(),
            local_adts_stack: Vec::new(),
        }
    }

    fn rename(&mut self, module: Rc<Module>) -> Rc<Module> {
        if self.rewritten_modules.contains_key(&module.name) {
            return Rc::clone(self.rewritten_modules.get(&module.name).unwrap());
        }

        let imported_modules: Vec<Rc<Module>> = module
            .imports
            .iter()
            .map(|import| {
                let import_module_name = to_import_module_name(import);
                self.rename(Rc::clone(
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

        let rewritten_module = Rc::new(Module {
            name: Rc::clone(&module.name),
            file_name: Rc::clone(&module.file_name),
            imports: module.imports.iter().map(Rc::clone).collect(),
            function_name_to_definition: module
                .function_name_to_definition
                .iter()
                .map(|(n, d)| {
                    (
                        prefix_name(n, &module.name),
                        self.rewrite_function_definition(
                            d,
                            &module.name,
                            &imported_modules,
                            &module_aliases,
                        ),
                    )
                })
                .collect(),
            adt_name_to_definition: module
                .adt_name_to_definition
                .iter()
                .map(|(n, d)| {
                    (
                        prefix_name(n, &module.name),
                        self.rewrite_adt_definition(
                            d,
                            &module.name,
                            &imported_modules,
                            &module_aliases,
                        ),
                    )
                })
                .collect(),
            record_name_to_definition: module
                .record_name_to_definition
                .iter()
                .map(|(n, d)| {
                    (
                        prefix_name(n, &module.name),
                        self.rewrite_record_definition(
                            d,
                            &module.name,
                            &imported_modules,
                            &module_aliases,
                        ),
                    )
                })
                .collect(),
        });
        self.rewritten_modules
            .insert(Rc::clone(&module.name), Rc::clone(&rewritten_module));
        return rewritten_module;
    }

    fn rewrite_adt_definition(
        &mut self,
        adt_definition: &Rc<ADTDefinition>,
        current_scope_name: &Rc<String>,
        imported_modules: &Vec<Rc<Module>>,
        module_aliases: &HashMap<Rc<String>, Rc<String>>,
    ) -> Rc<ADTDefinition> {
        Rc::new(ADTDefinition {
            name: prefix_name(&adt_definition.name, current_scope_name),
            location: Rc::clone(&adt_definition.location),
            type_variables: adt_definition.type_variables.iter().cloned().collect(),
            constructors: adt_definition
                .constructors
                .iter()
                .map(|c| {
                    Rc::new(ADTConstructor {
                        name: prefix_name(&c.name, current_scope_name),
                        elements: c
                            .elements
                            .iter()
                            .map(|e| {
                                self.rewrite_type(
                                    e,
                                    current_scope_name,
                                    imported_modules,
                                    module_aliases,
                                )
                            })
                            .collect(),
                    })
                })
                .collect(),
        })
    }

    fn rewrite_record_definition(
        &mut self,
        record_definition: &Rc<RecordDefinition>,
        current_scope_name: &Rc<String>,
        imported_modules: &Vec<Rc<Module>>,
        module_aliases: &HashMap<Rc<String>, Rc<String>>,
    ) -> Rc<RecordDefinition> {
        Rc::new(RecordDefinition {
            name: prefix_name(&record_definition.name, current_scope_name),
            location: Rc::clone(&record_definition.location),
            type_variables: record_definition.type_variables.iter().cloned().collect(),
            fields: record_definition
                .fields
                .iter()
                .map(|(name, field_type)| {
                    (
                        Rc::clone(name),
                        self.rewrite_type(
                            field_type,
                            current_scope_name,
                            imported_modules,
                            module_aliases,
                        ),
                    )
                })
                .collect(),
        })
    }

    fn rewrite_type(
        &mut self,
        loz_type: &Rc<Type>,
        current_scope_name: &Rc<String>,
        imported_modules: &Vec<Rc<Module>>,
        module_aliases: &HashMap<Rc<String>, Rc<String>>,
    ) -> Rc<Type> {
        match loz_type.borrow() {
            Type::Bool => Rc::clone(loz_type),
            Type::Char => Rc::clone(loz_type),
            Type::String => Rc::clone(loz_type),
            Type::Int => Rc::clone(loz_type),
            Type::Float => Rc::clone(loz_type),
            Type::UserType(name, arguments) => Rc::new(Type::UserType(
                self.rewrite_type_name(name, current_scope_name, imported_modules, module_aliases),
                arguments
                    .iter()
                    .map(|a| {
                        self.rewrite_type(a, current_scope_name, imported_modules, module_aliases)
                    })
                    .collect(),
            )),
            Type::Tuple(els) => Rc::new(Type::Tuple(
                els.iter()
                    .map(|t| {
                        self.rewrite_type(t, current_scope_name, imported_modules, module_aliases)
                    })
                    .collect(),
            )),
            Type::List(t) => Rc::new(Type::List(self.rewrite_type(
                t,
                current_scope_name,
                imported_modules,
                module_aliases,
            ))),
            Type::Variable(_) => Rc::clone(loz_type),
            Type::Function(from, to) => Rc::new(Type::Function(
                from.iter()
                    .map(|t| {
                        self.rewrite_type(t, current_scope_name, imported_modules, module_aliases)
                    })
                    .collect(),
                self.rewrite_type(to, current_scope_name, imported_modules, module_aliases),
            )),
        }
    }

    fn rewrite_function_definition(
        &mut self,
        function_definition: &Rc<FunctionDefinition>,
        current_scope_name: &Rc<String>,
        imported_modules: &Vec<Rc<Module>>,
        module_aliases: &HashMap<Rc<String>, Rc<String>>,
    ) -> Rc<FunctionDefinition> {
        Rc::new(FunctionDefinition {
            location: Rc::clone(&function_definition.location),
            name: prefix_name(&function_definition.name, current_scope_name),
            function_type: Some(Rc::new(TypeScheme {
                bound_variables: function_definition
                    .function_type
                    .as_ref()
                    .unwrap()
                    .bound_variables
                    .clone(),
                enclosed_type: self.rewrite_type(
                    &function_definition
                        .function_type
                        .as_ref()
                        .unwrap()
                        .enclosed_type,
                    current_scope_name,
                    imported_modules,
                    module_aliases,
                ),
            })),
            function_bodies: function_definition
                .function_bodies
                .iter()
                .map(|b| {
                    self.rewrite_function_body(
                        b,
                        current_scope_name,
                        imported_modules,
                        module_aliases,
                    )
                })
                .collect(),
        })
    }

    fn rewrite_type_name(
        &self,
        type_name: &Rc<String>,
        current_scope_name: &Rc<String>,
        imported_modules: &Vec<Rc<Module>>,
        module_aliases: &HashMap<Rc<String>, Rc<String>>,
    ) -> Rc<String> {
        for (defined_in, records) in self.local_records_stack.iter().rev() {
            if records.contains(type_name) {
                return prefix_name(type_name, defined_in);
            }
        }
        for (defined_in, adts) in self.local_adts_stack.iter().rev() {
            if adts.contains_key(type_name) {
                return prefix_name(type_name, defined_in);
            }
        }

        for m in imported_modules {
            // If the module is alias as import we should not consider it for rewriting here.
            if module_aliases.values().any(|e| e == &m.name) {
                continue;
            }
            // A type name cannot be both a record and an ADT, so we can safely
            // search both collections.
            let local_name = prefix_name(type_name, &m.name);
            for (n, _) in &m.record_name_to_definition {
                if n == &local_name {
                    //println!(
                    //    "Rewriting record reference {} in module {} to {}",
                    //    type_name, current_module_name, local_name
                    //);
                    return local_name;
                }
            }

            for (n, _) in &m.adt_name_to_definition {
                if n == &local_name {
                    //println!(
                    //    "Rewriting adt reference {} in module {} to {}",
                    //    type_name, current_module_name, local_name
                    //);
                    return local_name;
                }
            }
        }

        // Not found in imported modules.. Must be a definition in the current module.
        prefix_name(type_name, current_scope_name)
    }

    fn rewrite_type_constructor_name(
        &self,
        constructor_name: &Rc<String>,
        current_scope_name: &Rc<String>,
        imported_modules: &Vec<Rc<Module>>,
        module_aliases: &HashMap<Rc<String>, Rc<String>>,
    ) -> Rc<String> {
        for (defined_in, adts) in self.local_adts_stack.iter() {
            for (_, c) in adts.iter() {
                if c.contains(constructor_name) {
                    return prefix_name(constructor_name, defined_in);
                }
            }
        }

        // Is already a qualified name so should be an alias for an exiting module name.
        if constructor_name.contains("::") {
            let mut splitter = constructor_name.split("::");
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
            if module_aliases.values().any(|e| e == &m.name) {
                continue;
            }
            let local_name = prefix_name(constructor_name, &m.name);
            for (_, d) in &m.adt_name_to_definition {
                for constructor in &d.constructors {
                    if &constructor.name == &local_name {
                        //println!(
                        //    "Rewriting adt constructor reference {} in module {} to {}",
                        //    constructor_name, current_module_name, local_name
                        //);
                        return local_name;
                    }
                }
            }
        }

        // Not found in imported modules.. Must be a definition in the current module.
        //println!(
        //    "Rewriting function reference {} in module {} to {}",
        //    function_name,
        //    current_module_name,
        //    prefix_name(function_name, current_module_name)
        //);
        prefix_name(constructor_name, current_scope_name)
    }

    fn rewrite_function_name(
        &self,
        function_name: &Rc<String>,
        current_module_name: &Rc<String>,
        imported_modules: &Vec<Rc<Module>>,
        module_aliases: &HashMap<Rc<String>, Rc<String>>,
    ) -> Rc<String> {
        for vars in self.variables_stack.iter().rev() {
            if vars.contains(function_name) {
                return Rc::clone(function_name);
            }
        }

        for (defined_in, functions) in self.local_functions_stack.iter().rev() {
            if functions.contains(function_name) {
                return prefix_name(function_name, defined_in);
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
            if module_aliases.values().any(|e| e == &m.name) {
                continue;
            }
            let local_name = prefix_name(function_name, &m.name);
            for (n, _) in &m.function_name_to_definition {
                if n == &local_name {
                    //println!(
                    //    "Rewriting function reference {} in module {} to {}",
                    //    function_name, current_module_name, local_name
                    //);
                    return local_name;
                }
            }
        }

        // Not found in imported modules.. Must be a definition in the current module.
        //println!(
        //    "Rewriting function reference {} in module {} to {}",
        //    function_name,
        //    current_module_name,
        //    prefix_name(function_name, current_module_name)
        //);
        prefix_name(function_name, current_module_name)
    }

    fn rewrite_function_body(
        &mut self,
        function_body: &Rc<FunctionBody>,
        current_scope_name: &Rc<String>,
        imported_modules: &Vec<Rc<Module>>,
        module_aliases: &HashMap<Rc<String>, Rc<String>>,
    ) -> Rc<FunctionBody> {
        let function_scope_name = prefix_name(&function_body.name, current_scope_name);

        self.variables_stack.push(
            function_body
                .match_expressions
                .iter()
                .flat_map(|me| me.variables().into_iter())
                .collect(),
        );
        self.local_functions_stack.push((
            Rc::clone(&function_scope_name),
            function_body
                .local_function_definitions
                .iter()
                .map(|(n, _)| Rc::clone(n))
                .collect(),
        ));
        self.local_records_stack.push((
            Rc::clone(&function_scope_name),
            function_body
                .local_record_definitions
                .iter()
                .map(|(n, _)| Rc::clone(n))
                .collect(),
        ));

        let res = Rc::new(FunctionBody {
            name: Rc::clone(&current_scope_name),
            location: Rc::clone(&function_body.location),
            type_information: function_body
                .type_information
                .iter()
                .map(|(v, t)| {
                    (
                        Rc::clone(v),
                        Rc::new(TypeScheme {
                            bound_variables: t.bound_variables.clone(),
                            enclosed_type: self.rewrite_type(
                                &t.enclosed_type,
                                current_scope_name,
                                imported_modules,
                                module_aliases,
                            ),
                        }),
                    )
                })
                .collect(),
            match_expressions: function_body
                .match_expressions
                .iter()
                .map(|me| {
                    self.rewrite_match_expression(
                        me,
                        current_scope_name,
                        imported_modules,
                        module_aliases,
                    )
                })
                .collect(),
            rules: function_body
                .rules
                .iter()
                .map(|rule| {
                    self.rewrite_function_rule(
                        rule,
                        &current_scope_name,
                        imported_modules,
                        module_aliases,
                    )
                })
                .collect(),
            local_function_definitions: function_body
                .local_function_definitions
                .iter()
                .map(|(_, fd)| {
                    let function_definition = self.rewrite_function_definition(
                        fd,
                        &function_scope_name,
                        imported_modules,
                        module_aliases,
                    );
                    (Rc::clone(&function_definition.name), function_definition)
                })
                .collect(),
            local_adt_definitions: function_body
                .local_adt_definitions
                .iter()
                .map(|(_, d)| {
                    let adt_definition = self.rewrite_adt_definition(
                        d,
                        &function_scope_name,
                        imported_modules,
                        module_aliases,
                    );
                    (Rc::clone(&adt_definition.name), adt_definition)
                })
                .collect(),
            local_record_definitions: function_body
                .local_record_definitions
                .iter()
                .map(|(_, d)| {
                    let record_definition = self.rewrite_record_definition(
                        d,
                        &function_scope_name,
                        imported_modules,
                        module_aliases,
                    );
                    (Rc::clone(&record_definition.name), record_definition)
                })
                .collect(),
        });
        self.variables_stack.pop();
        self.local_functions_stack.pop();
        self.local_adts_stack.pop();
        self.local_records_stack.pop();
        res
    }

    fn rewrite_function_rule(
        &mut self,
        function_rule: &Rc<FunctionRule>,
        current_module_name: &Rc<String>,
        imported_modules: &Vec<Rc<Module>>,
        module_aliases: &HashMap<Rc<String>, Rc<String>>,
    ) -> Rc<FunctionRule> {
        Rc::new(match function_rule.borrow() {
            FunctionRule::ConditionalRule(l, c, e) => FunctionRule::ConditionalRule(
                Rc::clone(l),
                self.rewrite_expression(c, current_module_name, imported_modules, module_aliases),
                self.rewrite_expression(e, current_module_name, imported_modules, module_aliases),
            ),
            FunctionRule::ExpressionRule(l, e) => FunctionRule::ExpressionRule(
                Rc::clone(l),
                self.rewrite_expression(e, current_module_name, imported_modules, module_aliases),
            ),
            FunctionRule::LetRule(l, type_information, me, e) => {
                self.variables_stack
                    .last_mut()
                    .unwrap()
                    .extend(me.variables().into_iter());
                let res = FunctionRule::LetRule(
                    Rc::clone(l),
                    type_information.clone(),
                    self.rewrite_match_expression(
                        me,
                        current_module_name,
                        imported_modules,
                        module_aliases,
                    ),
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
        current_scope_name: &Rc<String>,
        imported_modules: &Vec<Rc<Module>>,
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
                            current_scope_name,
                            imported_modules,
                            module_aliases,
                        )
                    })
                    .collect(),
            ),
            Expression::EmptyListLiteral(l, list_type) => {
                Expression::EmptyListLiteral(Rc::clone(l), list_type.clone())
            }
            Expression::ShorthandListLiteral(l, list_type, es) => Expression::ShorthandListLiteral(
                Rc::clone(l),
                list_type.clone(),
                es.iter()
                    .map(|e| {
                        self.rewrite_expression(
                            e,
                            current_scope_name,
                            imported_modules,
                            module_aliases,
                        )
                    })
                    .collect(),
            ),
            Expression::LonghandListLiteral(l, list_type, he, te) => {
                Expression::LonghandListLiteral(
                    Rc::clone(l),
                    list_type.clone(),
                    self.rewrite_expression(
                        he,
                        current_scope_name,
                        imported_modules,
                        module_aliases,
                    ),
                    self.rewrite_expression(
                        te,
                        current_scope_name,
                        imported_modules,
                        module_aliases,
                    ),
                )
            }
            Expression::ADTTypeConstructor(l, user_type, name, es) => {
                Expression::ADTTypeConstructor(
                    Rc::clone(l),
                    user_type.as_ref().map(|t| {
                        self.rewrite_type(t, current_scope_name, imported_modules, module_aliases)
                    }),
                    self.rewrite_type_constructor_name(
                        name,
                        current_scope_name,
                        imported_modules,
                        module_aliases,
                    ),
                    es.iter()
                        .map(|e| {
                            self.rewrite_expression(
                                e,
                                current_scope_name,
                                imported_modules,
                                module_aliases,
                            )
                        })
                        .collect(),
                )
            }
            Expression::Record(l, user_type, n, fields) => Expression::Record(
                Rc::clone(l),
                user_type.as_ref().map(|t| {
                    self.rewrite_type(t, current_scope_name, imported_modules, module_aliases)
                }),
                self.rewrite_type_name(n, current_scope_name, imported_modules, module_aliases),
                fields
                    .iter()
                    .map(|(n, e)| {
                        (
                            Rc::clone(n),
                            self.rewrite_expression(
                                e,
                                current_scope_name,
                                imported_modules,
                                module_aliases,
                            ),
                        )
                    })
                    .collect(),
            ),
            Expression::Case(l, e, rules, result_type) => Expression::Case(
                Rc::clone(l),
                self.rewrite_expression(e, current_scope_name, imported_modules, module_aliases),
                rules
                    .iter()
                    .map(|r| {
                        self.variables_stack.push(r.case_rule.variables());
                        let res = Rc::new(CaseRule {
                            loc_info: Rc::clone(&r.loc_info),
                            type_information: r
                                .type_information
                                .iter()
                                .map(|(v, t)| {
                                    (
                                        Rc::clone(v),
                                        Rc::new(TypeScheme {
                                            bound_variables: t.bound_variables.clone(),
                                            enclosed_type: self.rewrite_type(
                                                &t.enclosed_type,
                                                current_scope_name,
                                                imported_modules,
                                                module_aliases,
                                            ),
                                        }),
                                    )
                                })
                                .collect(),
                            case_rule: self.rewrite_match_expression(
                                &r.case_rule,
                                current_scope_name,
                                imported_modules,
                                module_aliases,
                            ),
                            result_rule: self.rewrite_expression(
                                &r.result_rule,
                                current_scope_name,
                                imported_modules,
                                module_aliases,
                            ),
                        });
                        self.variables_stack.pop();
                        res
                    })
                    .collect(),
                result_type.as_ref().map(|rt| {
                    self.rewrite_type(rt, current_scope_name, imported_modules, module_aliases)
                }),
            ),
            Expression::Call(l, function_type, function_name, es) => Expression::Call(
                Rc::clone(l),
                function_type.as_ref().map(|ft| {
                    self.rewrite_type(ft, current_scope_name, imported_modules, module_aliases)
                }),
                self.rewrite_function_name(
                    function_name,
                    current_scope_name,
                    imported_modules,
                    module_aliases,
                ),
                es.iter()
                    .map(|e| {
                        self.rewrite_expression(
                            e,
                            current_scope_name,
                            imported_modules,
                            module_aliases,
                        )
                    })
                    .collect(),
            ),
            Expression::Variable(l, v) => Expression::Variable(Rc::clone(l), Rc::clone(v)),
            Expression::Negation(l, e) => Expression::Negation(
                Rc::clone(l),
                self.rewrite_expression(e, current_scope_name, imported_modules, module_aliases),
            ),
            Expression::Minus(l, e) => Expression::Minus(
                Rc::clone(l),
                self.rewrite_expression(e, current_scope_name, imported_modules, module_aliases),
            ),
            Expression::Times(l, el, er) => Expression::Times(
                Rc::clone(l),
                self.rewrite_expression(el, current_scope_name, imported_modules, module_aliases),
                self.rewrite_expression(er, current_scope_name, imported_modules, module_aliases),
            ),
            Expression::Divide(l, el, er) => Expression::Divide(
                Rc::clone(l),
                self.rewrite_expression(el, current_scope_name, imported_modules, module_aliases),
                self.rewrite_expression(er, current_scope_name, imported_modules, module_aliases),
            ),
            Expression::Modulo(l, el, er) => Expression::Modulo(
                Rc::clone(l),
                self.rewrite_expression(el, current_scope_name, imported_modules, module_aliases),
                self.rewrite_expression(er, current_scope_name, imported_modules, module_aliases),
            ),
            Expression::Add(l, el, er) => Expression::Add(
                Rc::clone(l),
                self.rewrite_expression(el, current_scope_name, imported_modules, module_aliases),
                self.rewrite_expression(er, current_scope_name, imported_modules, module_aliases),
            ),
            Expression::Subtract(l, el, er) => Expression::Subtract(
                Rc::clone(l),
                self.rewrite_expression(el, current_scope_name, imported_modules, module_aliases),
                self.rewrite_expression(er, current_scope_name, imported_modules, module_aliases),
            ),
            Expression::ShiftLeft(l, el, er) => Expression::ShiftLeft(
                Rc::clone(l),
                self.rewrite_expression(el, current_scope_name, imported_modules, module_aliases),
                self.rewrite_expression(er, current_scope_name, imported_modules, module_aliases),
            ),
            Expression::ShiftRight(l, el, er) => Expression::ShiftRight(
                Rc::clone(l),
                self.rewrite_expression(el, current_scope_name, imported_modules, module_aliases),
                self.rewrite_expression(er, current_scope_name, imported_modules, module_aliases),
            ),
            Expression::Greater(l, el, er) => Expression::Greater(
                Rc::clone(l),
                self.rewrite_expression(el, current_scope_name, imported_modules, module_aliases),
                self.rewrite_expression(er, current_scope_name, imported_modules, module_aliases),
            ),
            Expression::Greq(l, el, er) => Expression::Greq(
                Rc::clone(l),
                self.rewrite_expression(el, current_scope_name, imported_modules, module_aliases),
                self.rewrite_expression(er, current_scope_name, imported_modules, module_aliases),
            ),
            Expression::Leq(l, el, er) => Expression::Leq(
                Rc::clone(l),
                self.rewrite_expression(el, current_scope_name, imported_modules, module_aliases),
                self.rewrite_expression(er, current_scope_name, imported_modules, module_aliases),
            ),
            Expression::Lesser(l, el, er) => Expression::Lesser(
                Rc::clone(l),
                self.rewrite_expression(el, current_scope_name, imported_modules, module_aliases),
                self.rewrite_expression(er, current_scope_name, imported_modules, module_aliases),
            ),
            Expression::Eq(l, el, er) => Expression::Eq(
                Rc::clone(l),
                self.rewrite_expression(el, current_scope_name, imported_modules, module_aliases),
                self.rewrite_expression(er, current_scope_name, imported_modules, module_aliases),
            ),
            Expression::Neq(l, el, er) => Expression::Neq(
                Rc::clone(l),
                self.rewrite_expression(el, current_scope_name, imported_modules, module_aliases),
                self.rewrite_expression(er, current_scope_name, imported_modules, module_aliases),
            ),
            Expression::And(l, el, er) => Expression::And(
                Rc::clone(l),
                self.rewrite_expression(el, current_scope_name, imported_modules, module_aliases),
                self.rewrite_expression(er, current_scope_name, imported_modules, module_aliases),
            ),
            Expression::Or(l, el, er) => Expression::Or(
                Rc::clone(l),
                self.rewrite_expression(el, current_scope_name, imported_modules, module_aliases),
                self.rewrite_expression(er, current_scope_name, imported_modules, module_aliases),
            ),
            Expression::RecordFieldAccess(l, record_type, record_name, re, fe) => {
                Expression::RecordFieldAccess(
                    Rc::clone(l),
                    Some(self.rewrite_type(
                        record_type.as_ref().unwrap(),
                        current_scope_name,
                        imported_modules,
                        module_aliases,
                    )),
                    self.rewrite_type_name(
                        record_name,
                        current_scope_name,
                        imported_modules,
                        module_aliases,
                    ),
                    self.rewrite_expression(
                        re,
                        current_scope_name,
                        imported_modules,
                        module_aliases,
                    ),
                    self.rewrite_expression(
                        fe,
                        current_scope_name,
                        imported_modules,
                        module_aliases,
                    ),
                )
            }
            Expression::Lambda(l, function_type, type_information, es, e) => Expression::Lambda(
                Rc::clone(l),
                function_type.clone(),
                type_information.clone(),
                es.iter()
                    .map(|e| {
                        self.rewrite_match_expression(
                            e,
                            current_scope_name,
                            imported_modules,
                            module_aliases,
                        )
                    })
                    .collect(),
                self.rewrite_expression(e, current_scope_name, imported_modules, module_aliases),
            ),
        })
    }

    fn rewrite_match_expression(
        &self,
        match_expression: &Rc<MatchExpression>,
        current_scope_name: &Rc<String>,
        imported_modules: &Vec<Rc<Module>>,
        module_aliases: &HashMap<Rc<String>, Rc<String>>,
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
                        self.rewrite_match_expression(
                            me,
                            current_scope_name,
                            imported_modules,
                            module_aliases,
                        )
                    })
                    .collect(),
            ),
            MatchExpression::ShorthandList(l, mes) => MatchExpression::ShorthandList(
                Rc::clone(l),
                mes.iter()
                    .map(|me| {
                        self.rewrite_match_expression(
                            me,
                            current_scope_name,
                            imported_modules,
                            module_aliases,
                        )
                    })
                    .collect(),
            ),
            MatchExpression::LonghandList(l, hme, tme) => MatchExpression::LonghandList(
                Rc::clone(l),
                self.rewrite_match_expression(
                    hme,
                    current_scope_name,
                    imported_modules,
                    module_aliases,
                ),
                self.rewrite_match_expression(
                    tme,
                    current_scope_name,
                    imported_modules,
                    module_aliases,
                ),
            ),
            MatchExpression::Wildcard(l) => MatchExpression::Wildcard(Rc::clone(l)),
            MatchExpression::ADT(l, constructor_name, mes) => MatchExpression::ADT(
                Rc::clone(l),
                self.rewrite_type_constructor_name(
                    constructor_name,
                    current_scope_name,
                    imported_modules,
                    module_aliases,
                ),
                mes.iter()
                    .map(|me| {
                        self.rewrite_match_expression(
                            me,
                            current_scope_name,
                            imported_modules,
                            module_aliases,
                        )
                    })
                    .collect(),
            ),
            MatchExpression::Record(l, record_name, fields) => MatchExpression::Record(
                Rc::clone(l),
                self.rewrite_type_name(
                    record_name,
                    current_scope_name,
                    imported_modules,
                    module_aliases,
                ),
                fields.clone(),
            ),
        })
    }
}

fn to_import_module_name(import: &Rc<Import>) -> Rc<String> {
    match import.borrow() {
        Import::ImportMembers(_, module_name, _) => Rc::clone(module_name),
        Import::ImportModule(_, module_name, _) => Rc::clone(module_name),
    }
}

fn prefix_name(name: &Rc<String>, scope_name: &Rc<String>) -> Rc<String> {
    let mut s = String::new();
    s.push_str(scope_name);
    s.push_str("::");
    s.push_str(name);
    Rc::new(s)
}

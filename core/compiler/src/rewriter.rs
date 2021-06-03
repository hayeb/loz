use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::ast::{
    ADTDefinition, CaseRule, Expression, FunctionBody, FunctionDefinition, FunctionRule,
    MatchExpression, Module, RecordDefinition,
};
use crate::generator::ir::{
    IRADTConstructor, IRADTDefinition, IRCaseRule, IRExpression, IRFunctionBody,
    IRFunctionDefinition, IRFunctionRule, IRMatchExpression, IRRecordDefinition, IRType,
};
use crate::rewriter::extractor::extract_closure_variables;
use crate::rewriter::flattener::flatten;
use crate::rewriter::instantiator::{instantiate, Instantiated};
use crate::rewriter::renamer::rename;
use crate::{Import, Type, TypeScheme};

mod extractor;
mod flattener;
mod instantiator;
mod renamer;

pub struct IRModule {
    pub name: Rc<String>,
    pub main_function_name: Rc<String>,
    pub main_function_type: Rc<Type>,

    pub functions: HashMap<Rc<String>, Rc<IRFunctionDefinition>>,
    pub adts: HashMap<Rc<String>, Monomorphized<IRADTDefinition>>,
    pub records: HashMap<Rc<String>, Monomorphized<IRRecordDefinition>>,
}

#[derive(Clone, Debug)]
pub struct Monomorphized<T> {
    pub base: Rc<T>,
    pub instances: HashMap<Rc<String>, Rc<T>>,
}

pub fn rewrite(
    main_module: Module,
    modules_by_name: HashMap<Rc<String>, Rc<Module>>,
) -> Rc<IRModule> {
    println!("Building runtime module..");

    let main_module_name = Rc::clone(&main_module.name);
    let main_function_name = Rc::new(format!("{}::main", &main_module_name));

    // 1. Rename all definitions to include the module name. Rename all variables with the module
    //    the variable refers to.
    let (functions, adts, records) = rename(main_module, modules_by_name);

    // 2. Flatten function definitions. Extracts local definitions and lifts them to the global
    //    scope. We have renamed the local definitions in the previous step so there are no name
    //    clashes.
    //        f g a = apply g a
    //        where
    //            apply g a = g a
    //        .
    //    becomes
    //        f_apply g a = g a
    //        f g a = f_apply g a
    let (functions, local_adts, local_records) = flatten(functions);

    let functions = add_closure_variables_to_type(functions);

    // 3. Remove variable types by monomorphization.
    //         f :: [a] Int -> Maybe a
    //         main = (f [1, 2, 3] 0, f ['a', 'b', 'c'] 1)
    //    becomes
    //         f_0 :: [Int] Int -> Maybe Int
    //         f_1 :: [Char] Int -> Maybe Char
    //         main = (f_0 [1, 2, 3] 0, f_1 ['a', 'b', 'c'] 1)
    let (combined_adts, combined_records, instantiated) = instantiate_definitions(
        &main_function_name,
        adts,
        records,
        local_adts,
        local_records,
        functions,
    );

    // 4. Build a runtime module with the newly generated definitions.
    let runtime_module = build_runtime_module(
        &main_module_name,
        &main_function_name,
        combined_adts,
        combined_records,
        &instantiated,
    );

    return Rc::new(runtime_module);
}

fn build_runtime_module(
    main_module_name: &Rc<String>,
    main_function_name: &Rc<String>,
    combined_adts: HashMap<Rc<String>, Rc<ADTDefinition>>,
    combined_records: HashMap<Rc<String>, Rc<RecordDefinition>>,
    instantiated: &Instantiated,
) -> IRModule {
    let runtime_module = IRModule {
        name: Rc::clone(&main_module_name),
        main_function_name: Rc::new("main".to_string()),
        main_function_type: Rc::clone(
            &instantiated
                .functions
                .get(main_function_name)
                .unwrap()
                .function_type
                .as_ref()
                .unwrap()
                .enclosed_type,
        ),
        functions: instantiated
            .functions
            .iter()
            .map(|(n, f)| (n.clone(), to_ir_functions(f)))
            .collect(),
        adts: combined_adts
            .iter()
            .map(|(n, d)| (n, to_ir_adt(d)))
            .map(|(name, definition)| {
                (
                    Rc::clone(name),
                    Monomorphized {
                        base: definition,
                        instances: instantiated
                            .adts
                            .iter()
                            .filter(|(n, _)| n.starts_with(&name.to_string()))
                            .map(|(_, d)| (Rc::clone(&d.name), to_ir_adt(d)))
                            .collect(),
                    },
                )
            })
            .filter(|(_, m)| m.instances.len() > 0)
            .collect(),
        records: combined_records
            .iter()
            .map(|(n, d)| (n, to_ir_record(d)))
            .map(|(name, definition)| {
                (
                    Rc::clone(name),
                    Monomorphized {
                        base: definition,
                        instances: instantiated
                            .records
                            .iter()
                            .filter(|(n, _)| n.starts_with(&name.to_string()))
                            .map(|(_, d)| (Rc::clone(&d.name), to_ir_record(d)))
                            .collect(),
                    },
                )
            })
            .filter(|(_, m)| m.instances.len() > 0)
            .collect(),
    };
    runtime_module
}

fn instantiate_definitions(
    main_function_name: &Rc<String>,
    adts: HashMap<Rc<String>, Rc<ADTDefinition>>,
    records: HashMap<Rc<String>, Rc<RecordDefinition>>,
    local_adts: HashMap<Rc<String>, Rc<ADTDefinition>>,
    local_records: HashMap<Rc<String>, Rc<RecordDefinition>>,
    functions: HashMap<Rc<String>, Rc<FunctionDefinition>>,
) -> (
    HashMap<Rc<String>, Rc<ADTDefinition>>,
    HashMap<Rc<String>, Rc<RecordDefinition>>,
    Instantiated,
) {
    let mut combined_adts = HashMap::new();
    combined_adts.extend(adts);
    combined_adts.extend(local_adts);

    let mut combined_records = HashMap::new();
    combined_records.extend(records);
    combined_records.extend(local_records);

    let instantiated = instantiate(
        &main_function_name,
        functions.clone(),
        combined_adts.clone(),
        combined_records.clone(),
    );
    (combined_adts, combined_records, instantiated)
}

fn to_ir_functions(function: &Rc<FunctionDefinition>) -> Rc<IRFunctionDefinition> {
    Rc::new(IRFunctionDefinition {
        location: function.location.clone(),
        name: function.name.clone(),
        function_type: to_ir_type(&function.function_type.as_ref().unwrap().enclosed_type),
        function_bodies: function
            .function_bodies
            .iter()
            .map(|b| to_ir_function_body(b))
            .collect(),
    })
}

fn to_ir_function_body(body: &Rc<FunctionBody>) -> Rc<IRFunctionBody> {
    Rc::new(IRFunctionBody {
        name: body.name.clone(),
        location: body.location.clone(),
        match_expressions: body
            .match_expressions
            .iter()
            .map(|me| to_ir_match_expression(me))
            .collect(),
        rules: body
            .rules
            .iter()
            .map(|rule| to_ir_function_rule(rule))
            .collect(),
    })
}

fn to_ir_function_rule(rule: &Rc<FunctionRule>) -> Rc<IRFunctionRule> {
    match rule.borrow() {
        FunctionRule::ConditionalRule(loc, c, e) => Rc::new(IRFunctionRule::ConditionalRule(
            loc.clone(),
            to_ir_expression(c),
            to_ir_expression(e),
        )),
        FunctionRule::ExpressionRule(loc, e) => Rc::new(IRFunctionRule::ExpressionRule(
            loc.clone(),
            to_ir_expression(e),
        )),
        FunctionRule::LetRule(loc, _, me, e) => Rc::new(IRFunctionRule::LetRule(
            loc.clone(),
            to_ir_match_expression(me),
            to_ir_expression(e),
        )),
    }
}

fn to_ir_expression(e: &Rc<Expression>) -> Rc<IRExpression> {
    Rc::new(match e.borrow() {
        Expression::BoolLiteral(loc, b) => IRExpression::BoolLiteral(loc.clone(), *b),
        Expression::StringLiteral(loc, s) => IRExpression::StringLiteral(loc.clone(), s.clone()),
        Expression::CharacterLiteral(loc, c) => IRExpression::CharacterLiteral(loc.clone(), *c),
        Expression::IntegerLiteral(loc, i) => IRExpression::IntegerLiteral(loc.clone(), *i),
        Expression::FloatLiteral(loc, f) => IRExpression::FloatLiteral(loc.clone(), *f),
        Expression::TupleLiteral(loc, es) => {
            IRExpression::TupleLiteral(loc.clone(), to_ir_expressions(es))
        }

        Expression::EmptyListLiteral(loc, bla) => {
            IRExpression::EmptyListLiteral(loc.clone(), to_ir_type(bla.as_ref().unwrap()))
        }
        Expression::ShorthandListLiteral(loc, list_type, es) => IRExpression::ShorthandListLiteral(
            loc.clone(),
            to_ir_type(list_type.as_ref().unwrap()),
            to_ir_expressions(es),
        ),
        Expression::LonghandListLiteral(loc, list_type, he, te) => {
            IRExpression::LonghandListLiteral(
                loc.clone(),
                to_ir_type(list_type.as_ref().unwrap()),
                to_ir_expression(he),
                to_ir_expression(te),
            )
        }
        Expression::ADTTypeConstructor(loc, adt_type, constructor_name, es) => {
            IRExpression::ADTTypeConstructor(
                loc.clone(),
                to_ir_type(adt_type.as_ref().unwrap()),
                constructor_name.clone(),
                to_ir_expressions(es),
            )
        }
        Expression::Record(loc, record_type, name, es) => IRExpression::Record(
            loc.clone(),
            to_ir_type(record_type.as_ref().unwrap()),
            name.clone(),
            es.iter()
                .map(|(n, e)| (n.clone(), to_ir_expression(e)))
                .collect(),
        ),
        Expression::Case(loc, e, rules, e_type) => IRExpression::Case(
            loc.clone(),
            to_ir_expression(e),
            rules
                .iter()
                .map(|r| {
                    Rc::new(IRCaseRule {
                        loc_info: r.loc_info.clone(),
                        case_rule: to_ir_match_expression(&r.case_rule),
                        result_rule: to_ir_expression(&r.result_rule),
                    })
                })
                .collect(),
            to_ir_type(e_type.as_ref().unwrap()),
        ),
        Expression::Call(loc, function_type, name, es) => IRExpression::Call(
            loc.clone(),
            to_ir_type(function_type.as_ref().unwrap()),
            name.clone(),
            to_ir_expressions(es),
        ),
        Expression::Variable(loc, name) => IRExpression::Variable(loc.clone(), name.clone()),

        Expression::Negation(loc, e) => IRExpression::Negation(loc.clone(), to_ir_expression(e)),
        Expression::Minus(loc, e) => IRExpression::Minus(loc.clone(), to_ir_expression(e)),
        Expression::Times(loc, le, re) => {
            IRExpression::Times(loc.clone(), to_ir_expression(le), to_ir_expression(re))
        }
        Expression::Divide(loc, le, re) => {
            IRExpression::Divide(loc.clone(), to_ir_expression(le), to_ir_expression(re))
        }
        Expression::Modulo(loc, le, re) => {
            IRExpression::Modulo(loc.clone(), to_ir_expression(le), to_ir_expression(re))
        }
        Expression::Add(loc, le, re) => {
            IRExpression::Add(loc.clone(), to_ir_expression(le), to_ir_expression(re))
        }
        Expression::Subtract(loc, le, re) => {
            IRExpression::Subtract(loc.clone(), to_ir_expression(le), to_ir_expression(re))
        }
        Expression::ShiftLeft(loc, le, re) => {
            IRExpression::ShiftLeft(loc.clone(), to_ir_expression(le), to_ir_expression(re))
        }
        Expression::ShiftRight(loc, le, re) => {
            IRExpression::ShiftRight(loc.clone(), to_ir_expression(le), to_ir_expression(re))
        }
        Expression::Greater(loc, le, re) => {
            IRExpression::Greater(loc.clone(), to_ir_expression(le), to_ir_expression(re))
        }
        Expression::Greq(loc, le, re) => {
            IRExpression::Greq(loc.clone(), to_ir_expression(le), to_ir_expression(re))
        }
        Expression::Leq(loc, le, re) => {
            IRExpression::Leq(loc.clone(), to_ir_expression(le), to_ir_expression(re))
        }
        Expression::Lesser(loc, le, re) => {
            IRExpression::Lesser(loc.clone(), to_ir_expression(le), to_ir_expression(re))
        }
        Expression::Eq(loc, le, re) => {
            IRExpression::Eq(loc.clone(), to_ir_expression(le), to_ir_expression(re))
        }
        Expression::Neq(loc, le, re) => {
            IRExpression::Neq(loc.clone(), to_ir_expression(le), to_ir_expression(re))
        }
        Expression::And(loc, le, re) => {
            IRExpression::And(loc.clone(), to_ir_expression(le), to_ir_expression(re))
        }
        Expression::Or(loc, le, re) => {
            IRExpression::Or(loc.clone(), to_ir_expression(le), to_ir_expression(re))
        }

        Expression::RecordFieldAccess(loc, record_type, record_name, el, er) => {
            IRExpression::RecordFieldAccess(
                loc.clone(),
                to_ir_type(record_type.as_ref().unwrap()),
                record_name.clone(),
                to_ir_expression(el),
                to_ir_expression(er),
            )
        }
        Expression::Lambda(_, _, _, _, _) => unreachable!(
            "Lambda's should have been replaced with proper function calls at this point"
        ),
    })
}

fn to_ir_expressions(es: &Vec<Rc<Expression>>) -> Vec<Rc<IRExpression>> {
    es.iter().map(|e| to_ir_expression(e)).collect()
}

fn to_ir_match_expression(me: &Rc<MatchExpression>) -> Rc<IRMatchExpression> {
    Rc::new(match me.borrow() {
        MatchExpression::IntLiteral(loc, i) => IRMatchExpression::IntLiteral(loc.clone(), *i),
        MatchExpression::CharLiteral(loc, c) => IRMatchExpression::CharLiteral(loc.clone(), *c),
        MatchExpression::StringLiteral(loc, s) => {
            IRMatchExpression::StringLiteral(loc.clone(), s.clone())
        }
        MatchExpression::BoolLiteral(loc, b) => IRMatchExpression::BoolLiteral(loc.clone(), *b),
        MatchExpression::Identifier(loc, id) => {
            IRMatchExpression::Identifier(loc.clone(), id.clone())
        }
        MatchExpression::Tuple(loc, mes) => {
            IRMatchExpression::Tuple(loc.clone(), to_ir_match_expressions(mes))
        }
        MatchExpression::ShorthandList(loc, mes) => {
            IRMatchExpression::ShorthandList(loc.clone(), to_ir_match_expressions(mes))
        }
        MatchExpression::LonghandList(loc, hme, tme) => IRMatchExpression::LonghandList(
            loc.clone(),
            to_ir_match_expression(hme),
            to_ir_match_expression(tme),
        ),
        MatchExpression::Wildcard(loc) => IRMatchExpression::Wildcard(loc.clone()),
        MatchExpression::ADT(loc, constructor_name, mes) => IRMatchExpression::ADT(
            loc.clone(),
            constructor_name.clone(),
            to_ir_match_expressions(mes),
        ),
        MatchExpression::Record(loc, record_name, fields) => {
            IRMatchExpression::Record(loc.clone(), record_name.clone(), fields.clone())
        }
    })
}

fn to_ir_match_expressions(mes: &Vec<Rc<MatchExpression>>) -> Vec<Rc<IRMatchExpression>> {
    mes.iter().map(|me| to_ir_match_expression(me)).collect()
}

fn to_ir_adt(adt: &Rc<ADTDefinition>) -> Rc<IRADTDefinition> {
    Rc::new(IRADTDefinition {
        name: adt.name.clone(),
        location: adt.location.clone(),
        constructors: adt
            .constructors
            .iter()
            .map(|c| {
                Rc::new(IRADTConstructor {
                    name: c.name.clone(),
                    elements: to_ir_types(&c.elements),
                })
            })
            .collect(),
    })
}

fn to_ir_record(record: &Rc<RecordDefinition>) -> Rc<IRRecordDefinition> {
    Rc::new(IRRecordDefinition {
        name: record.name.clone(),
        location: record.location.clone(),
        fields: record
            .fields
            .iter()
            .map(|(n, f)| (n.clone(), to_ir_type(f)))
            .collect(),
    })
}

fn to_ir_types(types: &Vec<Rc<Type>>) -> Vec<Rc<IRType>> {
    types.iter().map(|e| to_ir_type(e)).collect()
}

fn to_ir_type(loz_type: &Rc<Type>) -> Rc<IRType> {
    Rc::new(match loz_type.borrow() {
        Type::Bool => IRType::Bool,
        Type::Char => IRType::Bool,
        Type::String => IRType::Bool,
        Type::Int => IRType::Bool,
        Type::Float => IRType::Bool,
        Type::UserType(n, _) => IRType::UserType(n.clone()),
        Type::Tuple(elements) => IRType::Tuple(to_ir_types(elements)),
        Type::List(list_type) => IRType::List(to_ir_type(list_type)),
        Type::Variable(v) => unreachable!(
            "Variable type '{}' should no longer be encountered after rewriting and monomorphization", v
        ),
        Type::Function(argument_types, return_type) => IRType::Function(to_ir_types(argument_types), to_ir_type(return_type)),
    })
}

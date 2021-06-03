use crate::ast::{CaseRule, Expression, FunctionBody, FunctionDefinition, FunctionRule};
use crate::{Type, TypeScheme};
use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

pub fn extract_closure_variables(function: &Rc<FunctionDefinition>) -> Rc<FunctionDefinition> {
    let mut free_variables_bodies: Vec<Vec<(Rc<String>, Rc<Type>)>> = Vec::new();
    let mut free_variables_function = Vec::new();
    for b in &function.function_bodies {
        let new_variables = free_variables_body(b);
        free_variables_bodies.push(new_variables);
    }

    let free_variables_function = free_variables_bodies.iter().flat_map(|vrs| vrs.iter()).collect();

    let function_type: &Rc<Type> = &function.function_type.unwrap().enclosed_type;
    let new_function_type = match function_type.borrow() {
        Type::Function(from, to) => {
            let
        }
        t => unreachable!("Function type is not a function: {}", t),
    };

    Rc::new(FunctionDefinition {
        location: function.location.clone(),
        name: function.name.clone(),
        function_type: function.function_type.clone(),
        function_bodies,
    })
}

fn free_variables_body(body: &Rc<FunctionBody>) -> Vec<(Rc<String>, Rc<Type>)> {

    let mut introduced_variables : HashSet<Rc<String>> = body.match_expressions.iter()
        .flat_map(|me| me.variables().iter())
        .collect();
    body.rules.iter()
        .map(|r| {
            match r.borrow() {
                FunctionRule::ConditionalRule(_, c, e) => {
                    let mut civ = free_variables_expression(c, &introduced_variables);
                    civ.extend(free_variables_expression(e, &introduced_variables));
                    civ
                }
                FunctionRule::ExpressionRule(_, e) => {
                    free_variables_expression(e, &introduced_variables)
                }
                FunctionRule::LetRule(_, _, me, e) => {
                    introduced_variables.extend(me.variables());
                    free_variables_expression(e, &introduced_variables)
                }
            }
        })
        .collect()
}

fn free_variables_expression(
    e: &Rc<Expression>,
    defined: &HashSet<Rc<String>>,
) -> Vec<(Rc<String>, Rc<Type>)> {
    match e.borrow() {
        Expression::BoolLiteral(loc, b) => Vec::new(),

        Expression::StringLiteral(loc, s) => Vec::new(),
        Expression::CharacterLiteral(loc, c) => Vec::new(),
        Expression::IntegerLiteral(loc, i) => Vec::new(),
        Expression::FloatLiteral(loc, f) => Vec::new(),
        Expression::TupleLiteral(loc, es) => {
            let (es, lambdas) = free_variables_expressions(n, es);
            (Rc::new(Expression::TupleLiteral(loc.clone(), es)), lambdas)
        }
        Expression::EmptyListLiteral(loc, bla) => (
            Rc::new(Expression::EmptyListLiteral(loc.clone(), bla.clone())),
            Vec::new(),
        ),
        Expression::ShorthandListLiteral(loc, list_type, es) => {
            let (es, lambdas) = free_variables_expressions(n, es);
            (
                Rc::new(Expression::ShorthandListLiteral(
                    loc.clone(),
                    list_type.clone(),
                    es,
                )),
                lambdas,
            )
        }
        Expression::LonghandListLiteral(loc, list_type, he, te) => {
            let (he, te, lambdas) = free_variables_expression_duo(n, he, te);
            (
                Rc::new(Expression::LonghandListLiteral(
                    loc.clone(),
                    list_type.clone(),
                    he,
                    te,
                )),
                lambdas,
            )
        }

        Expression::ADTTypeConstructor(loc, adt_type, bla, blie) => {
            let (es, lambdas) = free_variables_expressions(n, blie);
            (
                Rc::new(Expression::ADTTypeConstructor(
                    loc.clone(),
                    adt_type.clone(),
                    bla.clone(),
                    es,
                )),
                lambdas,
            )
        }

        Expression::Record(loc, record_type, name, es) => {
            let mut lambdas = Vec::new();
            let mut ir_es = Vec::new();
            for (f, e) in es {
                let (e, nl) = free_variables_expression(n, e);
                for l in nl {
                    lambdas.push(l);
                }
                ir_es.push((f.clone(), e))
            }
            (
                Rc::new(Expression::Record(
                    loc.clone(),
                    record_type.clone(),
                    name.clone(),
                    ir_es,
                )),
                lambdas,
            )
        }
        Expression::Case(loc, e, rules, e_type) => {
            let mut lambdas = Vec::new();
            let (ir_e, new_lambdas) = free_variables_expression(n, e);
            lambdas.extend(new_lambdas);

            let mut ir_rules = Vec::new();
            for r in rules {
                let (ir_e, new_lambdas) = free_variables_expression(n, &r.result_rule);
                lambdas.extend(new_lambdas);
                ir_rules.push(Rc::new(CaseRule {
                    loc_info: r.loc_info.clone(),
                    type_information: r.type_information.clone(),
                    case_rule: r.case_rule.clone(),
                    result_rule: ir_e,
                }))
            }

            (
                Rc::new(Expression::Case(
                    loc.clone(),
                    ir_e,
                    ir_rules,
                    e_type.clone(),
                )),
                lambdas,
            )
        }
        Expression::Call(loc, function_type, name, es) => {
            let (ir_es, lambdas) = free_variables_expressions(n, es);
            (
                Rc::new(Expression::Call(
                    loc.clone(),
                    function_type.clone(),
                    name.clone(),
                    ir_es,
                )),
                lambdas,
            )
        }
        Expression::Variable(loc, name) => (
            Rc::new(Expression::Variable(loc.clone(), name.clone())),
            Vec::new(),
        ),

        Expression::Negation(loc, e) => {
            let (ir_e, lambdas) = free_variables_expression(n, e);
            (Rc::new(Expression::Negation(loc.clone(), ir_e)), lambdas)
        }
        Expression::Minus(loc, e) => {
            let (ir_e, lambdas) = free_variables_expression(n, e);
            (Rc::new(Expression::Minus(loc.clone(), ir_e)), lambdas)
        }

        Expression::Times(loc, le, re) => {
            let (ir_le, ir_re, lambdas) = free_variables_expression_duo(n, le, re);
            (
                Rc::new(Expression::Times(loc.clone(), ir_le, ir_re)),
                lambdas,
            )
        }
        Expression::Divide(loc, le, re) => {
            let (ir_le, ir_re, lambdas) = free_variables_expression_duo(n, le, re);
            (
                Rc::new(Expression::Divide(loc.clone(), ir_le, ir_re)),
                lambdas,
            )
        }
        Expression::Modulo(loc, le, re) => {
            let (ir_le, ir_re, lambdas) = free_variables_expression_duo(n, le, re);
            (
                Rc::new(Expression::Modulo(loc.clone(), ir_le, ir_re)),
                lambdas,
            )
        }
        Expression::Add(loc, le, re) => {
            let (ir_le, ir_re, lambdas) = free_variables_expression_duo(n, le, re);
            (Rc::new(Expression::Add(loc.clone(), ir_le, ir_re)), lambdas)
        }
        Expression::Subtract(loc, le, re) => {
            let (ir_le, ir_re, lambdas) = free_variables_expression_duo(n, le, re);
            (
                Rc::new(Expression::Subtract(loc.clone(), ir_le, ir_re)),
                lambdas,
            )
        }
        Expression::ShiftLeft(loc, le, re) => {
            let (ir_le, ir_re, lambdas) = free_variables_expression_duo(n, le, re);
            (
                Rc::new(Expression::ShiftLeft(loc.clone(), ir_le, ir_re)),
                lambdas,
            )
        }
        Expression::ShiftRight(loc, le, re) => {
            let (ir_le, ir_re, lambdas) = free_variables_expression_duo(n, le, re);
            (
                Rc::new(Expression::ShiftRight(loc.clone(), ir_le, ir_re)),
                lambdas,
            )
        }
        Expression::Greater(loc, le, re) => {
            let (ir_le, ir_re, lambdas) = free_variables_expression_duo(n, le, re);
            (
                Rc::new(Expression::Greater(loc.clone(), ir_le, ir_re)),
                lambdas,
            )
        }
        Expression::Greq(loc, le, re) => {
            let (ir_le, ir_re, lambdas) = free_variables_expression_duo(n, le, re);
            (
                Rc::new(Expression::Greq(loc.clone(), ir_le, ir_re)),
                lambdas,
            )
        }
        Expression::Leq(loc, le, re) => {
            let (ir_le, ir_re, lambdas) = free_variables_expression_duo(n, le, re);
            (Rc::new(Expression::Leq(loc.clone(), ir_le, ir_re)), lambdas)
        }
        Expression::Lesser(loc, le, re) => {
            let (ir_le, ir_re, lambdas) = free_variables_expression_duo(n, le, re);
            (
                Rc::new(Expression::Lesser(loc.clone(), ir_le, ir_re)),
                lambdas,
            )
        }
        Expression::Eq(loc, le, re) => {
            let (ir_le, ir_re, lambdas) = free_variables_expression_duo(n, le, re);
            (Rc::new(Expression::Eq(loc.clone(), ir_le, ir_re)), lambdas)
        }
        Expression::Neq(loc, le, re) => {
            let (ir_le, ir_re, lambdas) = free_variables_expression_duo(n, le, re);
            (Rc::new(Expression::Neq(loc.clone(), ir_le, ir_re)), lambdas)
        }
        Expression::And(loc, le, re) => {
            let (ir_le, ir_re, lambdas) = free_variables_expression_duo(n, le, re);
            (Rc::new(Expression::And(loc.clone(), ir_le, ir_re)), lambdas)
        }
        Expression::Or(loc, le, re) => {
            let (ir_le, ir_re, lambdas) = free_variables_expression_duo(n, le, re);
            (Rc::new(Expression::Or(loc.clone(), ir_le, ir_re)), lambdas)
        }

        Expression::RecordFieldAccess(loc, record_type, record_name, el, er) => {
            let (ir_le, ir_re, lambdas) = free_variables_expression_duo(n, el, er);
            (
                Rc::new(Expression::RecordFieldAccess(
                    loc.clone(),
                    record_type.clone(),
                    record_name.clone(),
                    ir_le,
                    ir_re,
                )),
                lambdas,
            )
        }
        Expression::Lambda(loc, lambda_type, a, b, c) => {
            let lambda_name = Rc::new(n.lambda());
            (
                Rc::new(Expression::Call(
                    loc.clone(),
                    lambda_type.clone(),
                    lambda_name.clone(),
                    vec![],
                )),
                vec![Rc::new(FunctionDefinition {
                    location: loc.clone(),
                    name: lambda_name.clone(),
                    function_type: Some(Rc::new(TypeScheme {
                        bound_variables: HashSet::new(),
                        enclosed_type: lambda_type.as_ref().unwrap().clone(),
                    })),
                    function_bodies: vec![Rc::new(FunctionBody {
                        name: lambda_name.clone(),
                        location: loc.clone(),
                        type_information: a.clone(),
                        match_expressions: b.clone(),
                        rules: vec![Rc::new(FunctionRule::ExpressionRule(
                            loc.clone(),
                            c.clone(),
                        ))],
                        local_function_definitions: HashMap::new(),
                        local_adt_definitions: HashMap::new(),
                        local_record_definitions: HashMap::new(),
                    })],
                })],
            )
        }
    }
}

fn free_variables_expression_duo(
    l: &Rc<Expression>,
    r: &Rc<Expression>,
    defined: &HashSet<Rc<String>>
) -> Vec<(Rc<String>, Rc<Type>)>{
    let mut civl = free_variables_expression(l, defined);
    civl.extend(free_variables_expression(r, defined));
    civl
}

fn free_variables_expressions(
    es: &Vec<Rc<Expression>>,
    defined: &HashSet<Rc<String>>
) -> (Vec<Rc<Expression>>, Vec<Rc<FunctionDefinition>>) {
    es.iter()
        .flat_map(|e| free_variables_expression(e, defined))
        .collect()
}

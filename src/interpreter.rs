use std::collections::HashMap;

use crate::parser::{AST, Expression, FunctionBody, FunctionRule, MatchExpression};
use crate::interpreter::InterpreterError::DivisionByZero;

#[derive(Debug, Clone)]
struct RunState {
    frames: Vec<Frame>
}

impl RunState {
    fn new() -> Self {
        RunState { frames: Vec::new() }
    }
}

#[derive(Debug, Clone)]
struct Frame {
    variables: HashMap<String, Value>
}

impl Frame {
    fn new() -> Self {
        Frame { variables: HashMap::new() }
    }
}

#[derive(Debug, Clone, PartialEq)]
enum Value {
    Bool(bool),
    Int(isize),
    Char(char),
    String(String),
    Tuple(Vec<Value>)
}

#[derive(Debug, Clone)]
pub enum InterpreterError {
    NoApplicableFunctionRule(String),
    DivisionByZero
}

pub fn interpret(ast: &AST) -> Result<(), InterpreterError> {
    let result = evaluate(&ast.main, ast, &mut RunState::new())?;
    println!("> {:?}", result);
    Ok(())
}

fn evaluate(e: &Expression, ast: &AST, state: &mut RunState) -> Result<Value, InterpreterError> {
    match e {
        Expression::BoolLiteral(_, b) => Ok(Value::Bool(*b)),
        Expression::StringLiteral(_, s) => Ok(Value::String(s.clone())),
        Expression::CharacterLiteral(_, c) => Ok(Value::Char(*c)),
        Expression::Number(_, n) => Ok(Value::Int(*n)),

        Expression::Call(_, f, args) => eval_function_call(f, args, state, ast),

        Expression::TupleLiteral(_, elements) => {
            let mut evaluated_elements = Vec::new();
            for e in elements {
                evaluated_elements.push(evaluate(e, ast, state)?);
            }
            Ok(Value::Tuple(evaluated_elements))
        }

        Expression::Variable(_, v) => Ok(state.frames.last().unwrap().variables.get(v).unwrap().clone()),
        Expression::Negation(_, e) => Ok(Value::Bool(!eval_bool(e, ast, state)?)),
        Expression::Minus(_, e) => Ok (Value::Int(- eval_int(e, ast, state)?)),
        Expression::Times(_, e1, e2) => Ok(Value::Int(eval_int(e1, ast, state)? * eval_int(e2, ast, state)?)),
        Expression::Divide(_, e1, e2) => {
            let divider = eval_int(e2, ast, state)?;
            if divider == 0 {
                return Err(DivisionByZero);
            }
            Ok(Value::Int(eval_int(e1, ast, state)? / divider))
        },
        Expression::Modulo(_, e1, e2) => Ok(Value::Int(eval_int(e1, ast, state)? % eval_int(e2, ast, state)?)),
        Expression::Add(_, e1, e2) => {
            match (evaluate(e1, ast, state)?, evaluate(e2, ast, state)?) {
                (Value::Int(l), Value::Int(r)) => Ok(Value::Int(l + r)),
                (Value::String(mut l), Value::String(r)) => {
                    l.push_str(r.as_str());
                    Ok(Value::String(l))
                }
                (l, r) => unreachable!("Addition between results {:?} and {:?}", l , r)
            }
        },
        Expression::Subtract(_, e1, e2) => Ok(Value::Int(eval_int(e1, ast, state)? - eval_int(e2, ast, state)?)),
        Expression::ShiftLeft(_, e1, e2) => Ok(Value::Int(eval_int(e1, ast, state)? << eval_int(e2, ast, state)?)),
        Expression::ShiftRight(_, e1, e2) => Ok(Value::Int(eval_int(e1, ast, state)? >> eval_int(e2, ast, state)?)),
        Expression::Greater(_, e1, e2) => Ok(Value::Bool(eval_int(e1, ast, state)? > eval_int(e2, ast, state)?)),
        Expression::Greq(_, e1, e2) => Ok(Value::Bool(eval_int(e1, ast, state)? >= eval_int(e2, ast, state)?)),
        Expression::Leq(_, e1, e2) => Ok(Value::Bool(eval_int(e1, ast, state)? <= eval_int(e2, ast, state)?)),
        Expression::Lesser(_, e1, e2) => Ok(Value::Bool(eval_int(e1, ast, state)? < eval_int(e2, ast, state)?)),
        Expression::Eq(_, e1, e2) => Ok(Value::Bool(evaluate(e1, ast, state)? == evaluate(e2, ast, state)?)),
        Expression::Neq(_, e1, e2) => Ok(Value::Bool(evaluate(e1, ast, state)? != evaluate(e2, ast, state)?)),
        Expression::And(_, e1, e2) => Ok(Value::Bool(eval_bool(e1, ast, state)? && eval_bool(e2, ast, state)?)),
        Expression::Or(_, e1, e2) => Ok(Value::Bool(eval_bool(e1, ast, state)? || eval_bool(e2, ast, state)?)),
    }
}

fn eval_function_call(f: &String, args: &Vec<Expression>, state: &mut RunState, ast: &AST) -> Result<Value, InterpreterError> {
    let declaration = ast.function_declarations.get(f).unwrap();

    // TODO: We only support single-body functions for now.
    let mut frame = Frame::new();
    for (arg_name, value_expression) in declaration.function_bodies.get(0).unwrap().parameters.iter().zip(args.iter()) {
        frame.variables.insert(arg_name.clone(), evaluate(value_expression, ast, state)?);
    }
    state.frames.push(frame);

    eval_function_body(f,declaration.function_bodies.get(0).unwrap(), state, ast)
}

fn eval_function_body(name: &String, body: &FunctionBody, state: &mut RunState, ast: &AST) -> Result<Value, InterpreterError> {
    //println!("Evaluating function {:?} in {:?}", name, state.frames.last().unwrap());

    for rule in &body.rules {
        match rule {
            FunctionRule::ConditionalRule(_, condition_expression, result_expression) => {
                if eval_bool(&condition_expression, ast, state)? {
                    return evaluate(&result_expression, ast, state);
                }
            },
            FunctionRule::ExpressionRule(_, result_expression) => return evaluate(&result_expression, ast, state),
            FunctionRule::LetRule(_, match_expression, e) => {
                let variables = collect_match_variables(match_expression, &evaluate(e, ast, state)?);

                state.frames.last_mut().unwrap().variables.extend(variables);
            }
        }
    }

    Err(InterpreterError::NoApplicableFunctionRule(name.clone()))
}

fn collect_match_variables(match_expression: &MatchExpression, evaluated_expression: &Value) -> HashMap<String, Value> {
    match (match_expression, evaluated_expression) {
        (MatchExpression::Identifier(identifier), value) => {
            let mut map = HashMap::new();
            map.insert(identifier.clone(), value.clone());
            return map
        },
        (MatchExpression::Tuple(elements), Value::Tuple(values)) => {
            let mut map = HashMap::new();
            for (e , v) in elements.iter().zip(values.iter()) {
                map.extend(collect_match_variables(e, v));
            }
            return map;
        },
        _ => unreachable!()

    }
}

fn eval_bool(e: &Expression, ast: &AST, state: &mut RunState) -> Result<bool, InterpreterError> {
    match evaluate(e, ast, state) {
        Ok(Value::Bool(b)) => Ok(b),
        _ => unreachable!("evaluate wrong type (expected bool)")
    }
}

fn eval_int(e: &Expression, ast: &AST, state: &mut RunState) -> Result<isize, InterpreterError> {
    match evaluate(e, ast, state) {
        Ok(Value::Int(n)) => Ok(n),
        _ => unreachable!("evaluate wrong type (expected int)")
    }
}

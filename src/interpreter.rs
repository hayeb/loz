use std::collections::HashMap;

use crate::interpreter::InterpreterError::{DivisionByZero, NoApplicableFunctionBody};
use crate::parser::{AST, Expression, FunctionBody, FunctionRule, MatchExpression};

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
pub enum Value {
    Bool(bool),
    Int(isize),
    Float(f64),
    Char(char),
    String(String),
    Tuple(Vec<Value>),
    List(Vec<Value>),
    CustomValue(String, Vec<Value>),
}

#[derive(Debug, Clone)]
pub enum InterpreterError {
    NoApplicableFunctionRule(String),
    NoApplicableFunctionBody(String),
    DivisionByZero,
    ExpressionDoesNotMatch(MatchExpression, Value),
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
        Expression::Float(_, f) => Ok(Value::Float(*f)),

        Expression::Call(_, f, args) => eval_function_call(f, args, state, ast),

        Expression::ADTTypeConstructor(_, name, arguments) => {
            let mut evaluated_arguments = Vec::new();
            for e in arguments {
                evaluated_arguments.push(evaluate(e, ast, state)?);
            }
            Ok(Value::CustomValue(name.clone(), evaluated_arguments))
        }

        Expression::TupleLiteral(_, elements) => {
            let mut evaluated_elements = Vec::new();
            for e in elements {
                evaluated_elements.push(evaluate(e, ast, state)?);
            }
            Ok(Value::Tuple(evaluated_elements))
        }
        Expression::EmptyListLiteral(_) => Ok(Value::List(vec![])),
        Expression::ShorthandListLiteral(_, elements) => {
            let mut evaluated_elements = Vec::new();
            for e in elements {
                evaluated_elements.push(evaluate(e, ast, state)?);
            }
            Ok(Value::List(evaluated_elements))
        }
        Expression::LonghandListLiteral(_, head, tail) => {
            let evaluated_head = evaluate(head, ast, state)?;
            let evaluated_tail = evaluate(tail, ast, state)?;

            let mut results = vec![evaluated_head];
            match evaluated_tail {
                Value::List(values) => {
                    results.extend(values);
                    Ok(Value::List(results))
                }
                v => unreachable!("tail evaluated to '{:?}' instead of Value::List", v)
            }
        }

        Expression::InlineMatch(_, identifier, match_expression) => {
            //println!("Evaluate InlineMatch: {} {:?}", identifier, match_expression);
            let identifier_value = state.frames.last().unwrap().variables.get(identifier).unwrap();
            //println!("Identifier value: {:?}", identifier_value);
            let match_result = collect_match_variables(match_expression, identifier_value);
            match match_result {
                Ok(variables) => {
                    state.frames.last_mut().unwrap().variables.extend(variables);
                    //println!("{:?} matches", match_expression);
                    Ok(Value::Bool(true))
                }
                Err(InterpreterError::ExpressionDoesNotMatch(_, _)) => {
                    //println!("{:?} does not match", match_expression);
                    Ok(Value::Bool(false))
                }
                Err(e) => Err(e)
            }
        }

        Expression::Variable(_, v) => Ok(state.frames.last().unwrap().variables.get(v).unwrap().clone()),
        Expression::Negation(_, e) => Ok(Value::Bool(!eval_bool(e, ast, state)?)),
        Expression::Minus(_, e) => Ok(Value::Int(-eval_int(e, ast, state)?)),
        Expression::Times(_, e1, e2) => {
            match (evaluate(e1, ast, state)?, evaluate(e2, ast, state)?) {
                (Value::Int(x), Value::Int(y)) => Ok(Value::Int(x * y)),
                (Value::Int(x), Value::Float(y)) => Ok(Value::Float(x as f64 * y)),
                (Value::Float(x), Value::Int(y)) => Ok(Value::Float(x * y as f64)),
                (Value::Float(x), Value::Float(y)) => Ok(Value::Float(x * y)),
                _ => unreachable!()
            }
        }
        Expression::Divide(_, e1, e2) => {
            let divider = evaluate(e2, ast, state)?;
            if let Value::Int(0) = divider {
                return Err(DivisionByZero);
            }
            match (evaluate(e1, ast, state)?, divider) {
                (Value::Int(x), Value::Int(y)) => Ok(Value::Int(x / y)),
                (Value::Int(x), Value::Float(y)) => Ok(Value::Float(x as f64 / y)),
                (Value::Float(x), Value::Int(y)) => Ok(Value::Float(x / y as f64)),
                (Value::Float(x), Value::Float(y)) => Ok(Value::Float(x / y)),
                _ => unreachable!()
            }
        }
        Expression::Modulo(_, e1, e2) => Ok(Value::Int(eval_int(e1, ast, state)? % eval_int(e2, ast, state)?)),
        Expression::Add(_, e1, e2) => {
            match (evaluate(e1, ast, state)?, evaluate(e2, ast, state)?) {
                (Value::Int(x), Value::Int(y)) => Ok(Value::Int(x + y)),
                (Value::Int(x), Value::Float(y)) => Ok(Value::Float(x as f64 + y)),
                (Value::Float(x), Value::Int(y)) => Ok(Value::Float(x + y as f64)),
                (Value::Float(x), Value::Float(y)) => Ok(Value::Float(x + y)),
                (Value::String(mut l), Value::String(r)) => {
                    l.push_str(r.as_str());
                    Ok(Value::String(l))
                }
                (l, r) => unreachable!("Addition between results {:?} and {:?}", l, r)
            }
        }
        Expression::Subtract(_, e1, e2) => {
            match (evaluate(e1, ast, state)?, evaluate(e2, ast, state)?) {
                (Value::Int(x), Value::Int(y)) => Ok(Value::Int(x - y)),
                (Value::Int(x), Value::Float(y)) => Ok(Value::Float(x as f64 - y)),
                (Value::Float(x), Value::Int(y)) => Ok(Value::Float(x - y as f64)),
                (Value::Float(x), Value::Float(y)) => Ok(Value::Float(x - y)),
                _ => unreachable!()
            }
        }
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

    for body in &declaration.function_bodies {
        let mut body_frame = Frame::new();

        let mut matches = true;

        for (match_expression, value) in body.match_expressions.iter().zip(args.iter()) {
            match collect_match_variables(match_expression, &evaluate(value, ast, state)?) {
                Ok(variables) => body_frame.variables.extend(variables),
                Err(InterpreterError::ExpressionDoesNotMatch(_, _)) => {
                    matches = false;
                    break;
                }
                Err(e) => return Err(e),
            }
        }
        if matches {
            state.frames.push(body_frame);

            let result = eval_function_body(f, &body, state, ast);

            state.frames.remove(state.frames.len() - 1);
            return result;
        }
    }
    Err(NoApplicableFunctionBody(declaration.name.clone()))
}

fn eval_function_body(name: &String, body: &FunctionBody, state: &mut RunState, ast: &AST) -> Result<Value, InterpreterError> {
    //println!("Evaluating function {:?} in {:?}", name, state.frames.last().unwrap());

    for rule in &body.rules {
        match rule {
            FunctionRule::ConditionalRule(_, condition_expression, result_expression) => {
                //println!("Evaluating {:?} in {:?}", condition_expression, state);
                if eval_bool(&condition_expression, ast, state)? {
                    return evaluate(&result_expression, ast, state);
                }
            }
            FunctionRule::ExpressionRule(_, result_expression) => return evaluate(&result_expression, ast, state),
            FunctionRule::LetRule(_, match_expression, e) => {
                let variables = collect_match_variables(match_expression, &evaluate(e, ast, state)?)?;

                state.frames.last_mut().unwrap().variables.extend(variables);
            }
        }
    }

    Err(InterpreterError::NoApplicableFunctionRule(name.clone()))
}

fn collect_match_variables(match_expression: &MatchExpression, evaluated_expression: &Value) -> Result<HashMap<String, Value>, InterpreterError> {
    //println!("Collecting match variables match_expression '{:?}' value '{:?}'", match_expression, evaluated_expression);
    match (match_expression, evaluated_expression) {
        (MatchExpression::Identifier(identifier), value) => {
            let mut map = HashMap::new();
            map.insert(identifier.clone(), value.clone());
            Ok(map)
        }
        (MatchExpression::Number(_n), Value::Int(n)) => {
            if _n == n {
                return Ok(HashMap::new());
            }
            Err(InterpreterError::ExpressionDoesNotMatch(MatchExpression::Number(_n.clone()), Value::Int(n.clone())))
        }
        (MatchExpression::CharLiteral(_c), Value::Char(c)) => {
            if _c == c {
                return Ok(HashMap::new());
            }
            Err(InterpreterError::ExpressionDoesNotMatch(MatchExpression::CharLiteral(_c.clone()), Value::Char(c.clone())))
        }
        (MatchExpression::StringLiteral(_s), Value::String(s)) => {
            if _s == s {
                return Ok(HashMap::new());
            }
            Err(InterpreterError::ExpressionDoesNotMatch(MatchExpression::StringLiteral(_s.clone()), Value::String(s.clone())))
        }
        (MatchExpression::BoolLiteral(_b), Value::Bool(b)) => {
            if _b == b {
                return Ok(HashMap::new());
            }
            Err(InterpreterError::ExpressionDoesNotMatch(MatchExpression::BoolLiteral(_b.clone()), Value::Bool(b.clone())))
        }

        (MatchExpression::Tuple(elements), Value::Tuple(values)) => {
            let mut map = HashMap::new();
            for (e, v) in elements.iter().zip(values.iter()) {
                map.extend(collect_match_variables(e, v)?);
            }
            Ok(map)
        }
        (MatchExpression::ShorthandList(elements), Value::List(values)) => {
            if elements.len() != values.len() {
                return Err(InterpreterError::ExpressionDoesNotMatch(MatchExpression::ShorthandList(elements.clone()), Value::List(values.clone())));
            }

            let mut map = HashMap::new();
            for (e, v) in elements.iter().zip(values.iter()) {
                map.extend(collect_match_variables(e, v)?);
            }
            Ok(map)
        }
        (MatchExpression::LonghandList(head, tail), Value::List(values)) => {
            //println!("Matching longhand list: [{:?} : {:?}] with value List({:?})", head, tail, values);
            if values.is_empty() {
                return Err(InterpreterError::ExpressionDoesNotMatch(MatchExpression::LonghandList(head.clone(), tail.clone()), Value::List(values.clone())));
            }

            let mut head_variables = collect_match_variables(head, values.iter().next().unwrap())?;
            let tail_variables = collect_match_variables(tail, &Value::List(values.iter().skip(1).cloned().collect()))?;
            head_variables.extend(tail_variables);

            Ok(head_variables)
        }
        (MatchExpression::ADT(match_name, match_arguments), Value::CustomValue(name, arguments)) => {
            if match_name != name {
                return Err(InterpreterError::ExpressionDoesNotMatch(MatchExpression::ADT(match_name.clone(), match_arguments.clone()), Value::CustomValue(name.clone(), arguments.clone())));
            }

            let mut variables = HashMap::new();
            for (e, v) in match_arguments.iter().zip(arguments.iter()) {
                variables.extend(collect_match_variables(e, v)?);
            }
            Ok(variables)
        }
        (MatchExpression::Wildcard, _type) => Ok(HashMap::new()),
        (mexpr, mvalue) => unreachable!("Could not collect match variables for expression {:?} with value {:?}", mexpr, mvalue)
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
        e => unreachable!("evaluate wrong type (expected int): {:?}", e)
    }
}

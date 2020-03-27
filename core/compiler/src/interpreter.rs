use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Error, Formatter};

use crate::{
    Expression, FunctionBody, FunctionDefinition, FunctionRule, Location, MatchExpression,
};
use crate::inferencer::TypedAST;
use crate::interpreter::InterpreterError::{DivisionByZero, NoApplicableFunctionBody};

#[derive(Debug, Clone)]
struct RunState {
    frames: Vec<Frame>,
}

impl RunState {
    fn push_frame(&mut self, frame: Frame) {
        self.frames.push(frame)
    }

    fn pop_frame(&mut self) -> Frame {
        return self.frames.remove(self.frames.len() - 1);
    }

    fn retrieve_variable_value(&self, name: &String) -> Value {
        for f in self.frames.iter().rev() {
            let val = f.variables.get(name);
            if let Some(v) = val {
                return v.clone();
            }
        }
        panic!("No value for variable {}", name);
    }

    fn get_function_definition(&self, name: &str) -> Option<FunctionDefinition> {
        for f in self.frames.iter().rev() {
            if let Some(function_definition) = f.declared_functions.get(name) {
                return Some(function_definition.clone());
            }
        }
        None
    }
}

#[derive(Debug, Clone)]
struct Frame {
    variables: HashMap<String, Value>,
    declared_functions: HashMap<String, FunctionDefinition>,
}

impl Frame {
    fn new() -> Self {
        Frame {
            variables: HashMap::new(),
            declared_functions: HashMap::new(),
        }
    }
    fn with_variables(variables: HashMap<String, Value>) -> Self {
        Frame {
            variables,
            declared_functions: HashMap::new(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Value {
    Bool(bool),
    Int(isize),
    Float(f64),
    Char(char),
    String(String),
    Tuple(Vec<Value>),
    List(Vec<Value>),
    ADTValue(String, Vec<Value>),
    RecordValue(HashMap<String, Value>),

    /* We keep currently curried-in values in the lambda itself.
       We keep a Vec of function bodies. In the following case:
        # f = \a b. as + b
       The lambda will just contain a single body.

       When we curry a "proper" function definition:
        f :: Int Int -> Int
        f 0 0 = 0
        f 1 0 = 0
        f 0 1 = 0
        f x y = x * y
        ...
        # ff = f 1
       there will be multiple function bodies in the list.
     */

    Lambda(Vec<Value>, HashMap<String, Value>, Vec<FunctionBody>),
}

impl Display for Value {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        match self {
            Value::Bool(b) => write!(f, "{}", b),
            Value::Int(i) => write!(f, "{}", i),
            Value::Float(float) => write!(f, "{}", float),
            Value::Char(c) => write!(f, "{}", c),
            Value::String(s) => write!(f, "\"{}\"", s),
            Value::Tuple(elements) => write!(
                f,
                "({})",
                elements
                    .iter()
                    .map(|e| e.to_string())
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            Value::List(elements) => write!(
                f,
                "[{}]",
                elements
                    .iter()
                    .map(|e| e.to_string())
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            Value::ADTValue(constructor, arguments) => write!(
                f,
                "{} {}",
                constructor,
                arguments
                    .iter()
                    .map(|a| a.to_string())
                    .collect::<Vec<String>>()
                    .join(" ")
            ),
            Value::RecordValue(fields) => write!(
                f,
                "{{{}}}",
                fields
                    .iter()
                    .map(|(name, value)| format!("{} = {}", name, value))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            Value::Lambda(curried_arguments, _captured_variables, bodies) => write!(f, "Lambda with {} args, {} args already curried in", bodies.get(0).unwrap().match_expressions.len(), curried_arguments.len()),
        }
    }
}

#[derive(Debug, Clone)]
pub enum InterpreterError {
    NoApplicableFunctionRule(String),
    NoApplicableFunctionBody(String),
    DivisionByZero,
    ExpressionDoesNotMatch(MatchExpression, Value),
    NoMatchingCaseRule(Value),
}

pub fn interpret(ast: &TypedAST) -> Result<(), InterpreterError> {
    let result = evaluate(
        &Expression::Call(
            Location {
                file: "?".to_string(),
                function: "main".to_string(),
                line: 1,
                col: 1,
            },
            "main".to_string(),
            vec![],
        ),
        &mut RunState {
            frames: vec![Frame {
                variables: HashMap::new(),
                declared_functions: ast.function_name_to_declaration.clone(),
            }],
        },
    )?;
    println!("{}", result);
    Ok(())
}

fn evaluate(e: &Expression, state: &mut RunState) -> Result<Value, InterpreterError> {
    match e {
        Expression::BoolLiteral(_, b) => Ok(Value::Bool(*b)),
        Expression::StringLiteral(_, s) => Ok(Value::String(s.clone())),
        Expression::CharacterLiteral(_, c) => Ok(Value::Char(*c)),
        Expression::IntegerLiteral(_, n) => Ok(Value::Int(*n)),
        Expression::FloatLiteral(_, f) => Ok(Value::Float(*f)),

        Expression::Call(_, f, args) => eval_function_call(f, args, state),

        Expression::ADTTypeConstructor(_, name, arguments) => {
            let mut evaluated_arguments = Vec::new();
            for e in arguments {
                evaluated_arguments.push(evaluate(e, state)?);
            }
            Ok(Value::ADTValue(name.clone(), evaluated_arguments))
        }

        Expression::Record(_, _, field_expressions) => {
            let mut result = HashMap::new();
            for (name, expression) in field_expressions.iter() {
                result.insert(name.clone(), evaluate(expression, state)?);
            }
            Ok(Value::RecordValue(result))
        }

        Expression::TupleLiteral(_, elements) => {
            let mut evaluated_elements = Vec::new();
            for e in elements {
                evaluated_elements.push(evaluate(e, state)?);
            }
            Ok(Value::Tuple(evaluated_elements))
        }
        Expression::EmptyListLiteral(_) => Ok(Value::List(vec![])),
        Expression::ShorthandListLiteral(_, elements) => {
            let mut evaluated_elements = Vec::new();
            for e in elements {
                evaluated_elements.push(evaluate(e, state)?);
            }
            Ok(Value::List(evaluated_elements))
        }
        Expression::LonghandListLiteral(_, head, tail) => {
            let evaluated_head = evaluate(head, state)?;
            let evaluated_tail = evaluate(tail, state)?;

            let mut results = vec![evaluated_head];
            match evaluated_tail {
                Value::List(values) => {
                    results.extend(values);
                    Ok(Value::List(results))
                }
                v => unreachable!("tail evaluated to '{:?}' instead of Value::List", v),
            }
        }

        Expression::Case(_, e, rules) => {
            let evaluated = evaluate(e, state)?;
            for rule in rules {
                let r = collect_match_variables(&rule.case_rule, &evaluated);
                if let Err(InterpreterError::ExpressionDoesNotMatch(_, _)) = r {
                    continue;
                }
                if let Err(e) = r {
                    return Err(e);
                }
                if let Ok(vars) = r {
                    state.push_frame(Frame::with_variables(vars));
                    let r = evaluate(&rule.result_rule, state);
                    state.pop_frame();
                    return r;
                }
            }
            Err(InterpreterError::NoMatchingCaseRule(evaluated))
        }

        Expression::Variable(_, v) => Ok(state.retrieve_variable_value(v)),
        Expression::Negation(_, e) => Ok(Value::Bool(!eval_bool(e, state)?)),
        Expression::Minus(_, e) => Ok(Value::Int(-eval_int(e, state)?)),
        Expression::Times(_, e1, e2) => match (evaluate(e1, state)?, evaluate(e2, state)?) {
            (Value::Int(x), Value::Int(y)) => Ok(Value::Int(x * y)),
            (Value::Int(x), Value::Float(y)) => Ok(Value::Float(x as f64 * y)),
            (Value::Float(x), Value::Int(y)) => Ok(Value::Float(x * y as f64)),
            (Value::Float(x), Value::Float(y)) => Ok(Value::Float(x * y)),
            _ => unreachable!(),
        },
        Expression::Divide(_, e1, e2) => {
            let divider = evaluate(e2, state)?;
            if let Value::Int(0) = divider {
                return Err(DivisionByZero);
            }
            match (evaluate(e1, state)?, divider) {
                (Value::Int(x), Value::Int(y)) => Ok(Value::Int(x / y)),
                (Value::Int(x), Value::Float(y)) => Ok(Value::Float(x as f64 / y)),
                (Value::Float(x), Value::Int(y)) => Ok(Value::Float(x / y as f64)),
                (Value::Float(x), Value::Float(y)) => Ok(Value::Float(x / y)),
                _ => unreachable!(),
            }
        }
        Expression::Modulo(_, e1, e2) => {
            Ok(Value::Int(eval_int(e1, state)? % eval_int(e2, state)?))
        }
        Expression::Add(_, e1, e2) => match (evaluate(e1, state)?, evaluate(e2, state)?) {
            (Value::Int(x), Value::Int(y)) => Ok(Value::Int(x + y)),
            (Value::Int(x), Value::Float(y)) => Ok(Value::Float(x as f64 + y)),
            (Value::Float(x), Value::Int(y)) => Ok(Value::Float(x + y as f64)),
            (Value::Float(x), Value::Float(y)) => Ok(Value::Float(x + y)),
            (Value::String(mut l), Value::String(r)) => {
                l.push_str(r.as_str());
                Ok(Value::String(l))
            }
            (l, r) => unreachable!("Addition between results {:?} and {:?}", l, r),
        },
        Expression::Subtract(_, e1, e2) => match (evaluate(e1, state)?, evaluate(e2, state)?) {
            (Value::Int(x), Value::Int(y)) => Ok(Value::Int(x - y)),
            (Value::Int(x), Value::Float(y)) => Ok(Value::Float(x as f64 - y)),
            (Value::Float(x), Value::Int(y)) => Ok(Value::Float(x - y as f64)),
            (Value::Float(x), Value::Float(y)) => Ok(Value::Float(x - y)),
            _ => unreachable!(),
        },
        Expression::ShiftLeft(_, e1, e2)
        => Ok(Value::Int(eval_int(e1, state)? << eval_int(e2, state)?)),

        Expression::ShiftRight(_, e1, e2)
        => Ok(Value::Int(eval_int(e1, state)? >> eval_int(e2, state)?)),

        Expression::Greater(_, e1, e2)
        => Ok(Value::Bool(eval_int(e1, state)? > eval_int(e2, state)?)),

        Expression::Greq(_, e1, e2)
        => Ok(Value::Bool(eval_int(e1, state)? >= eval_int(e2, state)?)),

        Expression::Leq(_, e1, e2)
        => Ok(Value::Bool(eval_int(e1, state)? <= eval_int(e2, state)?)),

        Expression::Lesser(_, e1, e2)
        => Ok(Value::Bool(eval_int(e1, state)? < eval_int(e2, state)?)),

        Expression::Eq(_, e1, e2) => Ok(Value::Bool(eq(evaluate(e1, state)?, evaluate(e2, state)?))),
        Expression::Neq(_, e1, e2) => Ok(Value::Bool(neq(evaluate(e1, state)?, evaluate(e2, state)?))),
        Expression::And(_, e1, e2)
        => Ok(Value::Bool(eval_bool(e1, state)? && eval_bool(e2, state)?)),

        Expression::Or(_, e1, e2)
        => Ok(Value::Bool(eval_bool(e1, state)? || eval_bool(e2, state)?)),

        Expression::RecordFieldAccess(_, record_expression, field_accessor) => {
            let record_value = evaluate(record_expression, state)?;
            if let Value::RecordValue(fields) = record_value {
                if let Expression::Variable(_, field) = &**field_accessor {
                    return Ok(fields.get(field).unwrap().clone());
                }
            }
            unreachable!()
        }
        Expression::Lambda(loc, args, body) => {
            let lambda_body = FunctionBody {
                name: "".to_string(),
                location: loc.clone(),
                match_expressions: args.clone(),
                rules: vec![FunctionRule::ExpressionRule(loc.clone(), *body.clone())],
                local_function_definitions: vec![],
                local_type_definitions: vec![],
            };

            let introduced_match_variables : HashSet<String> = args.iter().flat_map(|me| me.variables().into_iter()).collect();
            let captured = body.references(true).into_iter()
                .filter(|(v, _)| !introduced_match_variables.contains(v))
                .map(|(v,_)| (v.clone(), state.retrieve_variable_value(&v)))
                .collect();
            Ok(Value::Lambda(Vec::new(), captured, vec![lambda_body]))
        }
    }
}

fn eq(l: Value, r: Value) -> bool {
    match (l, r) {
        (Value::Bool(l), Value::Bool(r)) => l == r,
        (Value::Int(l), Value::Int(r)) => l == r,
        (Value::Float(l), Value::Float(r)) => l == r,
        (Value::Char(l), Value::Char(r)) => l == r,
        (Value::String(l), Value::String(r)) => l == r,
        (Value::Tuple(l), Value::Tuple(r))
        => l.into_iter().zip(r).fold(true, |b, (l, r)| b && eq(l, r)),

        (Value::List(l), Value::List(r))
        => l.into_iter().zip(r).fold(true, |b, (l, r)| b && eq(l, r)),

        (Value::ADTValue(l_constructor, l_arguments), Value::ADTValue(r_constructor, r_arguments))
        => l_constructor == r_constructor && l_arguments.into_iter().zip(r_arguments).fold(true, |b, (l, r)| b && eq(l, r)),

        (Value::RecordValue(l_values), Value::RecordValue(mut r_values)) => {
            for (k, v) in l_values {
                if !eq(v, r_values.remove(&k).unwrap()) {
                    return false
                }
            }
            return true
        },

        // This case is prevented by the type inferencer.
        (Value::Lambda(_, _, _), Value::Lambda(_, _, _)) => unreachable!(),

        (l, r) => unreachable!("eq {} and {}", l, r),
    }
}

fn neq(l: Value, r: Value) -> bool {
    match (l, r) {
        (Value::Bool(l), Value::Bool(r)) => l != r,
        (Value::Int(l), Value::Int(r)) => l != r,
        (Value::Float(l), Value::Float(r)) => l != r,
        (Value::Char(l), Value::Char(r)) => l != r,
        (Value::String(l), Value::String(r)) => l != r,

        (Value::Tuple(l), Value::Tuple(r))
        => l.into_iter().zip(r).fold(false, |b, (l, r)| b || neq(l, r)),

        (Value::List(l), Value::List(r))
        => l.into_iter().zip(r).fold(false, |b, (l, r)| b || neq(l, r)),

        (Value::ADTValue(l_constructor, l_arguments), Value::ADTValue(r_constructor, r_arguments))
        => l_constructor == r_constructor && l_arguments.into_iter().zip(r_arguments).fold(false, |b, (l, r)| b || eq(l, r)),

        (Value::RecordValue(l_values), Value::RecordValue(mut r_values)) => {
            for (k, v) in l_values {
                if neq(v, r_values.remove(&k).unwrap()) {
                    return true
                }
            }
            return false
        },

        // This case is prevented by the type inferencer.
        (Value::Lambda(_, _, _), Value::Lambda(_, _, _)) => unreachable!(),

        (l, r) => unreachable!("neq {} and {}", l, r),
    }
}

fn eval_function_call(
    f: &String,
    args: &Vec<Expression>,
    state: &mut RunState,
) -> Result<Value, InterpreterError> {
    let r = match state.get_function_definition(f) {
        Some(d) => eval_declared_function(&d, args, state),
        None => eval_lambda(f, state.retrieve_variable_value(f), args, state),
    };
    r
}

fn eval_lambda(
    f: &String,
    lambda: Value,
    args: &Vec<Expression>,
    state: &mut RunState,
) -> Result<Value, InterpreterError> {
    let (curried_argument_values, captured_variable_values, bodies) = match lambda {
        Value::Lambda(curried_argument_values, captured_variable_values, bodies) => (curried_argument_values, captured_variable_values, bodies),
        v => unreachable!("{}", v)
    };

    if curried_argument_values.len() + args.len() < bodies.get(0).unwrap().match_expressions.len() {
        // Handle currying
        let mut argument_values = Vec::new();
        for a in args {
            argument_values.push(evaluate(a, state)?);
        }

        let mut all_argument_values = Vec::new();
        all_argument_values.extend(curried_argument_values);
        all_argument_values.extend(argument_values);
        return Ok(Value::Lambda(all_argument_values, captured_variable_values, bodies));
    }

    let mut all_args = Vec::new();
    all_args.extend(curried_argument_values);

    for a in args {
        all_args.push(evaluate(a, state)?);
    }

    state.frames.push(Frame::with_variables(captured_variable_values));

    let res = eval_function_bodies(f.clone(), &bodies, &all_args, state);
    state.frames.pop();
    res
}

fn eval_function_bodies(f: String, bodies: &Vec<FunctionBody>, args: &Vec<Value>, state: &mut RunState) -> Result<Value, InterpreterError> {
    for body in bodies {
        let mut body_frame = Frame::new();

        let mut matches = true;

        for (match_expression, value) in body.match_expressions.iter().zip(args.iter()) {
            match collect_match_variables(match_expression, value) {
                Ok(variables) => body_frame.variables.extend(variables),
                Err(InterpreterError::ExpressionDoesNotMatch(_, _)) => {
                    matches = false;
                    break;
                }
                Err(e) => return Err(e),
            }
        }
        if matches {
            for function_definition in &body.local_function_definitions {
                body_frame.declared_functions.insert(
                    function_definition.name.clone(),
                    function_definition.clone(),
                );
            }

            state.frames.push(body_frame);

            let result = eval_function_body(&f, &body, state);

            state.frames.pop();
            return result;
        }
    }
    Err(NoApplicableFunctionBody(f))
}

fn eval_declared_function(
    d: &FunctionDefinition,
    args: &Vec<Expression>,
    state: &mut RunState,
) -> Result<Value, InterpreterError> {

    // Inferencer insures all bodies have the same number of arguments, so we just use the first.
    if d.function_bodies.get(0).unwrap().match_expressions.len() > args.len() {
        // Handle currying
        let mut argument_values = Vec::new();
        for a in args {
            argument_values.push(evaluate(a, state)?);
        }

        // Calling a declared function does not capture any values.
        return Ok(Value::Lambda(argument_values, HashMap::new(), d.function_bodies.clone()));
    }

    let mut arg_values = Vec::new();
    for a in args {
        arg_values.push(evaluate(a, state)?);
    }

    eval_function_bodies(d.name.clone(), &d.function_bodies, &arg_values, state)
}

fn eval_function_body(
    name: &String,
    body: &FunctionBody,
    state: &mut RunState,
) -> Result<Value, InterpreterError> {
    for rule in &body.rules {
        match rule {
            FunctionRule::ConditionalRule(_, condition_expression, result_expression) => {
                if eval_bool(&condition_expression, state)? {
                    return evaluate(&result_expression, state);
                }
            }
            FunctionRule::ExpressionRule(_, result_expression) => {
                return evaluate(&result_expression, state);
            }

            FunctionRule::LetRule(_, match_expression, e) => {
                let variables = collect_match_variables(match_expression, &evaluate(e, state)?)?;
                state.frames.last_mut().unwrap().variables.extend(variables);
            }
        }
    }

    Err(InterpreterError::NoApplicableFunctionRule(name.clone()))
}

fn collect_match_variables(
    match_expression: &MatchExpression,
    evaluated_expression: &Value,
) -> Result<HashMap<String, Value>, InterpreterError> {
    match (match_expression, evaluated_expression) {
        (MatchExpression::Identifier(_loc_info, identifier), value) => {
            let mut map = HashMap::new();
            map.insert(identifier.clone(), value.clone());
            Ok(map)
        }
        (MatchExpression::IntLiteral(loc_info, _n), Value::Int(n)) => {
            if _n == n {
                return Ok(HashMap::new());
            }
            Err(InterpreterError::ExpressionDoesNotMatch(
                MatchExpression::IntLiteral(loc_info.clone(), _n.clone()),
                Value::Int(n.clone()),
            ))
        }
        (MatchExpression::CharLiteral(loc_info, _c), Value::Char(c)) => {
            if _c == c {
                return Ok(HashMap::new());
            }
            Err(InterpreterError::ExpressionDoesNotMatch(
                MatchExpression::CharLiteral(loc_info.clone(), _c.clone()),
                Value::Char(c.clone()),
            ))
        }
        (MatchExpression::StringLiteral(loc_info, _s), Value::String(s)) => {
            if _s == s {
                return Ok(HashMap::new());
            }
            Err(InterpreterError::ExpressionDoesNotMatch(
                MatchExpression::StringLiteral(loc_info.clone(), _s.clone()),
                Value::String(s.clone()),
            ))
        }
        (MatchExpression::BoolLiteral(loc_info, _b), Value::Bool(b)) => {
            if _b == b {
                return Ok(HashMap::new());
            }
            Err(InterpreterError::ExpressionDoesNotMatch(
                MatchExpression::BoolLiteral(loc_info.clone(), _b.clone()),
                Value::Bool(b.clone()),
            ))
        }

        (MatchExpression::Tuple(_loc_info, elements), Value::Tuple(values)) => {
            let mut map = HashMap::new();
            for (e, v) in elements.iter().zip(values.iter()) {
                map.extend(collect_match_variables(e, v)?);
            }
            Ok(map)
        }
        (MatchExpression::ShorthandList(loc_info, elements), Value::List(values)) => {
            if elements.len() != values.len() {
                return Err(InterpreterError::ExpressionDoesNotMatch(
                    MatchExpression::ShorthandList(loc_info.clone(), elements.clone()),
                    Value::List(values.clone()),
                ));
            }

            let mut map = HashMap::new();
            for (e, v) in elements.iter().zip(values.iter()) {
                map.extend(collect_match_variables(e, v)?);
            }
            Ok(map)
        }
        (MatchExpression::LonghandList(loc_info, head, tail), Value::List(values)) => {
            if values.is_empty() {
                return Err(InterpreterError::ExpressionDoesNotMatch(
                    MatchExpression::LonghandList(loc_info.clone(), head.clone(), tail.clone()),
                    Value::List(values.clone()),
                ));
            }

            let mut head_variables = collect_match_variables(head, values.iter().next().unwrap())?;
            let tail_variables = collect_match_variables(
                tail,
                &Value::List(values.iter().skip(1).cloned().collect()),
            )?;
            head_variables.extend(tail_variables);

            Ok(head_variables)
        }
        (
            MatchExpression::ADT(loc_info, match_name, match_arguments),
            Value::ADTValue(name, arguments),
        ) => {
            if match_name != name {
                return Err(InterpreterError::ExpressionDoesNotMatch(
                    MatchExpression::ADT(
                        loc_info.clone(),
                        match_name.clone(),
                        match_arguments.clone(),
                    ),
                    Value::ADTValue(name.clone(), arguments.clone()),
                ));
            }

            let mut variables = HashMap::new();
            for (e, v) in match_arguments.iter().zip(arguments.iter()) {
                variables.extend(collect_match_variables(e, v)?);
            }
            Ok(variables)
        }
        (MatchExpression::Record(_loc_info, _name, fields), Value::RecordValue(field_to_value)) => {
            Ok(fields
                .iter()
                .map(|field| (field.clone(), field_to_value.get(field).unwrap().clone()))
                .collect())
        }
        (MatchExpression::Wildcard(_loc_info), _type) => Ok(HashMap::new()),
        (mexpr, mvalue) => unreachable!(
            "Could not collect match variables for expression {:?} with value {:?}",
            mexpr, mvalue
        ),
    }
}

fn eval_bool(e: &Expression, state: &mut RunState) -> Result<bool, InterpreterError> {
    match evaluate(e, state) {
        Ok(Value::Bool(b)) => Ok(b),
        _ => unreachable!("evaluate wrong type (expected bool)"),
    }
}

fn eval_int(e: &Expression, state: &mut RunState) -> Result<isize, InterpreterError> {
    match evaluate(e, state) {
        Ok(Value::Int(n)) => Ok(n),
        e => unreachable!("evaluate wrong type (expected int): {:?}", e),
    }
}

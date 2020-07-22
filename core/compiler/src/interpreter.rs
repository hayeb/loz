use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Error, Formatter};

use crate::interpreter::InterpreterError::{DivisionByZero, NoApplicableFunctionBody};
use crate::rewriter::RuntimeModule;
use crate::{
    body_references, Expression, FunctionBody, FunctionDefinition, FunctionRule, Location,
    MatchExpression,
};
use std::borrow::Borrow;
use std::rc::Rc;

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

    fn retrieve_variable_value(&self, name: &String, loc: &Location) -> Rc<Value> {
        for f in self.frames.iter().rev() {
            let val = f.variables.get(name);
            if let Some(v) = val {
                return Rc::clone(v);
            }

            if let Some(d) = f.declared_functions.get(name) {
                let closures = d
                    .function_bodies
                    .iter()
                    .map(|fb| {
                        Rc::new(FunctionClosure {
                            closed_variables: body_references(fb, true)
                                .iter()
                                // A function can refer itself. Skip that reference to stop infinite recursion
                                .filter(|(v, _)| v != &d.name)
                                .map(|(v, loc)| (v.clone(), self.retrieve_variable_value(v, loc)))
                                .collect(),
                            body: Rc::clone(fb),
                        })
                    })
                    .collect();

                return Rc::new(Value::Lambda(Vec::new(), closures));
            }
        }
        panic!(
            "No value for variable '{}' at '{}'. Available frames:\n {:#?}",
            name, loc, self.frames
        );
    }

    fn get_function_definition(&self, name: &Rc<String>) -> Option<Rc<FunctionDefinition>> {
        for f in self.frames.iter().rev() {
            if let Some(function_definition) = f.declared_functions.get(name) {
                return Some(Rc::clone(function_definition));
            }
        }
        None
    }

    fn determine_closure(
        &self,
        args: &Vec<Rc<MatchExpression>>,
        references: &HashSet<(Rc<String>, Rc<Location>)>,
    ) -> HashMap<Rc<String>, Rc<Value>> {
        let introduced_match_variables: HashSet<Rc<String>> = args
            .iter()
            .flat_map(|me| me.variables().into_iter())
            .collect();
        references
            .into_iter()
            .filter(|(v, _)| !introduced_match_variables.contains(v))
            .map(|(v, loc)| (v.clone(), self.retrieve_variable_value(&v, loc)))
            .collect()
    }
}

#[derive(Debug, Clone)]
struct Frame {
    variables: HashMap<Rc<String>, Rc<Value>>,
    declared_functions: HashMap<Rc<String>, Rc<FunctionDefinition>>,
}

impl Frame {
    fn new() -> Self {
        Frame {
            variables: HashMap::new(),
            declared_functions: HashMap::new(),
        }
    }
    fn with_variables(variables: HashMap<Rc<String>, Rc<Value>>) -> Self {
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
    String(Rc<String>),
    Tuple(Vec<Rc<Value>>),
    List(Vec<Rc<Value>>),
    ADTValue(Rc<String>, Vec<Rc<Value>>),
    RecordValue(Vec<(Rc<String>, Rc<Value>)>),

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
    Lambda(
        Vec<Rc<Value>>, // Curried-in values (evaluated expressions)
        Vec<Rc<FunctionClosure>>,
    ),
}

#[derive(Debug, Clone)]
pub struct FunctionClosure {
    closed_variables: HashMap<Rc<String>, Rc<Value>>,
    body: Rc<FunctionBody>,
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
            Value::ADTValue(constructor, arguments) if arguments.len() == 0 => {
                write!(f, "{}", constructor)
            }
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
            Value::Lambda(curried_arguments, closures) => write!(
                f,
                "Lambda with {} args, {} args already curried in",
                closures.get(0).unwrap().body.match_expressions.len(),
                curried_arguments.len()
            ),
        }
    }
}

#[derive(Debug, Clone)]
pub enum InterpreterError {
    NoApplicableFunctionRule(Rc<String>),
    NoApplicableFunctionBody(Rc<String>),
    DivisionByZero,
    ExpressionDoesNotMatch(MatchExpression, Rc<Value>),
    NoMatchingCaseRule(Rc<Value>),
}

impl Display for InterpreterError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            InterpreterError::NoApplicableFunctionRule(name) => {
                write!(f, "No applicable function rule in {}", name)
            }
            NoApplicableFunctionBody(name) => write!(f, "No applicable function body for {}", name),
            DivisionByZero => write!(f, "Division by zero"),
            InterpreterError::ExpressionDoesNotMatch(me, value) => write!(
                f,
                "Expression does not match\nMatch expression: {:?}\nValue: {}",
                me, value
            ),
            InterpreterError::NoMatchingCaseRule(_) => write!(f, "No matching case rule"),
        }
    }
}

pub fn interpret(runtime_module: Rc<RuntimeModule>) -> Result<Rc<Value>, InterpreterError> {
    let mut main_function_name = String::new();
    main_function_name.push_str(&runtime_module.name);
    main_function_name.push_str("::main");
    let result = evaluate(
        &Expression::Call(
            Rc::new(Location {
                module: Rc::clone(&runtime_module.name),
                function: Rc::new("main".to_string()),
                line: 1,
                col: 1,
            }),
            Rc::new(main_function_name),
            vec![],
        ),
        &mut RunState {
            frames: vec![Frame {
                variables: HashMap::new(),
                declared_functions: runtime_module
                    .functions
                    .iter()
                    .map(|(n, d)| (Rc::clone(n), Rc::clone(d)))
                    .collect(),
            }],
        },
    )?;
    Ok(result)
}

fn evaluate(e: &Expression, state: &mut RunState) -> Result<Rc<Value>, InterpreterError> {
    match e {
        Expression::BoolLiteral(_, b) => Ok(Rc::new(Value::Bool(*b))),
        Expression::StringLiteral(_, s) => Ok(Rc::new(Value::String(Rc::clone(s)))),
        Expression::CharacterLiteral(_, c) => Ok(Rc::new(Value::Char(*c))),
        Expression::IntegerLiteral(_, n) => Ok(Rc::new(Value::Int(*n))),
        Expression::FloatLiteral(_, f) => Ok(Rc::new(Value::Float(*f))),

        Expression::Call(loc, f, args) => eval_function_call(f, args, state, loc),

        Expression::ADTTypeConstructor(_, name, arguments) => {
            let mut evaluated_arguments = Vec::new();
            for e in arguments {
                evaluated_arguments.push(evaluate(e, state)?);
            }
            Ok(Rc::new(Value::ADTValue(name.clone(), evaluated_arguments)))
        }

        Expression::Record(_, _, field_expressions) => {
            let mut result = Vec::new();
            for (name, expression) in field_expressions.iter() {
                result.push((name.clone(), evaluate(expression, state)?));
            }
            Ok(Rc::new(Value::RecordValue(result)))
        }

        Expression::TupleLiteral(_, elements) => {
            let mut evaluated_elements = Vec::new();
            for e in elements {
                evaluated_elements.push(evaluate(e, state)?);
            }
            Ok(Rc::new(Value::Tuple(evaluated_elements)))
        }
        Expression::EmptyListLiteral(_) => Ok(Rc::new(Value::List(vec![]))),
        Expression::ShorthandListLiteral(_, elements) => {
            let mut evaluated_elements = Vec::new();
            for e in elements {
                evaluated_elements.push(evaluate(e, state)?);
            }
            Ok(Rc::new(Value::List(evaluated_elements)))
        }
        Expression::LonghandListLiteral(_, head, tail) => {
            let evaluated_head = evaluate(head, state)?;
            let evaluated_tail = evaluate(tail, state)?;

            let mut results = vec![evaluated_head];
            match evaluated_tail.borrow() {
                Value::List(values) => {
                    results.extend(
                        values
                            .iter()
                            .map(|v| Rc::clone(v))
                            .collect::<Vec<Rc<Value>>>(),
                    );
                    Ok(Rc::new(Value::List(results)))
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

        Expression::Variable(loc, v) => Ok(state.retrieve_variable_value(v, loc)),
        Expression::Negation(_, e) => Ok(Rc::new(Value::Bool(!eval_bool(e, state)?))),
        Expression::Minus(_, e) => Ok(Rc::new(Value::Int(-eval_int(e, state)?))),
        Expression::Times(_, e1, e2) => {
            match (evaluate(e1, state)?.borrow(), evaluate(e2, state)?.borrow()) {
                (Value::Int(x), Value::Int(y)) => Ok(Rc::new(Value::Int(*x * *y))),
                (Value::Int(x), Value::Float(y)) => Ok(Rc::new(Value::Float(*x as f64 * *y))),
                (Value::Float(x), Value::Int(y)) => Ok(Rc::new(Value::Float(*x * *y as f64))),
                (Value::Float(x), Value::Float(y)) => Ok(Rc::new(Value::Float(*x * *y))),
                _ => unreachable!(),
            }
        }
        Expression::Divide(_, e1, e2) => {
            let divider = evaluate(e2, state)?;
            if let Value::Int(0) = *divider {
                return Err(DivisionByZero);
            }
            match (evaluate(e1, state)?.borrow(), divider.borrow()) {
                (Value::Int(x), Value::Int(y)) => Ok(Rc::new(Value::Int(x / y))),
                (Value::Int(x), Value::Float(y)) => Ok(Rc::new(Value::Float(*x as f64 / *y))),
                (Value::Float(x), Value::Int(y)) => Ok(Rc::new(Value::Float(x / *y as f64))),
                (Value::Float(x), Value::Float(y)) => Ok(Rc::new(Value::Float(x / y))),
                _ => unreachable!(),
            }
        }
        Expression::Modulo(_, e1, e2) => Ok(Rc::new(Value::Int(
            eval_int(e1, state)? % eval_int(e2, state)?,
        ))),
        Expression::Add(_, e1, e2) => {
            match (evaluate(e1, state)?.borrow(), evaluate(e2, state)?.borrow()) {
                (Value::Int(x), Value::Int(y)) => Ok(Rc::new(Value::Int(x + y))),
                (Value::Int(x), Value::Float(y)) => Ok(Rc::new(Value::Float(*x as f64 + *y))),
                (Value::Float(x), Value::Int(y)) => Ok(Rc::new(Value::Float(x + *y as f64))),
                (Value::Float(x), Value::Float(y)) => Ok(Rc::new(Value::Float(x + y))),
                (Value::String(l), Value::String(r)) => {
                    let mut s = String::new();
                    s.push_str(&l.to_string());
                    s.push_str(&r.to_string());
                    Ok(Rc::new(Value::String(Rc::new(s))))
                }
                (l, r) => unreachable!("Addition between results {:?} and {:?}", l, r),
            }
        }
        Expression::Subtract(_, e1, e2) => {
            match (evaluate(e1, state)?.borrow(), evaluate(e2, state)?.borrow()) {
                (Value::Int(x), Value::Int(y)) => Ok(Rc::new(Value::Int(x - y))),
                (Value::Int(x), Value::Float(y)) => Ok(Rc::new(Value::Float(*x as f64 - *y))),
                (Value::Float(x), Value::Int(y)) => Ok(Rc::new(Value::Float(x - *y as f64))),
                (Value::Float(x), Value::Float(y)) => Ok(Rc::new(Value::Float(x - y))),
                _ => unreachable!(),
            }
        }
        Expression::ShiftLeft(_, e1, e2) => Ok(Rc::new(Value::Int(
            eval_int(e1, state)? << eval_int(e2, state)?,
        ))),

        Expression::ShiftRight(_, e1, e2) => Ok(Rc::new(Value::Int(
            eval_int(e1, state)? >> eval_int(e2, state)?,
        ))),

        Expression::Greater(_, e1, e2) => Ok(Rc::new(Value::Bool(
            eval_int(e1, state)? > eval_int(e2, state)?,
        ))),

        Expression::Greq(_, e1, e2) => Ok(Rc::new(Value::Bool(
            eval_int(e1, state)? >= eval_int(e2, state)?,
        ))),

        Expression::Leq(_, e1, e2) => Ok(Rc::new(Value::Bool(
            eval_int(e1, state)? <= eval_int(e2, state)?,
        ))),

        Expression::Lesser(_, e1, e2) => Ok(Rc::new(Value::Bool(
            eval_int(e1, state)? < eval_int(e2, state)?,
        ))),

        Expression::Eq(_, e1, e2) => Ok(Rc::new(Value::Bool(eq(
            evaluate(e1, state)?,
            evaluate(e2, state)?,
        )))),
        Expression::Neq(_, e1, e2) => Ok(Rc::new(Value::Bool(!eq(
            evaluate(e1, state)?,
            evaluate(e2, state)?,
        )))),
        Expression::And(_, e1, e2) => Ok(Rc::new(Value::Bool(
            eval_bool(e1, state)? && eval_bool(e2, state)?,
        ))),

        Expression::Or(_, e1, e2) => Ok(Rc::new(Value::Bool(
            eval_bool(e1, state)? || eval_bool(e2, state)?,
        ))),

        Expression::RecordFieldAccess(_, record_name, record_expression, field_accessor) => {
            let record_value = evaluate(record_expression, state)?;
            if let Value::RecordValue(fields) = record_value.borrow() {
                if let Expression::Variable(_, field) = &**field_accessor {
                    return Ok(fields
                        .into_iter()
                        .find(|(v, _)| v == field)
                        .unwrap()
                        .clone()
                        .1);
                }
            }
            unreachable!()
        }
        Expression::Lambda(loc, args, body) => {
            let lambda_body = FunctionBody {
                name: Rc::new("".to_string()),
                location: loc.clone(),
                match_expressions: args.clone(),
                rules: vec![Rc::new(FunctionRule::ExpressionRule(
                    loc.clone(),
                    body.clone(),
                ))],
                local_function_definitions: vec![],
                local_adt_definitions: vec![],
                local_record_definitions: vec![],
            };

            let closure = FunctionClosure {
                closed_variables: state.determine_closure(args, &body.references(true)),
                body: Rc::new(lambda_body),
            };
            Ok(Rc::new(Value::Lambda(Vec::new(), vec![Rc::new(closure)])))
        }
    }
}

fn eq(l: Rc<Value>, r: Rc<Value>) -> bool {
    match (l.borrow(), r.borrow()) {
        (Value::Bool(l), Value::Bool(r)) => l == r,
        (Value::Int(l), Value::Int(r)) => l == r,
        (Value::Float(l), Value::Float(r)) => l == r,
        (Value::Char(l), Value::Char(r)) => l == r,
        (Value::String(l), Value::String(r)) => l == r,
        (Value::Tuple(l), Value::Tuple(r)) => l
            .into_iter()
            .zip(r)
            .fold(true, |b, (l, r)| b && eq(Rc::clone(l), Rc::clone(r))),

        (Value::List(l), Value::List(r)) => l
            .into_iter()
            .zip(r)
            .fold(true, |b, (l, r)| b && eq(Rc::clone(l), Rc::clone(r))),

        (
            Value::ADTValue(l_constructor, l_arguments),
            Value::ADTValue(r_constructor, r_arguments),
        ) => {
            l_constructor == r_constructor
                && l_arguments
                    .into_iter()
                    .zip(r_arguments)
                    .fold(true, |b, (l, r)| b && eq(Rc::clone(l), Rc::clone(r)))
        }

        (Value::RecordValue(l_values), Value::RecordValue(r_values)) => l_values
            .into_iter()
            .map(|(_, value)| Rc::clone(value))
            .zip(r_values.into_iter().map(|(_, value)| Rc::clone(value)))
            .all(|(l, r)| eq(l, r)),

        (l, r) => unreachable!("eq {} and {}", l, r),
    }
}

fn eval_function_call(
    f: &Rc<String>,
    args: &Vec<Rc<Expression>>,
    state: &mut RunState,
    loc: &Location,
) -> Result<Rc<Value>, InterpreterError> {
    let r = match state.get_function_definition(f) {
        Some(d) => eval_declared_function(&d, args, state),
        None => eval_lambda(f, state.retrieve_variable_value(f, loc), args, state),
    };
    r
}

fn eval_lambda(
    f: &Rc<String>,
    lambda: Rc<Value>,
    args: &Vec<Rc<Expression>>,
    state: &mut RunState,
) -> Result<Rc<Value>, InterpreterError> {
    let (curried_argument_values, closures) = match lambda.borrow() {
        Value::Lambda(curried_argument_values, closures) => (curried_argument_values, closures),
        v => unreachable!("{}", v),
    };

    if curried_argument_values.len() + args.len()
        < closures.get(0).unwrap().body.match_expressions.len()
    {
        // Handle currying
        let mut argument_values: Vec<Rc<Value>> = Vec::new();
        for a in args {
            argument_values.push(evaluate(a, state)?);
        }

        let mut all_argument_values: Vec<Rc<Value>> = Vec::new();
        all_argument_values.extend(
            curried_argument_values
                .iter()
                .map(|v| Rc::clone(v))
                .collect::<Vec<Rc<Value>>>(),
        );
        all_argument_values.extend(argument_values);
        return Ok(Rc::new(Value::Lambda(
            all_argument_values,
            closures.iter().map(|c| Rc::clone(c)).collect(),
        )));
    }

    let mut all_args: Vec<Rc<Value>> = Vec::new();
    all_args.extend(
        curried_argument_values
            .iter()
            .map(Rc::clone)
            .collect::<Vec<Rc<Value>>>(),
    );

    for a in args {
        all_args.push(evaluate(a, state)?);
    }

    eval_function_closures(f, closures, &all_args, state)
}

fn eval_function_closures(
    f: &Rc<String>,
    bodies: &Vec<Rc<FunctionClosure>>,
    args: &Vec<Rc<Value>>,
    state: &mut RunState,
) -> Result<Rc<Value>, InterpreterError> {
    for closure in bodies {
        let mut body_frame = Frame::new();

        let mut matches = true;
        for (match_expression, value) in closure.body.match_expressions.iter().zip(args.iter()) {
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
            for function_definition in closure.body.local_function_definitions.iter() {
                body_frame.declared_functions.insert(
                    function_definition.name.clone(),
                    Rc::clone(function_definition),
                );
            }

            for (v, value) in &closure.closed_variables {
                body_frame.variables.insert(v.clone(), Rc::clone(value));
            }

            state.frames.push(body_frame);

            let result = eval_function_body(&f, &closure.body, state);

            state.frames.pop();
            return result;
        }
    }
    Err(NoApplicableFunctionBody(Rc::clone(f)))
}

fn eval_declared_function(
    d: &FunctionDefinition,
    args: &Vec<Rc<Expression>>,
    state: &mut RunState,
) -> Result<Rc<Value>, InterpreterError> {
    // Inferencer ensures all bodies have the same number of arguments, so we just use the first.
    if d.function_bodies.get(0).unwrap().match_expressions.len() > args.len() {
        // Handle currying
        let mut argument_values = Vec::new();
        for a in args {
            argument_values.push(evaluate(a, state)?);
        }

        let closures = d
            .function_bodies
            .iter()
            .map(|fb| {
                Rc::new(FunctionClosure {
                    closed_variables: body_references(fb, true)
                        .iter()
                        .map(|(v, loc)| (v.clone(), state.retrieve_variable_value(v, loc)))
                        .collect(),
                    body: fb.clone(),
                })
            })
            .collect();

        return Ok(Rc::new(Value::Lambda(argument_values, closures)));
    }

    let mut arg_values = Vec::new();
    for a in args {
        arg_values.push(evaluate(a, state)?);
    }

    let closures = d
        .function_bodies
        .iter()
        .map(|b| {
            Rc::new(FunctionClosure {
                closed_variables: HashMap::new(),
                body: b.clone(),
            })
        })
        .collect();
    eval_function_closures(&d.name, &closures, &arg_values, state)
}

fn eval_function_body(
    name: &Rc<String>,
    body: &FunctionBody,
    state: &mut RunState,
) -> Result<Rc<Value>, InterpreterError> {
    for rule in &body.rules {
        match rule.borrow() {
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

    Err(InterpreterError::NoApplicableFunctionRule(Rc::clone(name)))
}

fn collect_match_variables(
    match_expression: &Rc<MatchExpression>,
    evaluated_expression: &Rc<Value>,
) -> Result<HashMap<Rc<String>, Rc<Value>>, InterpreterError> {
    match (match_expression.borrow(), evaluated_expression.borrow()) {
        (MatchExpression::Identifier(_loc_info, identifier), _) => {
            let mut map = HashMap::new();
            map.insert(Rc::clone(identifier), Rc::clone(evaluated_expression));
            Ok(map)
        }
        (MatchExpression::IntLiteral(loc_info, _n), Value::Int(n)) => {
            if _n == n {
                return Ok(HashMap::new());
            }
            Err(InterpreterError::ExpressionDoesNotMatch(
                MatchExpression::IntLiteral(loc_info.clone(), _n.clone()),
                Rc::clone(evaluated_expression),
            ))
        }
        (MatchExpression::CharLiteral(loc_info, _c), Value::Char(c)) => {
            if _c == c {
                return Ok(HashMap::new());
            }
            Err(InterpreterError::ExpressionDoesNotMatch(
                MatchExpression::CharLiteral(loc_info.clone(), _c.clone()),
                Rc::clone(evaluated_expression),
            ))
        }
        (MatchExpression::StringLiteral(loc_info, _s), Value::String(s)) => {
            if _s == s {
                return Ok(HashMap::new());
            }
            Err(InterpreterError::ExpressionDoesNotMatch(
                MatchExpression::StringLiteral(loc_info.clone(), _s.clone()),
                Rc::clone(evaluated_expression),
            ))
        }
        (MatchExpression::BoolLiteral(loc_info, _b), Value::Bool(b)) => {
            if _b == b {
                return Ok(HashMap::new());
            }
            Err(InterpreterError::ExpressionDoesNotMatch(
                MatchExpression::BoolLiteral(loc_info.clone(), _b.clone()),
                Rc::clone(evaluated_expression),
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
                    Rc::clone(evaluated_expression),
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
                    Rc::clone(evaluated_expression),
                ));
            }

            let mut head_variables = collect_match_variables(&head, values.iter().next().unwrap())?;
            let tail_variables = collect_match_variables(
                &tail,
                &Rc::new(Value::List(values.iter().skip(1).map(Rc::clone).collect())),
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
                    Rc::clone(evaluated_expression),
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
                .map(|field| {
                    (
                        field.clone(),
                        field_to_value
                            .iter()
                            .find(|(v, _)| v == field)
                            .unwrap()
                            .1
                            .clone(),
                    )
                })
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
    match evaluate(e, state)?.borrow() {
        Value::Bool(b) => Ok(b.clone()),
        _ => unreachable!("evaluate wrong type (expected bool)"),
    }
}

fn eval_int(e: &Expression, state: &mut RunState) -> Result<isize, InterpreterError> {
    match evaluate(e, state)?.borrow() {
        Value::Int(n) => Ok(n.clone()),
        e => unreachable!("evaluate wrong type (expected int): {:?}", e),
    }
}

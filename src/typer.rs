use std::collections::HashMap;
use std::fmt::{Display, Error, Formatter};

use crate::parser::{AST, Expression, FunctionBody, FunctionDeclaration, FunctionRule, FunctionType, LocationInformation, Type};
use crate::parser::FunctionRule::{ConditionalRule, ExpressionRule};
use crate::parser::Type::Bool;
use crate::typer::TypeErrorType::{ArgumentCountMismatch, ParameterCountMismatch, TypeMismatch, UndefinedFunction, UndefinedVariable};

#[derive(Debug)]
pub struct TypeError {
    context: ErrorContext,
    err: TypeErrorType,
}

impl TypeError {
    fn from(context: ErrorContext, err: TypeErrorType) -> TypeError {
        TypeError { context, err }
    }
}

#[derive(Debug)]
pub enum TypeErrorType {
    ParameterCountMismatch(usize, usize),
    ArgumentCountMismatch(String, usize, usize),
    UndefinedVariable(String),
    UndefinedFunction(String),
    TypeMismatch(Type, Type),
}

#[derive(Debug)]
struct ErrorContext {
    file: String,
    function: String,
    line: usize,
    col: usize,
}

impl Display for TypeError {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        write_error_context(f, &self.context)?;
        match &self.err {
            ParameterCountMismatch(expected, got) => write!(f, "Exptected {} parameters from type, found {} parameters in body", expected, got),
            ArgumentCountMismatch(function, expected, got) => write!(f, "Expected {} arguments to call {}, got {}", expected, function, got),
            TypeMismatch(expected, got) => write!(f, "Exptected type {:?}, got {:?}", expected, got),
            UndefinedVariable(name) => write!(f, "Undefined variable {}", name),
            UndefinedFunction(name) => write!(f, "Undefined function {}", name),
        }
    }
}

fn write_error_context(f: &mut Formatter<'_>, context: &ErrorContext) -> Result<(), Error> {
    write!(f, "[{}]/{} [{}:{}]: ", context.file, context.function, context.line, context.col)
}

#[derive(Debug)]
pub struct TypeResult {}

struct TyperState {
    ast: Box<AST>,
    function_name_to_type: HashMap<String, FunctionType>,
}

pub fn _type(ast: Box<AST>) -> Result<TypeResult, Vec<TypeError>> {
    TyperState::new(ast).check_types()
}

pub fn build_function_type_cache(ast: Box<AST>) -> HashMap<String, FunctionType> {
    ast.function_declarations.iter()
        .map(|(n, d)| (n.clone(), d.function_type.clone()))
        .collect()
}

impl TyperState {
    fn new(ast: Box<AST>) -> TyperState {
        return TyperState { ast: ast.clone(), function_name_to_type: build_function_type_cache(ast.clone()) };
    }

    fn check_types(&self) -> Result<TypeResult, Vec<TypeError>> {
        let errors: Vec<TypeError> = self.ast.function_declarations.iter()
            .map(|(_, d)| self.check_function_declaration(d))
            .filter(|r| r.is_err())
            .flat_map(|err| err.err().unwrap().into_iter())
            .collect();

        if errors.len() > 0 {
            Err(errors)
        } else {
            Ok(TypeResult {})
        }
    }

    fn check_function_declaration(&self, decl: &FunctionDeclaration) -> Result<TypeResult, Vec<TypeError>> {
        let errors: Vec<TypeError> = (&decl.function_bodies).into_iter()
            .map(|b| self.check_function_body(&decl.name, b))
            .filter(|r| r.is_err())
            .flat_map(|err| err.err().unwrap().into_iter())
            .collect();

        if errors.len() > 0 {
            Err(errors)
        } else { Ok(TypeResult {}) }
    }

    fn check_function_body(&self, name: &String, body: &FunctionBody) -> Result<TypeResult, Vec<TypeError>> {
        let function_type = &self.function_name_to_type[name];

        if function_type.from.len() != body.parameters.len() {
            return Err(vec![TypeError::from(ErrorContext { file: "NotImplemented".to_string(), function: name.to_string(), line: 0, col: 0 }, ParameterCountMismatch(function_type.from.len(), body.parameters.len()))]);
        }
        let parameter_to_type: HashMap<&String, Type> = (&body.parameters).into_iter().enumerate()
            .map(|(i, name)| (name, function_type.from[i].clone()))
            .collect();

        let errors: Vec<TypeError> = (&body.rules).into_iter()
            .map(|r| self.check_function_rule(name, &function_type.clone().to, &parameter_to_type, r))
            .filter(|r| r.is_err())
            .flat_map(|err| err.err().unwrap().into_iter())
            .collect();

        if errors.len() > 0 {
            Err(errors)
        } else {
            Ok(TypeResult {})
        }
    }

    fn check_function_rule(&self, function_name: &String, result_type: &Type, parameter_to_type: &HashMap<&String, Type>, rule: &FunctionRule) -> Result<TypeResult, Vec<TypeError>> {
        print!("check function rule {} ", function_name);
        match rule {
            ConditionalRule(locInfo, condition, expression) => {
                let e1r = self.check_expression(&locInfo.file, function_name, condition, Type::Bool, parameter_to_type);
                let e2r = self.check_expression(&locInfo.file, function_name, expression, result_type.clone(), parameter_to_type);
                match (e1r, e2r) {
                    (Ok(_), Ok(_)) => Ok(TypeResult {}),
                    (Err(e1), Err(e2)) => Err(e1.into_iter().chain(e2).collect()),
                    (Err(e1), _) => Err(e1),
                    (_, Err(e2)) => Err(e2),
                }
            }
            ExpressionRule(locInfo, e) => self.check_expression(&locInfo.file, function_name, e, result_type.clone(), parameter_to_type).map(|e| TypeResult {}),
        }
    }

    fn check_expression(&self, file_name: &String, function_name: &String, expression: &Expression, required_type: Type, parameter_to_type: &HashMap<&String, Type>) -> Result<Type, Vec<TypeError>> {
        println!("checking expression {:?}", expression);
        let combine = |result_type: Type, er1: Result<Type, Vec<TypeError>>, er2: Result<Type, Vec<TypeError>>| match (er1, er2) {
            (Ok(_), Ok(_)) => Ok(result_type),
            (Err(ers1), Err(ers2)) => Err(ers1.into_iter().chain(ers2).collect()),
            (Err(ers1), _) => Err(ers1),
            (_, Err(ers2)) => Err(ers2)
        };

        let determined_type: Result<Type, Vec<TypeError>> = match expression {
            Expression::BoolLiteral(l) => Ok(Type::Bool),
            Expression::StringLiteral(s) => Ok(Type::String),
            Expression::CharacterLiteral(c) => Ok(Type::Char),
            Expression::Number(n) => Ok(Type::Int),
            Expression::Call(f, args) => self.check_function_call(&f, &args, required_type.clone(), parameter_to_type, function_name, file_name),
            Expression::Variable(v) => {
                match parameter_to_type.get(v) {
                    Some(_type) => Ok(_type.clone()),
                    None => Err(vec![TypeError::from(ErrorContext { file: file_name.clone(), function: function_name.clone(), line: 0, col: 0 }, TypeErrorType::UndefinedVariable(v.clone()))]),
                }
            }
            Expression::Negation(e) => self.check_expression(function_name, file_name, e, Type::Bool, parameter_to_type),
            Expression::Minus(n) => self.check_expression(function_name, file_name, n, Type::Int, parameter_to_type),
            Expression::Times(e1, e2) =>
                combine(Type::Int, self.check_expression(function_name, file_name, e1, Type::Int, parameter_to_type), self.check_expression(function_name, file_name, e2, Type::Int, parameter_to_type)),
            Expression::Divide(e1, e2) =>
                combine(Type::Int, self.check_expression(function_name, file_name, e1, Type::Int, parameter_to_type), self.check_expression(function_name, file_name, e2, Type::Int, parameter_to_type)),
            Expression::Modulo(e1, e2) =>
                combine(Type::Int, self.check_expression(function_name, file_name, e1, Type::Int, parameter_to_type), self.check_expression(function_name, file_name, e2, Type::Int, parameter_to_type)),
            Expression::Add(e1, e2) =>
                combine(Type::Int, self.check_expression(function_name, file_name, e1, Type::Int, parameter_to_type), self.check_expression(function_name, file_name, e2, Type::Int, parameter_to_type)),
            Expression::Substract(e1, e2) =>
                combine(Type::Int, self.check_expression(function_name, file_name, e1, Type::Int, parameter_to_type), self.check_expression(function_name, file_name, e2, Type::Int, parameter_to_type)),
            Expression::ShiftLeft(e1, e2) =>
                combine(Type::Int, self.check_expression(function_name, file_name, e1, Type::Int, parameter_to_type), self.check_expression(function_name, file_name, e2, Type::Int, parameter_to_type)),
            Expression::ShiftRight(e1, e2) =>
                combine(Type::Int, self.check_expression(function_name, file_name, e1, Type::Int, parameter_to_type), self.check_expression(function_name, file_name, e2, Type::Int, parameter_to_type)),
            Expression::Greater(e1, e2) =>
                combine(Type::Bool, self.check_expression(function_name, file_name, e1, Type::Int, parameter_to_type), self.check_expression(function_name, file_name, e2, Type::Int, parameter_to_type)),
            Expression::Greq(e1, e2) =>
                combine(Type::Bool, self.check_expression(function_name, file_name, e1, Type::Int, parameter_to_type), self.check_expression(function_name, file_name, e2, Type::Int, parameter_to_type)),
            Expression::Leq(e1, e2) =>
                combine(Type::Bool, self.check_expression(function_name, file_name, e1, Type::Int, parameter_to_type), self.check_expression(function_name, file_name, e2, Type::Int, parameter_to_type)),
            Expression::Lesser(e1, e2) =>
                combine(Type::Bool, self.check_expression(function_name, file_name, e1, Type::Int, parameter_to_type), self.check_expression(function_name, file_name, e2, Type::Int, parameter_to_type)),
            Expression::Eq(e1, e2) =>
                combine(Type::Bool, self.check_expression(function_name, file_name, e1, Type::Int, parameter_to_type), self.check_expression(function_name, file_name, e2, Type::Int, parameter_to_type)),
            Expression::Neq(e1, e2) =>
                combine(Type::Bool, self.check_expression(function_name, file_name, e1, Type::Int, parameter_to_type), self.check_expression(function_name, file_name, e2, Type::Int, parameter_to_type)),
            Expression::And(e1, e2) =>
                combine(Type::Bool, self.check_expression(function_name, file_name, e1, Type::Bool, parameter_to_type), self.check_expression(function_name, file_name, e2, Type::Bool, parameter_to_type)),
            Expression::Or(e1, e2) =>
                combine(Type::Bool, self.check_expression(function_name, file_name, e1, Type::Bool, parameter_to_type), self.check_expression(function_name, file_name, e2, Type::Bool, parameter_to_type))
        };

        if let Err(r) = determined_type {
            println!("error in subexpr: {:?}", r);
            return Err(r);
        }

        let determined_type = determined_type.ok().unwrap();
        if determined_type != required_type {
            println!("determined type error: {:?}, required: {:?}", determined_type, required_type);
            return Err(vec![TypeError::from(ErrorContext { file: file_name.clone(), function: function_name.clone(), line: 0, col: 0 }, TypeMismatch(required_type.clone(), determined_type))]);
        }

        Ok(determined_type)
    }

    fn check_function_call(&self, name: &String, args: &Vec<Expression>, required_type: Type, parameter_to_type: &HashMap<&String, Type>, file_name: &String, function_name: &String) -> Result<Type, Vec<TypeError>> {
        println!("checking call {}", name);
        let ftype = self.function_name_to_type.get(name);
        if let None = ftype {
            return Err(vec![TypeError::from(ErrorContext { file: file_name.clone(), function: function_name.clone(), line: 0, col: 0 }, UndefinedFunction(name.clone()))]);
        }

        let ftype = ftype.unwrap();

        if ftype.from.len() != args.len() {
            return Err(vec![TypeError::from(ErrorContext { file: file_name.clone(), function: function_name.clone(), line: 0, col: 0 }, ArgumentCountMismatch(name.clone(), ftype.from.len(), args.len()))]);
        }

        let errors : Vec<TypeError> = ftype.clone().from.into_iter().zip(args.into_iter())
            .map(|(atype, e)| self.check_expression(file_name, function_name, e, atype, parameter_to_type))
            .filter(|r| r.is_err())
            .flat_map(|r| r.err().unwrap())
            .collect();

        if errors.len() > 0 {
            return Err(errors);
        }
        Ok(ftype.clone().to)
    }
}
use std::collections::HashMap;
use std::fmt::{Display, Error, Formatter};

use crate::parser::{AST, Expression, FunctionBody, FunctionDeclaration, FunctionRule, FunctionType, Location, Type};
use crate::parser::FunctionRule::{ConditionalRule, ExpressionRule};
use crate::typer::TypeErrorType::{ArgumentCountMismatch, OperatorArgumentsNotEqual, ParameterCountMismatch, TypeMismatch, UndefinedFunction, UndefinedVariable};

#[derive(Debug)]
pub struct TypeError {
    context: ErrorContext,
    err: TypeErrorType,
}

impl TypeError {
    fn from(context: ErrorContext, err: TypeErrorType) -> TypeError {
        TypeError { context, err }
    }

    fn from_loc(loc: Location, err: TypeErrorType) -> TypeError {
        TypeError {
            context: ErrorContext {
                file: loc.file.clone(),
                function: loc.function.clone(),
                line: loc.line,
                col: loc.col,
            },
            err,
        }
    }
}

#[derive(Debug)]
pub enum TypeErrorType {
    ParameterCountMismatch(usize, usize),
    ArgumentCountMismatch(String, usize, usize),
    UndefinedVariable(String),
    UndefinedFunction(String),
    TypeMismatch(Vec<Type>, Type),
    OperatorArgumentsNotEqual(String, Type, Type),
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
            ParameterCountMismatch(expected, got) => write!(f, "Expected {} parameters from type, found {} parameters in body", expected, got),
            ArgumentCountMismatch(function, expected, got) => write!(f, "Expected {} arguments to call {}, got {}", expected, function, got),
            TypeMismatch(expected, got) => write!(f, "Expected type {:?}, got {:?}", expected, got),
            UndefinedVariable(name) => write!(f, "Undefined variable {}", name),
            UndefinedFunction(name) => write!(f, "Undefined function {}", name),
            OperatorArgumentsNotEqual(o, l, r) => write!(f, "Arguments to {} operator do not have equal type: {:?} and {:?}", o, l, r)
        }
    }
}

fn write_error_context(f: &mut Formatter<'_>, context: &ErrorContext) -> Result<(), Error> {
    write!(f, "{}/{} [{}:{}]: ", context.file, context.function, context.line, context.col)
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

fn combine(type_transformer: impl FnOnce(Type, Type) -> Result<Type, TypeError>, er1: Result<Type, Vec<TypeError>>, er2: Result<Type, Vec<TypeError>>) -> Result<Type, Vec<TypeError>> {
    match (er1, er2) {
        (Ok(lt), Ok(rt)) => type_transformer(lt, rt).map_err(|e| vec![e]),
        (Err(ers1), Err(ers2)) => Err(ers1.into_iter().chain(ers2).collect()),
        (Err(ers1), _) => Err(ers1),
        (_, Err(ers2)) => Err(ers2)
    }
}

impl TyperState {
    fn new(ast: Box<AST>) -> TyperState {
        return TyperState { ast: ast.clone(), function_name_to_type: build_function_type_cache(ast.clone()) };
    }

    fn check_types(&self) -> Result<TypeResult, Vec<TypeError>> {
        let mut errors: Vec<TypeError> = self.ast.function_declarations.iter()
            .map(|(_, d)| self.check_function_declaration(d))
            .filter(|r| r.is_err())
            .flat_map(|err| err.err().unwrap().into_iter())
            .collect();

        let res = self.check_expression(&self.ast.main, &Vec::new(), &HashMap::new());
        if let Err(mut e) = res {
            errors.append(&mut e);
        }

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
            .map(|r| self.check_function_rule(&function_type.clone().to, &parameter_to_type, r))
            .filter(|r| r.is_err())
            .flat_map(|err| err.err().unwrap().into_iter())
            .collect();

        if errors.len() > 0 {
            Err(errors)
        } else {
            Ok(TypeResult {})
        }
    }

    fn check_function_rule(&self, result_type: &Type, parameter_to_type: &HashMap<&String, Type>, rule: &FunctionRule) -> Result<TypeResult, Vec<TypeError>> {
        // print!("check function rule {} ", function_name);
        match rule {
            ConditionalRule(_, condition, expression) => {
                let e1r = self.check_expression(condition, &vec![Type::Bool], parameter_to_type);
                let e2r = self.check_expression(expression, &vec![result_type.clone()], parameter_to_type);
                match (e1r, e2r) {
                    (Ok(_), Ok(_)) => Ok(TypeResult {}),
                    (Err(e1), Err(e2)) => Err(e1.into_iter().chain(e2).collect()),
                    (Err(e1), _) => Err(e1),
                    (_, Err(e2)) => Err(e2),
                }
            }
            ExpressionRule(_, e) => self.check_expression(e, &vec![result_type.clone()], parameter_to_type).map(|_| TypeResult {}),
        }
    }

    fn check_expression(&self, expression: &Expression, required_type: &Vec<Type>, parameter_to_type: &HashMap<&String, Type>) -> Result<Type, Vec<TypeError>> {
        // println!("checking expression {:?}", expression);

        let type_equal = |operator, loc| |l, r| {
            return if l == r { Ok(l) } else { Err(TypeError::from_loc(loc, OperatorArgumentsNotEqual(operator, l, r))) };
        };
        let type_fixed = |t| (|_l, _r| Ok(t));

        let (determined_type, loc_info): (Result<Type, Vec<TypeError>>, &Location) = match expression {
            Expression::BoolLiteral(loc_info, _) => (Ok(Type::Bool), loc_info),
            Expression::StringLiteral(loc_info, _) => (Ok(Type::String), loc_info),
            Expression::CharacterLiteral(loc_info, _) => (Ok(Type::Char), loc_info),
            Expression::Number(loc_info, _) => (Ok(Type::Int), loc_info),
            Expression::Call(loc_info, f, args) => (self.check_function_call(&f, &args, required_type, parameter_to_type, loc_info), loc_info),
            Expression::Variable(loc_info, v) => {
                (match parameter_to_type.get(v) {
                    Some(_type) => Ok(_type.clone()),
                    None => Err(vec![TypeError::from(ErrorContext { file: loc_info.file.clone(), function: loc_info.function.clone(), line: loc_info.line, col: loc_info.col }, TypeErrorType::UndefinedVariable(v.clone()))]),
                }, loc_info)
            }
            Expression::Negation(loc_info, e) => (self.check_expression(e, &vec![Type::Bool], parameter_to_type), loc_info),
            Expression::Minus(loc_info, n) => (self.check_expression(n, &vec![Type::Int], parameter_to_type), loc_info),
            Expression::Times(loc_info, e1, e2) =>
                (combine(type_fixed(Type::Int), self.check_expression(e1, &vec![Type::Int], parameter_to_type), self.check_expression(e2, &vec![Type::Int], parameter_to_type)), loc_info),
            Expression::Divide(loc_info, e1, e2) =>
                (combine(type_fixed(Type::Int), self.check_expression(e1, &vec![Type::Int], parameter_to_type), self.check_expression(e2, &vec![Type::Int], parameter_to_type)), loc_info),
            Expression::Modulo(loc_info, e1, e2) =>
                (combine(type_fixed(Type::Int), self.check_expression(e1, &vec![Type::Int], parameter_to_type), self.check_expression(e2, &vec![Type::Int], parameter_to_type)), loc_info),

            Expression::Add(loc_info, e1, e2) =>
                (combine(type_equal("+".to_string(), loc_info.clone()), self.check_expression(e1, &vec![Type::Int, Type::String], parameter_to_type), self.check_expression(e2, &vec![Type::Int, Type::String], parameter_to_type)), loc_info),

            Expression::Subtract(loc_info, e1, e2) =>
                (combine(type_fixed(Type::Int), self.check_expression(e1, &vec![Type::Int], parameter_to_type), self.check_expression(e2, &vec![Type::Int], parameter_to_type)), loc_info),
            Expression::ShiftLeft(loc_info, e1, e2) =>
                (combine(type_fixed(Type::Int), self.check_expression(e1, &vec![Type::Int], parameter_to_type), self.check_expression(e2, &vec![Type::Int], parameter_to_type)), loc_info),
            Expression::ShiftRight(loc_info, e1, e2) =>
                (combine(type_fixed(Type::Int), self.check_expression(e1, &vec![Type::Int], parameter_to_type), self.check_expression(e2, &vec![Type::Int], parameter_to_type)), loc_info),
            Expression::Greater(loc_info, e1, e2) =>
                (combine(type_fixed(Type::Bool), self.check_expression(e1, &vec![Type::Int], parameter_to_type), self.check_expression(e2, &vec![Type::Int], parameter_to_type)), loc_info),
            Expression::Greq(loc_info, e1, e2) =>
                (combine(type_fixed(Type::Bool), self.check_expression(e1, &vec![Type::Int], parameter_to_type), self.check_expression(e2, &vec![Type::Int], parameter_to_type)), loc_info),
            Expression::Leq(loc_info, e1, e2) =>
                (combine(type_fixed(Type::Bool), self.check_expression(e1, &vec![Type::Int], parameter_to_type), self.check_expression(e2, &vec![Type::Int], parameter_to_type)), loc_info),
            Expression::Lesser(loc_info, e1, e2) =>
                (combine(type_fixed(Type::Bool), self.check_expression(e1, &vec![Type::Int], parameter_to_type), self.check_expression(e2, &vec![Type::Int], parameter_to_type)), loc_info),
            Expression::Eq(loc_info, e1, e2) =>
                (combine(type_fixed(Type::Bool), self.check_expression(e1, &vec![], parameter_to_type), self.check_expression(e2, &vec![], parameter_to_type)), loc_info),
            Expression::Neq(loc_info, e1, e2) =>
                (combine(type_fixed(Type::Bool), self.check_expression(e1, &vec![], parameter_to_type), self.check_expression(e2, &vec![], parameter_to_type)), loc_info),
            Expression::And(loc_info, e1, e2) =>
                (combine(type_fixed(Type::Bool), self.check_expression(e1, &vec![Type::Bool], parameter_to_type), self.check_expression(e2, &vec![Type::Bool], parameter_to_type)), loc_info),
            Expression::Or(loc_info, e1, e2) =>
                (combine(type_fixed(Type::Bool), self.check_expression(e1, &vec![Type::Bool], parameter_to_type), self.check_expression(e2, &vec![Type::Bool], parameter_to_type)), loc_info),
        };

        if let Err(r) = determined_type {
            // println!("error in subexpr: {:?}", r);
            return Err(r);
        }

        let determined_type = determined_type.ok().unwrap();
        if required_type.is_empty() {
            return Ok(determined_type);
        }
        if !required_type.contains(&determined_type) {
            //println!("determined type error: {:?}, required: {:?}", determined_type, required_type);
            return Err(vec![TypeError::from(ErrorContext { file: loc_info.file.clone(), function: loc_info.function.clone(), line: loc_info.line, col: loc_info.col }, TypeMismatch(required_type.clone(), determined_type))]);
        }

        Ok(determined_type)
    }

    fn check_function_call(&self, name: &String, args: &Vec<Expression>, required_type: &Vec<Type>, parameter_to_type: &HashMap<&String, Type>, loc_info: &Location) -> Result<Type, Vec<TypeError>> {
        //println!("checking call {}", name);
        let ftype = self.function_name_to_type.get(name);
        if let None = ftype {
            return Err(vec![TypeError::from(ErrorContext { file: loc_info.file.clone(), function: loc_info.function.clone(), line: loc_info.line, col: loc_info.col }, UndefinedFunction(name.clone()))]);
        }

        let ftype = ftype.unwrap();

        if ftype.from.len() != args.len() {
            return Err(vec![TypeError::from(ErrorContext { file: loc_info.file.clone(), function: loc_info.function.clone(), line: loc_info.line, col: loc_info.col }, ArgumentCountMismatch(name.clone(), ftype.from.len(), args.len()))]);
        }

        let errors: Vec<TypeError> = ftype.clone().from.into_iter().zip(args.into_iter())
            .map(|(atype, e)| self.check_expression(e, &vec![atype], parameter_to_type))
            .filter(|r| r.is_err())
            .flat_map(|r| r.err().unwrap())
            .collect();

        if errors.len() > 0 {
            return Err(errors);
        }

        if required_type.is_empty() || required_type.contains(&ftype.clone().to) {
            return Ok(ftype.clone().to);
        }
        Err(vec![TypeError::from(ErrorContext { file: loc_info.file.clone(), function: loc_info.function.clone(), line: loc_info.line, col: loc_info.col }, TypeMismatch(required_type.clone(), ftype.clone().to))])
    }
}
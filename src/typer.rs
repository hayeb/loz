use std::collections::{HashMap};
use std::fmt::{Display, Error, Formatter};
use std::iter;

use crate::parser::{ADTDefinition, AST, CustomType, Expression, FunctionBody, FunctionDeclaration, FunctionRule, Location, MatchExpression, RecordDefinition, Type, TypeScheme};
use crate::parser::FunctionRule::{ConditionalRule, ExpressionRule, LetRule};
use crate::typer::TypeErrorType::{DuplicateVariableNameSingleMatchExpression, FunctionCallArgumentCountMismatch, MatchWrongType, OperatorArgumentsNotEqual, ParameterCountMismatch, TypeConstructorArgumentCountMismatch, TypeMismatch, UndefinedFunction, UndefinedRecordField, UndefinedTypeConstructor, UndefinedVariable, FunctionMultiplyDefined, TypeMultiplyDefined, TypeConstructorMultiplyDefined};

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
    FunctionCallArgumentCountMismatch(String, usize, usize),
    TypeConstructorArgumentCountMismatch(String, usize, usize),
    UndefinedVariable(String),
    UndefinedFunction(String),
    UndefinedTypeConstructor(String),
    TypeMismatch(Vec<Type>, Type),
    OperatorArgumentsNotEqual(String, Type, Type),
    MatchWrongType(Type),
    DuplicateVariableNameSingleMatchExpression(String),
    UndefinedRecordField(String, String),
    FunctionMultiplyDefined(String, Location),
    TypeMultiplyDefined(String, Location),
    TypeConstructorMultiplyDefined(String, String, Location)
}
#[derive(Debug)]
pub struct TypedAST {
    pub function_name_to_declaration: HashMap<String, FunctionDeclaration>,
    pub adt_type_constructor_to_type: HashMap<String, ADTDefinition>,
    pub record_name_to_definition: HashMap<String, RecordDefinition>,
    pub main: Expression
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
            FunctionCallArgumentCountMismatch(function, expected, got) => write!(f, "Expected {} arguments to call {}, got {}", expected, function, got),
            TypeConstructorArgumentCountMismatch(constructor, expected, got) => write!(f, "Expected {} arguments to constructor {}, got {}", expected, constructor, got),
            TypeMismatch(expected, got) => {
                if expected.len() == 1 {
                    write!(f, "Expected type '{}', got '{}'", expected.get(0).unwrap(), got)
                } else {
                    write!(f, "Expected one of type {}, got '{}'", expected.iter().map(|t| t.to_string()).collect::<Vec<String>>().join(", "), got)
                }
            }
            UndefinedVariable(name) => write!(f, "Undefined variable '{}'", name),
            UndefinedFunction(name) => write!(f, "Undefined function '{}'", name),
            UndefinedTypeConstructor(name) => write!(f, "Undefined type constructor: '{}'", name),
            OperatorArgumentsNotEqual(o, l, r) => write!(f, "Arguments to '{}' operator do not have equal type: '{}' and '{}'", o, l, r),
            MatchWrongType(expected_type) => write!(f, "Match expression has wrong type, expected type '{}'", expected_type),
            DuplicateVariableNameSingleMatchExpression(v) => write!(f, "Duplicate variable introduced in single match: '{}'", v),
            UndefinedRecordField(record_name, field_name) => write!(f, "Undefined record field '{}' in record '{}'", field_name, record_name),
            FunctionMultiplyDefined(name, location) => write!(f, "Function {} already defined, encountered earlier at {}", name, location),
            TypeMultiplyDefined(name, location) => write!(f, "Type {} already defined, encountered earlier at {}", name, location),
            TypeConstructorMultiplyDefined(constructor_name, defined_in_type, defined_in_location) => write!(f, "Type constructor {} already defined in type {} at {}", constructor_name, defined_in_type, defined_in_location)
        }
    }
}

fn write_error_context(f: &mut Formatter<'_>, context: &ErrorContext) -> Result<(), Error> {
    write!(f, "{}::{}[{}:{}]: ", context.file, context.function, context.line, context.col)
}

#[derive(Debug)]
pub struct TypeResult {}

struct TyperState<'a> {
    ast: &'a AST,
    function_name_to_type: HashMap<String, TypeScheme>,
    adt_type_constructor_to_type: HashMap<String, ADTDefinition>,
    record_name_to_definition: HashMap<String, RecordDefinition>,
}

pub fn _type(ast: &AST) -> Result<TypedAST, Vec<TypeError>> {
    TyperState::new(ast)?.check_types()
}

fn build_function_type_cache(function_declarations: &Vec<FunctionDeclaration>) -> HashMap<String, TypeScheme> {
    function_declarations.iter()
        .map(|d| (d.name.clone(), d.function_type.clone()))
        .collect()
}

fn build_adt_cache(type_declarations: &Vec<CustomType>) -> HashMap<String, ADTDefinition> {
    type_declarations.iter()
        .filter(|td| match td {
            CustomType::ADT(_, _) => true,
            _ => false
        })
        .flat_map(|adt| {
            match adt {
                CustomType::ADT(_, adt_def) => adt_def.constructors.iter().zip(iter::repeat(adt_def)),
                _ => unreachable!()
            }
        })
        .map(|((alternative, _), alternative_type)| {
            (alternative.clone(), alternative_type.clone())
        })
        .collect()
}

fn build_record_cache(type_declarations: &Vec<CustomType>) -> HashMap<String, RecordDefinition> {
    type_declarations.iter()
        .filter(|td| match td {
            CustomType::Record(_, _) => true,
            _ => false
        })
        .map(|record| match record {
            CustomType::Record(_, record_def) => (record_def.name.clone(), record_def.clone()),
            _ => unreachable!()
        })
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

fn check_unique_definitions(ast: &AST) -> Vec<TypeError> {
    let mut type_errors = Vec::new();

    // 1. Ensure there are no functions multiply defined
    let mut function_names: HashMap<String, Location> = HashMap::new();
    for d in &ast.function_declarations {
        if function_names.contains_key(&d.name) {
            type_errors.push(TypeError::from_loc(d.location.clone(), TypeErrorType::FunctionMultiplyDefined(d.name.clone(), function_names.get(&d.name).unwrap().clone())));
        } else {
            function_names.insert(d.name.clone(), d.location.clone());
        }
    }

    // 2. Ensure no ADTs with the same name are defined
    // 3. Ensure all ADT constructors are unique
    // 4. Ensure no records with the same name are defined
    let mut adt_names: HashMap<String, Location> = HashMap::new();
    let mut adt_constructors : HashMap<String, (String, Location)> = HashMap::new();
    let mut record_names: HashMap<String, Location> = HashMap::new();
    for td in &ast.type_declarations {
        match td {
            CustomType::ADT(location, adt_definition) => {
                if adt_names.contains_key(&adt_definition.name) {
                    type_errors.push(TypeError::from_loc(location.clone(), TypeErrorType::TypeMultiplyDefined(adt_definition.name.clone(), adt_names.get(&adt_definition.name).unwrap().clone())))
                } else {
                    for (constructor_name, _) in &adt_definition.constructors {
                        if adt_constructors.contains_key(constructor_name) {
                            let (defined_in, defined_in_location) = adt_constructors.get(constructor_name).unwrap();
                            type_errors.push(TypeError::from_loc(location.clone(), TypeErrorType::TypeConstructorMultiplyDefined(constructor_name.clone(), defined_in.clone(), defined_in_location.clone())))
                        } else {
                            adt_constructors.insert(constructor_name.clone(), (adt_definition.name.clone(), location.clone()));
                        }
                    }

                    adt_names.insert(adt_definition.name.clone(), location.clone());
                }
            }
            CustomType::Record(location, record_definition) => {
                if record_names.contains_key(&record_definition.name) {
                    type_errors.push(TypeError::from_loc(location.clone(), TypeErrorType::TypeMultiplyDefined(record_definition.name.clone(), record_names.get(&record_definition.name).unwrap().clone())))
                } else {
                    record_names.insert(record_definition.name.clone(), location.clone());
                }
            },
        }
    }
    type_errors

}

impl TyperState<'_> {
    fn new(ast: &AST) -> Result<TyperState, Vec<TypeError>> {
        let type_errors = check_unique_definitions(ast);
        if type_errors.len() > 0 {
            return Err(type_errors)
        }
        let function_name_to_type = build_function_type_cache(&ast.function_declarations);
        let adt_type_constructor_to_type = build_adt_cache(&ast.type_declarations);
        let record_name_to_definition = build_record_cache(&ast.type_declarations);
        return Ok(TyperState {
            ast,
            function_name_to_type,
            adt_type_constructor_to_type,
            record_name_to_definition,
        });
    }

    fn to_typed_ast(&self) -> TypedAST {
        TypedAST {
            function_name_to_declaration: self.ast.function_declarations.iter().map(|d| (d.name.clone(), d.clone())).collect(),
            adt_type_constructor_to_type: self.adt_type_constructor_to_type.clone(),
            record_name_to_definition: self.record_name_to_definition.clone(),
            main: self.ast.main.clone()
        }
    }

    fn check_types(&self) -> Result<TypedAST, Vec<TypeError>> {
        let mut errors: Vec<TypeError> = self.ast.function_declarations.iter()
            .map(|d| self.check_function_declaration(d))
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
            Ok(self.to_typed_ast())
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
        if let Type::Function(from, to) = &function_type.enclosed_type {
            if from.len() != body.match_expressions.len() {
                return Err(vec![TypeError::from(ErrorContext { file: body.location.file.clone(), function: name.to_string(), line: body.location.line, col: body.location.col }, ParameterCountMismatch(from.len(), body.match_expressions.len()))]);
            }

            let parameter_to_type: &mut HashMap<String, Type> = &mut HashMap::new();
            for (me, match_type) in (&body.match_expressions).into_iter().zip(from) {
                parameter_to_type.extend(self.check_match_expression(&body.location, &me, &match_type)?);
            }

            let errors: Vec<TypeError> = (&body.rules).into_iter()
                .map(|r| self.check_function_rule(&to, parameter_to_type, r))
                .filter(|r| r.is_err())
                .flat_map(|err| err.err().unwrap().into_iter())
                .collect();

            if errors.len() > 0 {
                return Err(errors)
            } else {
                return Ok(TypeResult {})
            }
        }

        unreachable!()
    }

    fn check_function_rule(&self, result_type: &Type, parameter_to_type: &mut HashMap<String, Type>, rule: &FunctionRule) -> Result<TypeResult, Vec<TypeError>> {
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
            LetRule(loc_info, match_expression, e) => {
                let expression_type = self.check_expression(e, &vec![], parameter_to_type)?;
                let match_expression_variables = self.check_match_expression(loc_info, match_expression, &expression_type)?;

                parameter_to_type.extend(match_expression_variables);
                Ok(TypeResult {})
            }
        }
    }

    fn check_match_expression(&self, loc_info: &Location, match_expression: &MatchExpression, expression_type: &Type) -> Result<HashMap<String, Type>, Vec<TypeError>> {
        match (match_expression, expression_type) {
            (MatchExpression::Identifier(loc_info, identifier), expression_type) => {
                let mut map = HashMap::new();
                map.insert(identifier.clone(), expression_type.clone());
                Ok(map)
            }
            (MatchExpression::Wildcard(loc_info), _) => Ok(HashMap::new()),
            (MatchExpression::IntLiteral(loc_info, _n), Type::Int) => Ok(HashMap::new()),
            (MatchExpression::CharLiteral(loc_info,_c), Type::Char) => Ok(HashMap::new()),
            (MatchExpression::StringLiteral(loc_info,_s), Type::String) => Ok(HashMap::new()),
            (MatchExpression::BoolLiteral(loc_info,_b), Type::Bool) => Ok(HashMap::new()),
            (MatchExpression::Tuple(loc_info,match_elements), Type::Tuple(element_types)) => {
                let mut variables_to_type = HashMap::new();
                for (match_element, element_type) in match_elements.iter().zip(element_types.iter()) {
                    let variables = self.check_match_expression(loc_info, match_element, element_type)?;
                    variables_to_type.extend(variables);
                }
                Ok(variables_to_type)
            }

            (MatchExpression::ShorthandList(loc_info,match_elements), Type::List(option_element_type)) => {
                let mut variables_to_type: HashMap<String, Type> = HashMap::new();
                for match_element in match_elements {
                    let variables = self.check_match_expression(loc_info, match_element, &option_element_type.as_ref())?;
                    for (name, vtype) in &variables {
                        if variables_to_type.contains_key(name) {
                            return Err(vec![TypeError::from_loc(loc_info.clone(), TypeErrorType::DuplicateVariableNameSingleMatchExpression(name.clone()))]);
                        }
                        variables_to_type.insert(name.clone(), vtype.clone());
                    }
                }
                Ok(variables_to_type)
            }
            (MatchExpression::LonghandList(loc_info,head, tail), Type::List(option_element_type)) => {
                let mut head_checked = self.check_match_expression(loc_info, head, &option_element_type.clone())?;
                let tail_checked = self.check_match_expression(loc_info, tail, &Type::List(option_element_type.clone()))?;
                head_checked.extend(tail_checked);
                Ok(head_checked)
            }
            (MatchExpression::ADT(loc_info,constructor_name, constructor_arguments), Type::UserType(type_name, _type_arguments)) => {
                let maybe_adt = self.adt_type_constructor_to_type.get(constructor_name);
                if let None = maybe_adt {
                    return Err(vec![TypeError::from_loc(loc_info.clone(), TypeErrorType::UndefinedTypeConstructor(constructor_name.clone()))]);
                }

                let adt = maybe_adt.unwrap();
                if adt.name != *type_name {
                    return Err(vec![TypeError::from_loc(loc_info.clone(), TypeErrorType::TypeMismatch(vec![Type::UserType(type_name.clone(), Vec::new())], Type::UserType(adt.name.clone(), Vec::new())))]);
                }

                let adt_alternative = adt.constructors.get(constructor_name).unwrap();
                if adt_alternative.elements.len() != constructor_arguments.len() {
                    return Err(vec![TypeError::from_loc(loc_info.clone(), TypeErrorType::TypeConstructorArgumentCountMismatch(constructor_name.clone(), adt_alternative.elements.len(), constructor_arguments.len()))]);
                }

                let mut variables = HashMap::new();
                for (arg, arg_type) in constructor_arguments.into_iter().zip((&adt_alternative.elements).into_iter()) {
                    variables.extend(self.check_match_expression(loc_info, arg, &arg_type)?);
                }
                Ok(variables)
            }
            (MatchExpression::Record(loc_info,_, fields), Type::UserType(record_name,_)) => {
                let record_definition = self.record_name_to_definition.get(record_name);

                if let None = record_definition {
                    return Err(vec![TypeError::from_loc(loc_info.clone(), TypeErrorType::UndefinedTypeConstructor(record_name.clone()))]);
                }

                let record_definition = record_definition.unwrap();
                let mut variables = HashMap::new();
                for field in fields {
                    let field_definition = record_definition.fields.get(field);
                    if let None = field_definition {
                        return Err(vec![TypeError::from_loc(loc_info.clone(), TypeErrorType::UndefinedRecordField(record_definition.name.clone(), field.clone()))]);
                    }
                    let field_type = field_definition.unwrap();
                    variables.insert(field.clone(), field_type.clone());
                }
                Ok(variables)
            }
            (_, expression_type) => {
                Err(vec![TypeError::from_loc(loc_info.clone(), TypeErrorType::MatchWrongType(expression_type.clone()))])
            }
        }
    }

    fn check_expression(&self, expression: &Expression, required_type: &Vec<Type>, parameter_to_type: &HashMap<String, Type>) -> Result<Type, Vec<TypeError>> {
        let type_eq_fixed = |operator, loc, result_type| |l, r| {
            return if l == r { Ok(result_type) } else { Err(TypeError::from_loc(loc, OperatorArgumentsNotEqual(operator, l, r))) };
        };
        let type_float_if_float_operands = |l, r| {
            return if l == Type::Float || r == Type::Float { Ok(Type::Float) } else { Ok(l) };
        };
        let type_add = |operator, loc| |l, r| {
            match (l, r) {
                (Type::List(t1), Type::List(t2)) if t1 == t2 => Ok(Type::List(t1)),
                (Type::Int, Type::Int) => Ok(Type::Int),
                (Type::Int, Type::Float) => Ok(Type::Float),
                (Type::Float, Type::Int) => Ok(Type::Float),
                (Type::Float, Type::Float) => Ok(Type::Float),
                (l, r) => Err(TypeError::from_loc(loc, OperatorArgumentsNotEqual(operator, l, r))),
            }
        };
        let type_fixed = |t| (|_l, _r| Ok(t));

        let (determined_type, loc_info): (Result<Type, Vec<TypeError>>, &Location) = match expression {
            Expression::BoolLiteral(loc_info, _) => (Ok(Type::Bool), loc_info),
            Expression::StringLiteral(loc_info, _) => (Ok(Type::String), loc_info),
            Expression::CharacterLiteral(loc_info, _) => (Ok(Type::Char), loc_info),
            Expression::IntegerLiteral(loc_info, _) => (Ok(Type::Int), loc_info),
            Expression::FloatLiteral(loc_info, _) => (Ok(Type::Float), loc_info),
            Expression::Call(loc_info, f, args) => (self.check_function_call(&f, &args, required_type, parameter_to_type, loc_info), loc_info),
            Expression::Variable(loc_info, v) => {
                (match parameter_to_type.get(v) {
                    Some(_type) => Ok(_type.clone()),
                    None => Err(vec![TypeError::from_loc(loc_info.clone(), TypeErrorType::UndefinedVariable(v.clone()))]),
                }, loc_info)
            }

            Expression::ADTTypeConstructor(loc_info, alternative_name, arguments) => {
                let maybe_adtdefinition = self.adt_type_constructor_to_type.get(alternative_name);
                if let None = maybe_adtdefinition {
                    return Err(vec![TypeError::from_loc(loc_info.clone(), TypeErrorType::UndefinedTypeConstructor(alternative_name.clone()))]);
                }

                let adt_def = maybe_adtdefinition.unwrap();

                let adt_alternative = adt_def.constructors.get(alternative_name).unwrap();
                if adt_alternative.elements.len() != arguments.len() {
                    return Err(vec![TypeError::from_loc(loc_info.clone(), TypeErrorType::TypeConstructorArgumentCountMismatch(alternative_name.clone(), adt_alternative.elements.len(), arguments.len()))]);
                }

                let errors: Vec<TypeError> = adt_alternative.elements.iter().zip(arguments.iter())
                    .map(|(alternative, expression)| self.check_expression(expression, &vec![alternative.clone()], parameter_to_type))
                    .filter(|result| result.is_err())
                    .flat_map(|r| r.err().unwrap().into_iter())
                    .collect();

                if errors.len() > 0 {
                    return Err(errors);
                }
                (Ok(Type::UserType(adt_def.name.clone(), Vec::new())), loc_info)
            }

            Expression::Record(loc_info, record_name, field_expressions) => {
                let record_definition = self.record_name_to_definition.get(record_name);
                if let None = record_definition {
                    return Err(vec![TypeError::from_loc(loc_info.clone(), TypeErrorType::UndefinedTypeConstructor(record_name.clone()))]);
                }
                let record_definition = record_definition.unwrap();

                for (field_name, expression) in field_expressions {
                    let required_type = record_definition.fields.get(field_name);
                    if let None = required_type {
                        return Err(vec![TypeError::from_loc(loc_info.clone(), TypeErrorType::UndefinedRecordField(record_name.clone(), field_name.clone()))]);
                    }
                    let required_type = required_type.unwrap();
                    self.check_expression(expression, &vec![required_type.clone()], parameter_to_type)?;
                }
                (Ok(Type::UserType(record_name.clone(), Vec::new())), loc_info)
            }

            Expression::TupleLiteral(loc_info, elements) => {
                let mut types = Vec::new();
                for e in elements {
                    types.push(self.check_expression(e, &vec![], parameter_to_type)?)
                }

                (Ok(Type::Tuple(types)), loc_info)
            }

            Expression::EmptyListLiteral(loc_info) => (Ok(Type::List(Box::new(Type::Int))), loc_info),
            Expression::ShorthandListLiteral(loc_info, elements) => {
                let mut det_type = Option::None;
                for e in elements {
                    let c_type = self.check_expression(e, &vec![], parameter_to_type)?;

                    if det_type.as_ref().filter(|t| **t != c_type).is_some() {
                        return Err(vec![TypeError::from_loc(loc_info.clone(), TypeErrorType::TypeMismatch(vec![det_type.unwrap()], c_type))]);
                    }

                    det_type = Some(c_type);
                }

                (Ok(Type::List(Box::new(det_type.unwrap()))), loc_info)
            }

            Expression::LonghandListLiteral(loc_info, head, tail) => {
                let list_type = Type::List(Box::new(self.check_expression(head, &vec![], parameter_to_type)?));
                let tail_type = self.check_expression(tail, &vec![list_type], parameter_to_type)?;
                (Ok(tail_type), loc_info)
            }

            Expression::Case(loc_info, case_expression, case_rules) => {
                let case_expression_type = self.check_expression(case_expression, &vec![], parameter_to_type)?;
                let mut last_type: Option<Type> = None;
                for case_rule in case_rules {
                    let mut lhs_variables: HashMap<String, Type> = self.check_match_expression(loc_info, &case_rule.case_rule, &case_expression_type)?;
                    lhs_variables.extend(parameter_to_type.into_iter().map(|(k, v)| (k.clone(), v.clone())));
                    let rhs_type = self.check_expression(&case_rule.result_rule, &vec![], &lhs_variables)?;
                    if last_type.is_some() && last_type.clone().filter(|lt| lt.clone() != rhs_type).is_some() {
                        return Err(vec![TypeError::from_loc(loc_info.clone(), TypeErrorType::TypeMismatch(vec![last_type.clone().unwrap()], rhs_type))]);
                    } else {
                        last_type = Some(rhs_type);
                    }
                }
                (Ok(last_type.unwrap()), loc_info)
            }

            Expression::Negation(loc_info, e) => (self.check_expression(e, &vec![Type::Bool], parameter_to_type), loc_info),
            Expression::Minus(loc_info, n) => (self.check_expression(n, &vec![Type::Int], parameter_to_type), loc_info),

            Expression::Times(loc_info, e1, e2) =>
                (combine(type_float_if_float_operands, self.check_expression(e1, &vec![Type::Int, Type::Float], parameter_to_type), self.check_expression(e2, &vec![Type::Int, Type::Float], parameter_to_type)), loc_info),
            Expression::Divide(loc_info, e1, e2) =>
                (combine(type_float_if_float_operands, self.check_expression(e1, &vec![Type::Int, Type::Float], parameter_to_type), self.check_expression(e2, &vec![Type::Int, Type::Float], parameter_to_type)), loc_info),
            Expression::Modulo(loc_info, e1, e2) =>
                (combine(type_fixed(Type::Int), self.check_expression(e1, &vec![Type::Int], parameter_to_type), self.check_expression(e2, &vec![Type::Int], parameter_to_type)), loc_info),

            Expression::Add(loc_info, e1, e2) =>
                (combine(type_add("+".to_string(), loc_info.clone()), self.check_expression(e1, &vec![Type::Int, Type::Float, Type::String], parameter_to_type), self.check_expression(e2, &vec![Type::Int, Type::Float, Type::String], parameter_to_type)), loc_info),

            Expression::Subtract(loc_info, e1, e2) =>
                (combine(type_float_if_float_operands, self.check_expression(e1, &vec![Type::Int, Type::Float], parameter_to_type), self.check_expression(e2, &vec![Type::Int, Type::Float], parameter_to_type)), loc_info),
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
            Expression::And(loc_info, e1, e2) =>
                (combine(type_fixed(Type::Bool), self.check_expression(e1, &vec![Type::Bool], parameter_to_type), self.check_expression(e2, &vec![Type::Bool], parameter_to_type)), loc_info),
            Expression::Or(loc_info, e1, e2) =>
                (combine(type_fixed(Type::Bool), self.check_expression(e1, &vec![Type::Bool], parameter_to_type), self.check_expression(e2, &vec![Type::Bool], parameter_to_type)), loc_info),

            Expression::Eq(loc_info, e1, e2) =>
                (combine(type_eq_fixed("==".to_string(), loc_info.clone(), Type::Bool), self.check_expression(e1, &vec![], parameter_to_type), self.check_expression(e2, &vec![], parameter_to_type)), loc_info),
            Expression::Neq(loc_info, e1, e2) =>
                (combine(type_eq_fixed("==".to_string(), loc_info.clone(), Type::Bool), self.check_expression(e1, &vec![], parameter_to_type), self.check_expression(e2, &vec![], parameter_to_type)), loc_info),
        };

        if let Err(r) = determined_type {
            return Err(r);
        }

        let determined_type = determined_type.ok().unwrap();
        if required_type.is_empty() {
            return Ok(determined_type);
        }

        if !required_type.contains(&determined_type) {
            return Err(vec![TypeError::from(ErrorContext { file: loc_info.file.clone(), function: loc_info.function.clone(), line: loc_info.line, col: loc_info.col }, TypeMismatch(required_type.clone(), determined_type))]);
        }

        Ok(determined_type)
    }

    fn check_function_call(&self, name: &String, args: &Vec<Expression>, required_type: &Vec<Type>, parameter_to_type: &HashMap<String, Type>, loc_info: &Location) -> Result<Type, Vec<TypeError>> {
        let ftype = self.function_name_to_type.get(name);
        if let None = ftype.clone() {
            return Err(vec![TypeError::from(ErrorContext { file: loc_info.file.clone(), function: loc_info.function.clone(), line: loc_info.line, col: loc_info.col }, UndefinedFunction(name.clone()))]);
        }

        if let Type::Function(from, to) = ftype.unwrap().clone().enclosed_type {
            if from.len() != args.len() {
                return Err(vec![TypeError::from(ErrorContext { file: loc_info.file.clone(), function: loc_info.function.clone(), line: loc_info.line, col: loc_info.col }, FunctionCallArgumentCountMismatch(name.clone(), from.len(), args.len()))]);
            }

            let errors: Vec<TypeError> = from.into_iter().zip(args.into_iter())
                .map(|(atype, e)| self.check_expression(e, &vec![atype.clone()], parameter_to_type))
                .filter(|r| r.is_err())
                .flat_map(|r| r.err().unwrap())
                .collect();

            if errors.len() > 0 {
                return Err(errors);
            }

            if required_type.is_empty() || required_type.contains(&to) {
                return Ok(*to);
            }
            return Err(vec![TypeError::from(ErrorContext { file: loc_info.file.clone(), function: loc_info.function.clone(), line: loc_info.line, col: loc_info.col }, TypeMismatch(required_type.clone(), *to))])
        }
        unreachable!()
    }
}
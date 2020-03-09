use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Error, Formatter};
use std::iter;

use crate::inferencer::substitutor::{substitute, substitute_list, substitute_type};
use crate::inferencer::unifier::{unify, unify_one_of};
use crate::parser::*;

mod unifier;
mod substitutor;
mod grapher;

#[derive(Debug)]
pub struct InferenceError {
    context: ErrorContext,
    err: InferenceErrorType,
}

impl InferenceError {
    fn from_loc(loc: Location, err: InferenceErrorType) -> InferenceError {
        InferenceError {
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

#[derive(Debug, PartialEq)]
pub enum InferenceErrorType {
    UnificationError(Type, Type),
    UnificationErrorMultiple(Vec<Type>, Type),
    UnboundTypeVariable(String),
    WrongNumberOfTypes(usize, usize),
    UndefinedFunction(String),

    FunctionDeclaredTypeMismatch(Type, Type),

    // Expected, Derived, source of expected type.
    FunctionDerivedTypeMismatch(Type, Type, Location),

    FunctionMultiplyDefined(String, Location),
    TypeMultiplyDefined(String, Location),
    TypeConstructorMultiplyDefined(String, String, Location),

    // ADT
    UndefinedTypeConstructor(String),
    WrongNumberConstructorArguments(String, usize, usize),

    // Record
    UndefinedRecord(String),
    UndefinedRecordFields(String, Vec<String>),
    MissingRecordFields(String, Vec<String>),

    UndefinedVariable(String),
}

#[derive(Debug)]
pub struct TypedAST {
    pub function_name_to_declaration: HashMap<String, FunctionDeclaration>,
    pub adt_type_constructor_to_type: HashMap<String, ADTDefinition>,
    pub record_name_to_definition: HashMap<String, RecordDefinition>,
    pub main: Expression,
}

#[derive(Debug)]
struct ErrorContext {
    file: String,
    function: String,
    line: usize,
    col: usize,
}

impl Display for InferenceError {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        write_error_context(f, &self.context)?;
        match &self.err {
            InferenceErrorType::UnificationError(a, b) => write!(f, "Could not unify expected type\n\t{}\nwith inferred type\n\t{}", b, a),
            InferenceErrorType::UnificationErrorMultiple(a, b) => write!(f, "Could not unify one of \n\t[{}]\nwith\n\t{}", a.into_iter().map(|a| a.to_string()).collect::<Vec<String>>().join(","), b),
            InferenceErrorType::UnboundTypeVariable(v) => write!(f, "Unbound type variable '{}'", v),
            InferenceErrorType::WrongNumberOfTypes(left, right) => write!(f, "Expected {} types, got {}", left, right),

            InferenceErrorType::FunctionDeclaredTypeMismatch(declared, derived) => write!(f, "Declared type\n\t{}\nnot equal to inferred type\n\t{}", declared, derived),
            InferenceErrorType::FunctionDerivedTypeMismatch(expected, derived, location_derived) => write!(f, "Derived type from previous body at line {}\n\t{}\ncould not be unified with current derived body type\n\t{}", location_derived.line, expected, derived),

            InferenceErrorType::FunctionMultiplyDefined(name, location) => write!(f, "Function {} already defined, encountered earlier at {}", name, location),
            InferenceErrorType::UndefinedFunction(name) => write!(f, "Function {} undefined", name),

            InferenceErrorType::TypeMultiplyDefined(name, location) => write!(f, "Type {} already defined, encountered earlier at {}", name, location),
            InferenceErrorType::TypeConstructorMultiplyDefined(constructor_name, defined_in_type, defined_in_location) => write!(f, "Type constructor {} already defined in type {} at {}", constructor_name, defined_in_type, defined_in_location),
            // ADT
            InferenceErrorType::UndefinedTypeConstructor(name) => write!(f, "Undefined type constructor {}", name),
            InferenceErrorType::WrongNumberConstructorArguments(name, expected, got) => write!(f, "Expected {} arguments to type constructor {}, got {}", expected, name, got),

            // Record
            InferenceErrorType::UndefinedRecord(name) => write!(f, "Record with name {} is not defined", name),

            InferenceErrorType::UndefinedRecordFields(name, undefined_fields) if undefined_fields.len() == 1
            => write!(f, "Field {} is not defined in record {}", undefined_fields.join(","), name),
            InferenceErrorType::UndefinedRecordFields(name, undefined_fields)
            => write!(f, "Fields [{}] are not defined in record {}", undefined_fields.join(","), name),

            InferenceErrorType::MissingRecordFields(name, missing_fields_values) if missing_fields_values.len() == 1
            => write!(f, "Field {} is missing a value in record {}", missing_fields_values.join(","), name),
            InferenceErrorType::MissingRecordFields(name, missing_fields_values)
            => write!(f, "Fields [{}] are missing a value in record {}", missing_fields_values.join(","), name),

            InferenceErrorType::UndefinedVariable(name) => write!(f, "Variable {} is not defined", name)
        }
    }
}

fn write_error_context(f: &mut Formatter<'_>, context: &ErrorContext) -> Result<(), Error> {
    write!(f, "{}::{}@[{}:{}]: ", context.file, context.function, context.line, context.col)
}

#[derive(Debug)]
pub struct InferencerResult {}

struct VariableNameStream {
    n: usize
}

impl Iterator for VariableNameStream {
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {
        let i = self.n;
        self.n += 1;
        Some(format!("v{}", i.to_string()))
    }
}

struct InferencerState<'a> {
    main: &'a Expression,
    adt_type_constructor_to_type: HashMap<String, ADTDefinition>,
    record_name_to_definition: HashMap<String, RecordDefinition>,
    type_variable_iterator: Box<dyn Iterator<Item=String>>,

    global_type_context: HashMap<String, TypeScheme>,

    local_type_context: HashMap<String, Type>,
}

pub fn infer(ast: &AST) -> Result<TypedAST, Vec<InferenceError>> {
    let mut infer_state = InferencerState::new(ast)?;
    let components = grapher::to_components(ast);
    Ok(infer_state.infer(components, &ast.main)?)
}

fn build_function_scheme_cache(function_declarations: &Vec<FunctionDeclaration>) -> HashMap<String, TypeScheme> {
    function_declarations.iter()
        .filter(|d| d.function_type.is_some())
        .map(|d| (d.name.clone(), d.function_type.clone().unwrap()))
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


impl InferencerState<'_> {
    fn new(ast: &AST) -> Result<InferencerState, Vec<InferenceError>> {
        // 1. Check whether all functions are uniquely defined.
        let type_errors = check_unique_definitions(ast);
        if type_errors.len() > 0 {
            return Err(type_errors);
        }

        // 2. Register all functions which have a type.
        let function_name_to_type = build_function_scheme_cache(&ast.function_declarations);

        // 3. Register all user-defined types.
        let adt_type_constructor_to_type = build_adt_cache(&ast.type_declarations);
        let record_name_to_definition = build_record_cache(&ast.type_declarations);

        return Ok(InferencerState {
            main: &ast.main,
            adt_type_constructor_to_type,
            record_name_to_definition,
            type_variable_iterator: Box::new(VariableNameStream { n: 1 }),
            global_type_context: function_name_to_type,
            local_type_context: HashMap::new(),
        });
    }
}

fn check_unique_definitions(ast: &AST) -> Vec<InferenceError> {
    let mut type_errors = Vec::new();

    // 1. Ensure there are no functions multiply defined
    let mut function_names: HashMap<String, Location> = HashMap::new();
    for d in &ast.function_declarations {
        if function_names.contains_key(&d.name) {
            type_errors.push(InferenceError::from_loc(d.location.clone(), InferenceErrorType::FunctionMultiplyDefined(d.name.clone(), function_names.get(&d.name).unwrap().clone())));
        } else {
            function_names.insert(d.name.clone(), d.location.clone());
        }
    }

    // 2. Ensure no ADTs with the same name are defined
    // 3. Ensure all ADT constructors are unique
    // 4. Ensure no records with the same name are defined
    let mut adt_names: HashMap<String, Location> = HashMap::new();
    let mut adt_constructors: HashMap<String, (String, Location)> = HashMap::new();
    let mut record_names: HashMap<String, Location> = HashMap::new();
    for td in &ast.type_declarations {
        match td {
            CustomType::ADT(location, adt_definition) => {
                // 1. Check whether some other type with this name is defined
                if adt_names.contains_key(&adt_definition.name) {
                    type_errors.push(InferenceError::from_loc(location.clone(), InferenceErrorType::TypeMultiplyDefined(adt_definition.name.clone(), adt_names.get(&adt_definition.name).unwrap().clone())))
                } else {
                    // 2. Check whether all constructors are uniquely defined
                    for (constructor_name, alternative) in &adt_definition.constructors {
                        if adt_constructors.contains_key(constructor_name) {
                            let (defined_in, defined_in_location) = adt_constructors.get(constructor_name).unwrap();
                            type_errors.push(InferenceError::from_loc(location.clone(), InferenceErrorType::TypeConstructorMultiplyDefined(constructor_name.clone(), defined_in.clone(), defined_in_location.clone())))
                        } else {
                            // 3. Check whether a constructor only uses defined type variables, if any.
                            for variable_name in alternative.elements.iter().flat_map(|e| e.collect_free_type_variables().into_iter()) {
                                if !adt_definition.type_variables.contains(&variable_name) {
                                    type_errors.push(InferenceError::from_loc(location.clone(), InferenceErrorType::UnboundTypeVariable(variable_name.clone())))
                                }
                            }
                            adt_constructors.insert(constructor_name.clone(), (adt_definition.name.clone(), location.clone()));
                        }
                    }

                    adt_names.insert(adt_definition.name.clone(), location.clone());
                }
            }
            CustomType::Record(location, record_definition) => {
                if record_names.contains_key(&record_definition.name) {
                    type_errors.push(InferenceError::from_loc(location.clone(), InferenceErrorType::TypeMultiplyDefined(record_definition.name.clone(), record_names.get(&record_definition.name).unwrap().clone())))
                } else {
                    record_names.insert(record_definition.name.clone(), location.clone());
                }
            }
        }
    }
    type_errors
}

fn map_unify(loc: Location, r: Result<Vec<(TypeVar, Type)>, InferenceErrorType>) -> Result<Vec<(TypeVar, Type)>, Vec<InferenceError>> {
    r.map_err(|e| vec![InferenceError::from_loc(loc.clone(), e)])
}

impl InferencerState<'_> {
    fn fresh(&mut self) -> Type {
        Type::Variable(self.type_variable_iterator.next().unwrap())
    }

    fn extend_type_environment(&mut self, with: &Vec<(TypeVar, Type)>) {
        self.local_type_context = self.local_type_context.iter()
            .map(|(n, t)| (n.clone(), substitutor::substitute_type(with, &t)))
            .collect();

        self.global_type_context = self.global_type_context.iter()
            .map(|(n, t)| (n.clone(), substitutor::substitute(with, &t)))
            .collect();
    }

    fn infer(&mut self, components: Vec<Vec<&FunctionDeclaration>>, main: &Expression) -> Result<TypedAST, Vec<InferenceError>> {
        for component in &components {
            // Generate fresh variables for all declarations in a component
            for d in component.iter() {
                let fresh = self.fresh();
                self.global_type_context.insert(d.name.clone(), TypeScheme { bound_variables: HashSet::new(), enclosed_type: fresh });
            }

            // Infer every declaration
            for d in component {
                let subs = self.infer_function_declaration(d)?;
                self.extend_type_environment(&subs);
            }

            // Generalize all declarations in a component
            for d in component {
                let derived_scheme = (&self.global_type_context).get(&d.name).unwrap();
                let generalized_scheme = self.generalize(derived_scheme.enclosed_type.clone());
                println!("Type for function '{}': {}", d.name.clone(), generalized_scheme);
                self.global_type_context.insert(d.name.clone(), generalized_scheme);
            }
        }

        let fresh = self.fresh();
        self.infer_expression(main, &fresh)?;

        Ok(TypedAST {
            function_name_to_declaration: components.into_iter().flat_map(|c| c.into_iter()).map(|d| (d.name.clone(), d.clone().clone())).collect(),
            adt_type_constructor_to_type: self.adt_type_constructor_to_type.clone(),
            record_name_to_definition: self.record_name_to_definition.clone(),
            main: self.main.clone(),
        })
    }

    fn instantiate(&mut self, t: &TypeScheme) -> Type {
        let mut subs = Vec::new();
        for v in &t.bound_variables {
            subs.push((v.clone(), self.fresh()));
        }
        substitute_type(&subs, &t.enclosed_type)
    }

    fn generalize(&self, t: Type) -> TypeScheme {
        let free = t.collect_free_type_variables();

        TypeScheme { bound_variables: free, enclosed_type: t }
    }

    fn infer_function_declaration(&mut self, declaration: &FunctionDeclaration) -> Result<Vec<(TypeVar, Type)>, Vec<InferenceError>> {
        let mut function_type = self.fresh();
        let mut function_type_location_mutated = declaration.location.clone();
        for body in (&declaration.function_bodies).into_iter() {
            let mut current_match_types = Vec::new();
            let mut current_return_type = self.fresh();
            for me in &body.match_expressions {
                let fresh = self.fresh();
                let subs = self.infer_match_expression(me, &fresh)?;
                self.extend_type_environment(&subs);
                current_match_types = substitute_list(&subs, &current_match_types);
                current_match_types.push(substitute_type(&subs, &fresh));
            }

            for r in &body.rules {
                match r {
                    FunctionRule::ConditionalRule(_loc, condition, expression) => {
                        let subs = self.infer_expression(&condition, &Type::Bool)?;
                        self.extend_type_environment(&subs);
                        current_match_types = substitute_list(&subs, &current_match_types);
                        current_return_type = substitute_type(&subs, &current_return_type);

                        let subs = self.infer_expression(&expression, &current_return_type)?;
                        self.extend_type_environment(&subs);
                        current_return_type = substitute_type(&subs, &current_return_type);
                        current_match_types = substitute_list(&subs, &current_match_types);
                    }
                    FunctionRule::ExpressionRule(_loc, expression) => {
                        let subs = self.infer_expression(&expression, &current_return_type)?;
                        self.extend_type_environment(&subs);

                        current_return_type = substitute_type(&subs, &current_return_type);
                        current_match_types = substitute_list(&subs, &current_match_types);
                    }
                    FunctionRule::LetRule(_loc, match_expression, expression) => {
                        let fresh = self.fresh();
                        let subs = self.infer_match_expression(&match_expression, &fresh)?;
                        self.extend_type_environment(&subs);
                        current_match_types = substitute_list(&subs, &current_match_types);
                        current_return_type = substitute_type(&subs, &current_return_type);

                        let subs = self.infer_expression(&expression, &substitute_type(&subs, &fresh))?;
                        self.extend_type_environment(&subs);
                        current_match_types = substitute_list(&subs, &current_match_types);
                        current_return_type = substitute_type(&subs, &current_return_type);
                    }
                }
            }

            self.local_type_context.clear();

            let derived_function_type = Type::Function(current_match_types, Box::new(current_return_type));

            match unify(&derived_function_type, &function_type) {
                Ok(subs) => {
                    self.extend_type_environment(&subs);
                    let new_function_type = substitute_type(&subs, &function_type);
                    if new_function_type != function_type {
                        function_type_location_mutated = body.location.clone();
                    }
                    function_type = new_function_type;
                }
                Err(_) => return Err(vec![InferenceError::from_loc(body.location.clone(), InferenceErrorType::FunctionDerivedTypeMismatch(function_type, derived_function_type.clone(), function_type_location_mutated.clone()))]),
            }
        }

        let mut derived_scheme = self.global_type_context.get(&declaration.name).unwrap().clone();

        let subs = map_unify(declaration.location.clone(), unify(&derived_scheme.enclosed_type, &function_type))?;
        self.extend_type_environment(&subs);

        if let Some(declared_scheme) = &declaration.function_type {

            derived_scheme = substitute(&subs, &derived_scheme);

            let subs = map_unify(declaration.location.clone(), unify(&derived_scheme.enclosed_type, &declared_scheme.enclosed_type))?;
            self.extend_type_environment(&subs);
            let substituted_type = substitute_type(&subs, &declared_scheme.enclosed_type);

            let declared_substituted_scheme = TypeScheme { bound_variables: substituted_type.clone().collect_free_type_variables(), enclosed_type: substituted_type.clone() };

            if &declared_substituted_scheme != declared_scheme {
                return Err(vec![InferenceError::from_loc(declaration.location.clone(), InferenceErrorType::FunctionDeclaredTypeMismatch(declared_scheme.enclosed_type.clone(), substituted_type.clone()))]);
            }
            Ok(Vec::new())
        } else {
            Ok(Vec::new())
        }
    }

    fn infer_match_expression(&mut self, me: &MatchExpression, expected_type: &Type) -> Result<Vec<(TypeVar, Type)>, Vec<InferenceError>> {
        let subs = match me {
            MatchExpression::IntLiteral(loc, _) => map_unify(loc.clone(), unify(&Type::Int, expected_type))?,
            MatchExpression::CharLiteral(loc, _) => map_unify(loc.clone(), unify(&Type::Char, expected_type))?,
            MatchExpression::StringLiteral(loc, _) => map_unify(loc.clone(), unify(&Type::String, expected_type))?,
            MatchExpression::BoolLiteral(loc, _) => map_unify(loc.clone(), unify(&Type::Bool, expected_type))?,

            MatchExpression::Identifier(_, name) => {
                self.local_type_context.insert(name.clone(), expected_type.clone());
                Vec::new()
            }

            MatchExpression::Tuple(loc, elements) => {
                let mut element_types = Vec::new();
                let mut union_subs = Vec::new();
                for e in elements {
                    let fresh = self.fresh();
                    let subs = self.infer_match_expression(e, &fresh)?;
                    self.extend_type_environment(&subs);
                    union_subs.extend(subs.clone());
                    element_types.push(substitute_type(&subs, &fresh));
                }

                map_unify(loc.clone(), unify(&Type::Tuple(element_types), &expected_type))
                    .map(|mut r| {
                        r.extend(union_subs);
                        r
                    })?
            }
            MatchExpression::LonghandList(loc, head, tail) => {
                let fresh_head = self.fresh();
                let head_subs = self.infer_match_expression(head, &fresh_head)?;
                self.extend_type_environment(&head_subs);

                let head_type = substitute_type(&head_subs, &fresh_head);

                let tail_subs = self.infer_match_expression(tail, &Type::List(Box::new(head_type.clone())))?;
                self.extend_type_environment(&tail_subs);

                let tail_type = substitute_type(&tail_subs, &Type::List(Box::new(head_type)));
                map_unify(loc.clone(), unify(&tail_type, &expected_type))
                    .map(|r| {
                        let mut nr = Vec::new();
                        nr.extend(head_subs);
                        nr.extend(tail_subs);
                        nr.extend(r);
                        nr
                    })?
            }
            MatchExpression::ADT(loc, constructor_name, constructor_arguments) => {
                let adt_definition = match self.adt_type_constructor_to_type.get(constructor_name) {
                    Some(d) => d.clone(),
                    None => return Err(vec![InferenceError::from_loc(loc.clone(), InferenceErrorType::UndefinedTypeConstructor(constructor_name.clone()))]),
                };
                let adt_constructor_definition = adt_definition.constructors.get(constructor_name).unwrap();

                if adt_constructor_definition.elements.len() != constructor_arguments.len() {
                    return Err(vec![InferenceError::from_loc(loc.clone(), InferenceErrorType::WrongNumberConstructorArguments(constructor_name.clone(), adt_constructor_definition.elements.len(), constructor_arguments.len()))]);
                }

                let mut type_variable_to_type = HashMap::new();
                for v in &adt_definition.type_variables {
                    type_variable_to_type.insert(v.clone(), self.fresh());
                }

                let instantiated_definition_argument_types = substitute_list(&type_variable_to_type.clone().into_iter().collect(), &adt_constructor_definition.elements);

                let mut argument_types = Vec::new();
                let mut union_subs = Vec::new();
                for arg in constructor_arguments {
                    let fresh = self.fresh();
                    let subs = self.infer_match_expression(&arg, &fresh)?;
                    union_subs.extend(subs.clone());
                    argument_types.push(substitute_type(&subs, &fresh));
                }

                let mut argument_substitutions = Vec::new();
                for ((l, r), ex) in argument_types.iter().zip(instantiated_definition_argument_types.iter()).zip(constructor_arguments.iter()) {
                    let subs = map_unify(ex.locate(), unify(&l, &r))?;
                    argument_substitutions = subs;
                }

                union_subs.extend(argument_substitutions.clone());

                type_variable_to_type = type_variable_to_type.iter()
                    .map(|(name, t)| (name.clone(), substitute_type(&argument_substitutions, t))).collect();

                let mut concrete_types = Vec::new();
                for tv in &adt_definition.type_variables {
                    concrete_types.push(type_variable_to_type.get(tv).unwrap().clone());
                }

                map_unify(loc.clone(), unify(&Type::UserType(adt_definition.name.clone(), concrete_types), expected_type))?
            }
            MatchExpression::ShorthandList(loc, elements) => {
                let mut element_type = self.fresh();
                let mut union_subs = Vec::new();
                for e in elements {
                    let subs = self.infer_match_expression(e, &element_type)?;
                    self.extend_type_environment(&subs);
                    union_subs.extend(subs.clone());

                    element_type = substitute_type(&subs, &element_type);
                }

                map_unify(loc.clone(), unify(&Type::List(Box::new(element_type)), expected_type))
                    .map(|mut r| {
                        r.extend(union_subs);
                        r
                    })?
            }

            MatchExpression::Wildcard(_loc) => Vec::new(),
            MatchExpression::Record(loc, name, fields) => {
                let record_definition = match self.record_name_to_definition.get(name) {
                    Some(d) => d.clone(),
                    None => return Err(vec![InferenceError::from_loc(loc.clone(), InferenceErrorType::UndefinedRecord(name.clone()))]),
                };

                let undefined_fields: Vec<String> = fields.into_iter()
                    .filter(|n| !record_definition.fields.contains_key(*n))
                    .map(|n| n.clone())
                    .collect();

                if undefined_fields.len() > 0 {
                    return Err(vec![InferenceError::from_loc(loc.clone(), InferenceErrorType::UndefinedRecordFields(name.clone(), undefined_fields))]);
                }

                // :: Data a b c = {alpha: a, beta: b, gamma: c}
                // >>>> :: Data v0 v1 v2 = {alpha: v0, beta: v1, gamma: v2}
                let mut type_variable_to_type = HashMap::new();
                let mut variables = Vec::new();
                for tv in record_definition.type_variables {
                    let fresh = self.fresh();
                    variables.push(fresh.clone());
                    type_variable_to_type.insert(tv.clone(), fresh.clone());
                }

                let mut instantiated_field_types = HashMap::new();
                for field in fields {
                    instantiated_field_types.insert(field.clone(), substitute_type(&type_variable_to_type.clone().into_iter().collect(), record_definition.fields.get(field).unwrap()));
                }

                /*
                    Unify with the required type, which might be (Data Int String Int)
                    For instance:
                        v0 -> Int,
                        v1 -> String,
                        v2 -> Int,
                */
                let subs = map_unify(loc.clone(), unify(&Type::UserType(name.clone(), variables), &expected_type))?;

                // For every field used in the match expression, add a variable with the discovered type.
                let mut field_to_type = HashMap::new();
                for (field_name, field_type) in instantiated_field_types {
                    self.local_type_context.insert(field_name.clone(), substitute_type(&subs, &field_type));
                    field_to_type.insert(field_name.clone(), substitute_type(&subs, &field_type));
                }
                subs
            }
        };
        Ok(subs)
    }

    fn infer_binary_expression(&mut self, loc: &Location, l: &Expression, r: &Expression, sub_types: &Vec<Type>,
                               name: String, type_transformer: impl FnOnce(String, &Type, &Type) -> Type, expected_type: &Type)
                               -> Result<Vec<(TypeVar, Type)>, Vec<InferenceError>> {
        let fresh_l = self.fresh();
        let subs_l = self.infer_expression(l, &fresh_l)?;
        self.extend_type_environment(&subs_l);

        let l_type = &substitute_type(&subs_l, &fresh_l);
        let subs_l = map_unify(l.locate(), unify_one_of(sub_types, l_type))?;
        self.extend_type_environment(&subs_l);

        let fresh_r = self.fresh();
        let subs_r = self.infer_expression(r, &fresh_r)?;
        self.extend_type_environment(&subs_r);

        let r_type = &substitute_type(&subs_r, &fresh_r);
        let subs_r = map_unify(r.locate(), unify_one_of(sub_types, r_type))?;
        self.extend_type_environment(&subs_r);

        let l_type = substitute_type(&subs_l, l_type);
        let r_type = substitute_type(&subs_r, r_type);
        let subs_e = map_unify(loc.clone(), unify(&l_type, &r_type))?;
        self.extend_type_environment(&subs_e);

        let l_type = substitute_type(&subs_e, &l_type);
        let r_type = substitute_type(&subs_e, &r_type);
        map_unify(loc.clone(), unify(&type_transformer(name, &l_type, &r_type), expected_type))
    }

    fn infer_expression(&mut self, e: &Expression, expected_type: &Type) -> Result<Vec<(TypeVar, Type)>, Vec<InferenceError>> {
        let static_type_combinator = |result_type: Type| |_, _ltype: &Type, _rtype: &Type| result_type;
        let binary_number_type_combinator = |op: String, l_type: &Type, r_type: &Type| match (l_type, r_type) {
            (Type::Int, Type::Int) => Type::Int,
            (Type::Float, Type::Float) => Type::Float,
            t => panic!("Unable to determine result type for operator '{}': {:#?}", op.clone(), t)
        };
        let res = match e {
            Expression::BoolLiteral(loc, _) => map_unify(loc.clone(), unify(&Type::Bool, &expected_type))?,
            Expression::StringLiteral(loc, _) => map_unify(loc.clone(), unify(&Type::String, &expected_type))?,
            Expression::CharacterLiteral(loc, _) => map_unify(loc.clone(), unify(&Type::Char, &expected_type))?,
            Expression::IntegerLiteral(loc, _) => map_unify(loc.clone(), unify(&Type::Int, &expected_type))?,
            Expression::FloatLiteral(loc, _) => map_unify(loc.clone(), unify(&Type::Float, &expected_type))?,

            Expression::Negation(loc, e) => {
                let fresh = self.fresh();
                let subs = self.infer_expression(e, &fresh)?;
                self.extend_type_environment(&subs);

                let subs = map_unify(e.locate(), unify(&Type::Bool, &substitute_type(&subs, &fresh)))?;
                self.extend_type_environment(&subs);
                map_unify(loc.clone(), unify(&Type::Bool, expected_type))?
            }

            Expression::Minus(loc, e) => {
                let fresh = self.fresh();
                let subs = self.infer_expression(e, &fresh)?;
                self.extend_type_environment(&subs);

                let e_type = substitute_type(&subs, &fresh);
                let subs = map_unify(e.locate(), unify_one_of(&vec![Type::Int, Type::Float], &e_type))?;
                self.extend_type_environment(&subs);

                map_unify(loc.clone(), unify(&e_type, expected_type))?
            }

            Expression::Times(loc, l, r)
            => self.infer_binary_expression(loc, l, r, &vec![Type::Int, Type::Float], "*".to_string(), binary_number_type_combinator, expected_type)?,

            Expression::Divide(loc, l, r)
            => self.infer_binary_expression(loc, l, r, &vec![Type::Int, Type::Float], "/".to_string(), binary_number_type_combinator, expected_type)?,

            Expression::Modulo(loc, l, r)
            => self.infer_binary_expression(loc, l, r, &vec![Type::Int, Type::Float], "%".to_string(), binary_number_type_combinator, expected_type)?,

            Expression::Add(loc, l, r)
            => self.infer_binary_expression(loc, l, r, &vec![Type::Int, Type::Float], "+".to_string(), binary_number_type_combinator, expected_type)?,

            Expression::Subtract(loc, l, r)
            => self.infer_binary_expression(loc, l, r, &vec![Type::Int, Type::Float], "-".to_string(), binary_number_type_combinator, expected_type)?,

            Expression::ShiftLeft(loc, l, r)
            => self.infer_binary_expression(loc, l, r, &vec![Type::Int], "<<".to_string(), static_type_combinator(Type::Int), expected_type)?,

            Expression::ShiftRight(loc, l, r)
            => self.infer_binary_expression(loc, l, r, &vec![Type::Int], ">>".to_string(), static_type_combinator(Type::Int), expected_type)?,

            Expression::Greater(loc, l, r)
            => self.infer_binary_expression(loc, l, r, &vec![Type::Int, Type::Float], ">".to_string(), static_type_combinator(Type::Bool), expected_type)?,

            Expression::Greq(loc, l, r)
            => self.infer_binary_expression(loc, l, r, &vec![Type::Int, Type::Float], ">=".to_string(), static_type_combinator(Type::Bool), expected_type)?,

            Expression::Leq(loc, l, r)
            => self.infer_binary_expression(loc, l, r, &vec![Type::Int, Type::Float], "<=".to_string(), static_type_combinator(Type::Bool), expected_type)?,

            Expression::Lesser(loc, l, r)
            => self.infer_binary_expression(loc, l, r, &vec![Type::Int, Type::Float], "<".to_string(), static_type_combinator(Type::Bool), expected_type)?,

            Expression::Eq(loc, l, r)
            => self.infer_binary_expression(loc, l, r, &vec![Type::Int, Type::Float, Type::String, Type::Char, Type::Bool], "==".to_string(), static_type_combinator(Type::Bool), expected_type)?,

            Expression::Neq(loc, l, r)
            => self.infer_binary_expression(loc, l, r, &vec![Type::Int, Type::Float, Type::String, Type::Char, Type::Bool], "!=".to_string(), static_type_combinator(Type::Bool), expected_type)?,

            Expression::And(loc, l, r)
            => self.infer_binary_expression(loc, l, r, &vec![Type::Bool], "&&".to_string(), static_type_combinator(Type::Bool), expected_type)?,

            Expression::Or(loc, l, r)
            => self.infer_binary_expression(loc, l, r, &vec![Type::Bool], "||".to_string(), static_type_combinator(Type::Bool), expected_type)?,

            Expression::Variable(loc, name) => {
                let variable_type = match self.local_type_context.get(name) {
                    None => return Err(vec![InferenceError::from_loc(loc.clone(), InferenceErrorType::UndefinedVariable(name.clone()))]),
                    Some(vtype) => vtype,
                };

                map_unify(loc.clone(), unify(variable_type, expected_type))?
            }

            Expression::TupleLiteral(loc, elements) => {
                let mut types = Vec::new();
                let mut union_subs = Vec::new();
                for e in elements {
                    let fresh_type = self.fresh();
                    let subs = self.infer_expression(e, &fresh_type)?;
                    self.extend_type_environment(&subs);
                    types = substitute_list(&subs, &types);
                    types.push(substitute_type(&subs, &fresh_type));
                    union_subs.extend(subs);
                }
                map_unify(loc.clone(), unify(&Type::Tuple(types), &expected_type))
                    .map(|mut r| {
                        r.extend(union_subs);
                        r
                    })?
            }
            Expression::EmptyListLiteral(loc) => {
                let fresh = self.fresh();
                map_unify(loc.clone(), unify(&Type::List(Box::new(fresh)), &expected_type))?
            }
            Expression::ShorthandListLiteral(loc, elements) => {
                let mut list_type = self.fresh();
                let mut union_subs = Vec::new();
                for e in elements {
                    let subs = self.infer_expression(e, &list_type)?;
                    self.extend_type_environment(&subs);
                    union_subs.extend(subs.clone());
                    list_type = substitute_type(&subs, &list_type);
                }
                map_unify(loc.clone(), unify(&Type::List(Box::new(list_type)), &expected_type))
                    .map(|mut r| {
                        r.extend(union_subs);
                        r
                    })?
            }
            Expression::LonghandListLiteral(loc, head, tail) => {
                let fresh = self.fresh();
                let head_subs = self.infer_expression(&head, &fresh)?;
                self.extend_type_environment(&head_subs);

                let head_type = substitute_type(&head_subs, &fresh);
                let tail_subs = self.infer_expression(&tail, &Type::List(Box::new(head_type.clone())))?;
                self.extend_type_environment(&tail_subs);

                let tail_type = Type::List(Box::new(substitute_type(&tail_subs, &head_type.clone())));
                map_unify(loc.clone(), unify(&tail_type, expected_type))
                    .map(|r| {
                        let mut nr = Vec::new();
                        nr.extend(head_subs);
                        nr.extend(tail_subs);
                        nr.extend(r);
                        nr
                    })?
            }
            Expression::ADTTypeConstructor(loc, name, arguments) => {
                let adt_definition = match self.adt_type_constructor_to_type.get(name) {
                    Some(d) => d.clone(),
                    None => return Err(vec![InferenceError::from_loc(loc.clone(), InferenceErrorType::UndefinedTypeConstructor(name.clone()))]),
                };
                let adt_constructor_definition = adt_definition.constructors.get(name).unwrap();

                if adt_constructor_definition.elements.len() != arguments.len() {
                    return Err(vec![InferenceError::from_loc(loc.clone(), InferenceErrorType::WrongNumberConstructorArguments(name.clone(), adt_constructor_definition.elements.len(), arguments.len()))]);
                }


                /*
                Ok "ONE" 15 :: v0?

                1. Retrieve definition: :: Result a b = Ok String a | Error String b
                2. Instantiate definition type variables:
                    :: Result v1 v2 = Ok String v1 | Error String v2

                    [(a, v1), (b, v2)]
                3. For every constructor argument:
                    "ONE":
                        a. Generate fresh variable f0
                        b. Infer expression with that variable
                            Subs: [(f0, String]
                        c. Apply substitutions to the variable
                     15:
                        a. Generate fresh variable f1
                        b. Infer expression with that variable
                            Subs: [(f1, Int)]
                4. Collect the type of the arguments:
                    [f0, f1] => [String, Int]
                5. Unify the type of the arguments with the types in the constructor
                    [(v1, Int)]
                6. Apply the substitutions to the ADT type from step 2
                    :: Result Int v2 = Ok String Int | Error String v2
                7. Unify the type with the expected type
                    [(v0, Result Int v2)]
                */
                let mut type_variable_to_type = HashMap::new();
                for v in &adt_definition.type_variables {
                    type_variable_to_type.insert(v.clone(), self.fresh());
                }

                let instantiated_definition_argument_types = substitute_list(&type_variable_to_type.clone().into_iter().collect(), &adt_constructor_definition.elements);

                let mut argument_types = Vec::new();
                for arg in arguments {
                    let fresh = self.fresh();
                    let subs = self.infer_expression(&arg, &fresh)?;
                    self.extend_type_environment(&subs);
                    argument_types.push(substitute_type(&subs, &fresh));
                }

                let mut argument_substitutions = Vec::new();
                for ((l, r), ex) in argument_types.iter().zip(instantiated_definition_argument_types.iter()).zip(arguments.iter()) {
                    let subs = map_unify(ex.locate(), unify(&l, &r))?;
                    self.extend_type_environment(&subs);
                    argument_substitutions.extend(subs);
                }

                type_variable_to_type = type_variable_to_type.iter()
                    .map(|(name, t)| (name.clone(), substitute_type(&argument_substitutions, t))).collect();

                let mut concrete_types = Vec::new();
                for tv in &adt_definition.type_variables {
                    concrete_types.push(type_variable_to_type.get(tv).unwrap().clone());
                }

                map_unify(loc.clone(), unify(&Type::UserType(adt_definition.name.clone(), concrete_types), expected_type))?
            }
            Expression::Record(loc, name, fields) => {
                let record_definition = match self.record_name_to_definition.get(name) {
                    Some(d) => d.clone(),
                    None => return Err(vec![InferenceError::from_loc(loc.clone(), InferenceErrorType::UndefinedRecord(name.clone()))]),
                };

                let mut errors = Vec::new();

                let undefined_fields: Vec<String> = fields.iter()
                    .filter(|(n, _)| !record_definition.fields.contains_key(n))
                    .map(|(n, _)| n.clone())
                    .collect();

                if undefined_fields.len() > 0 {
                    errors.push(InferenceError::from_loc(loc.clone(), InferenceErrorType::UndefinedRecordFields(name.clone(), undefined_fields)))
                }

                let missing_fields: Vec<String> = record_definition.fields.iter()
                    .filter(|(n, _)| !fields.iter().map(|(name, _)| name.clone()).collect::<Vec<String>>().contains(n))
                    .map(|(n, _)| n.clone())
                    .collect();

                if missing_fields.len() > 0 {
                    errors.push(InferenceError::from_loc(loc.clone(), InferenceErrorType::MissingRecordFields(name.clone(), missing_fields)))
                }

                if errors.len() > 0 {
                    return Err(errors);
                }

                let mut type_variable_to_type = HashMap::new();
                for v in &record_definition.type_variables {
                    type_variable_to_type.insert(v.clone(), self.fresh());
                }

                let instantiated_field_definition_types: HashMap<String, Type> = record_definition.fields.iter()
                    .map(|(field_name, field_type)| (field_name.clone(), substitute_type(&type_variable_to_type.clone().into_iter().collect(), field_type)))
                    .collect();

                let mut field_types = Vec::new();
                let mut field_location: HashMap<String, Location> = HashMap::new();
                for (name, expression) in fields {
                    let fresh = self.fresh();
                    let subs = self.infer_expression(&expression, &fresh)?;
                    self.extend_type_environment(&subs);
                    field_types.push((name.clone(), substitute_type(&subs, &fresh)));
                    field_location.insert(name.clone(), expression.locate());
                }

                let mut field_substitutions = Vec::new();
                for (name, inferred_type) in field_types.iter() {
                    let defined_type = instantiated_field_definition_types.get(name).unwrap();
                    let subs = map_unify(field_location.get(name).unwrap().clone(), unify(&inferred_type, defined_type))?;
                    self.extend_type_environment(&subs);
                    field_substitutions.extend(subs);
                }

                type_variable_to_type = type_variable_to_type.iter()
                    .map(|(name, t)| (name.clone(), substitute_type(&field_substitutions, t))).collect();

                let mut concrete_types = Vec::new();
                for tv in &record_definition.type_variables {
                    concrete_types.push(type_variable_to_type.get(tv).unwrap().clone());
                }

                map_unify(loc.clone(), unify(&Type::UserType(record_definition.name.clone(), concrete_types), expected_type))?
            }
            Expression::Call(loc, name, arguments) => {
                let function_type = match self.global_type_context.get(name) {
                    None => return Err(vec![InferenceError::from_loc(loc.clone(), InferenceErrorType::UndefinedFunction(name.clone()))]),
                    Some(ft) => ft.clone(),
                };

                let instantiated_function_type = self.instantiate(&function_type);

                // f :: v0 v0 -> v0
                let mut argument_types = Vec::new();
                let mut arg_subs = Vec::new();
                for a in arguments {
                    let fresh = self.fresh();
                    let subs = self.infer_expression(&a, &fresh)?;
                    self.extend_type_environment(&subs);
                    arg_subs.extend(subs.clone());
                    argument_types = substitute_list(&subs, &argument_types);
                    argument_types.push(substitute_type(&subs, &fresh));
                }

                // FIXME: This reports the wrong error location. Check if instantiated_function_type
                //        is a function, then we can report better errors.. Otherwise we report the error
                //        of unifying the two whole types like now.
                let fresh_result = self.fresh();
                let result_subs = map_unify(loc.clone(), unify(&Type::Function(argument_types, Box::new(fresh_result.clone())), &instantiated_function_type))?;
                self.extend_type_environment(&result_subs);
                let result_type = substitute_type(&result_subs, &fresh_result.clone());


                map_unify(loc.clone(), unify(&result_type, &expected_type))
                    .map(|s| {
                        let mut ns = Vec::new();
                        ns.extend(arg_subs);
                        ns.extend(result_subs);
                        ns.extend(s);
                        ns
                    })?
            }
            Expression::Case(loc, expression, rules) => {
                let fresh = self.fresh();
                let subs = self.infer_expression(expression, &fresh)?;
                self.extend_type_environment(&subs);

                let mut match_type = substitute_type(&subs, &fresh);
                let mut return_type = self.fresh();
                for rule in rules {
                    let subs = self.infer_match_expression(&rule.case_rule, &match_type)?;
                    self.extend_type_environment(&subs);
                    match_type = substitute_type(&subs, &match_type);

                    let subs = self.infer_expression(&rule.result_rule, &return_type)?;
                    self.extend_type_environment(&subs);
                    return_type = substitute_type(&subs, &return_type);
                }

                map_unify(loc.clone(), unify(&return_type, &expected_type))?
            }
        };

        Ok(res)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[cfg(test)]
    mod expression {
        use super::*;

        #[cfg(test)]
        mod simple {
            use super::*;

            #[test]
            fn test_infer_bool() {
                let ast = test_ast();
                let mut state = test_state(&ast);
                let result = state.infer_expression(&Expression::BoolLiteral(test_loc(1), true), &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_ok())
            }

            #[test]
            fn test_infer_char() {
                let ast = test_ast();
                let mut state = test_state(&ast);
                let result = state.infer_expression(&Expression::CharacterLiteral(test_loc(1), 'c'), &Type::Char);
                println!("{:#?}", result);
                assert!(result.is_ok())
            }

            #[test]
            fn test_infer_int() {
                let ast = test_ast();
                let mut state = test_state(&ast);
                let result = state.infer_expression(&Expression::IntegerLiteral(test_loc(1), 123), &Type::Int);
                println!("{:#?}", result);
                assert!(result.is_ok())
            }

            #[test]
            fn test_infer_string() {
                let ast = test_ast();
                let mut state = test_state(&ast);
                let result = state.infer_expression(&Expression::StringLiteral(test_loc(1), "123".to_string()), &Type::String);
                println!("{:#?}", result);
                assert!(result.is_ok())
            }

            #[test]
            fn test_infer_float() {
                let ast = test_ast();
                let mut state = test_state(&ast);
                let result = state.infer_expression(&Expression::FloatLiteral(test_loc(1), 11.23), &Type::Float);
                println!("{:#?}", result);
                assert!(result.is_ok())
            }
        }

        #[cfg(test)]
        mod negation {
            use super::*;

            #[test]
            fn test_infer_negation_1() {
                let ast = test_ast();
                let mut state = test_state(&ast);
                let result = state.infer_expression(&Expression::Negation(test_loc(1), Box::new(Expression::BoolLiteral(test_loc(2), true))), &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_ok())
            }

            #[test]
            fn test_infer_negation_2() {
                let ast = test_ast();
                let mut state = test_state(&ast);
                state.local_type_context.insert("a".to_string(), Type::Variable("y0".to_string()));
                let result = state.infer_expression(&Expression::Negation(test_loc(1), Box::new(Expression::Variable(test_loc(2), "a".to_string()))), &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_ok());
                assert_eq!(&Type::Bool, state.local_type_context.get("a").unwrap())
            }
        }

        #[cfg(test)]
        mod minus {
            use super::*;

            #[test]
            fn test_infer_minus_int() {
                let ast = test_ast();
                let mut state = test_state(&ast);
                let result = state.infer_expression(&Expression::Minus(test_loc(1), Box::new(Expression::IntegerLiteral(test_loc(2), 1))), &Type::Int);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_minus_float() {
                let ast = test_ast();
                let mut state = test_state(&ast);
                let result = state.infer_expression(&Expression::Minus(test_loc(1), Box::new(Expression::FloatLiteral(test_loc(2), 1.1))), &Type::Float);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_minus_error() {
                let ast = test_ast();
                let mut state = test_state(&ast);
                let result = state.infer_expression(&Expression::Minus(test_loc(1), Box::new(Expression::FloatLiteral(test_loc(2), 1.1))), &Type::Int);
                println!("{:#?}", result);
                assert!(result.is_err());
            }
        }

        #[cfg(test)]
        mod times {
            use super::*;

            #[test]
            fn test_infer_times_int() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Times(test_loc(1), Box::new(Expression::IntegerLiteral(test_loc(2), 1)), Box::new(Expression::IntegerLiteral(test_loc(3), 2)));
                let result = state.infer_expression(&e, &Type::Int);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_times_int_err() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Times(test_loc(1), Box::new(Expression::IntegerLiteral(test_loc(2), 1)), Box::new(Expression::IntegerLiteral(test_loc(3), 2)));
                let result = state.infer_expression(&e, &Type::Float);
                println!("{:#?}", result);
                assert!(result.is_err());
            }

            #[test]
            fn test_infer_times_float() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Times(test_loc(1), Box::new(Expression::FloatLiteral(test_loc(2), 1.1)), Box::new(Expression::FloatLiteral(test_loc(3), 2.2)));
                let result = state.infer_expression(&e, &Type::Float);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_times_float_err() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Times(test_loc(1), Box::new(Expression::FloatLiteral(test_loc(2), 1.1)), Box::new(Expression::FloatLiteral(test_loc(3), 2.2)));
                let result = state.infer_expression(&e, &Type::Int);
                println!("{:#?}", result);
                assert!(result.is_err());
            }

            #[test]
            fn test_infer_times_variable() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                state.local_type_context.insert("a".to_string(), Type::Float);
                state.local_type_context.insert("b".to_string(), Type::Float);

                let e = Expression::Times(test_loc(1), Box::new(Expression::Variable(test_loc(2), "a".to_string())), Box::new(Expression::Variable(test_loc(3), "b".to_string())));
                let result = state.infer_expression(&e, &Type::Float);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }
        }

        #[cfg(test)]
        mod divide {
            use super::*;

            #[test]
            fn test_infer_divide_int() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Divide(test_loc(1), Box::new(Expression::IntegerLiteral(test_loc(2), 1)), Box::new(Expression::IntegerLiteral(test_loc(3), 2)));
                let result = state.infer_expression(&e, &Type::Int);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_divide_int_err() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Divide(test_loc(1), Box::new(Expression::IntegerLiteral(test_loc(2), 1)), Box::new(Expression::IntegerLiteral(test_loc(3), 2)));
                let result = state.infer_expression(&e, &Type::Float);
                println!("{:#?}", result);
                assert!(result.is_err());
            }

            #[test]
            fn test_infer_divide_float() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Divide(test_loc(1), Box::new(Expression::FloatLiteral(test_loc(2), 1.1)), Box::new(Expression::FloatLiteral(test_loc(3), 2.2)));
                let result = state.infer_expression(&e, &Type::Float);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_divide_float_err() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Divide(test_loc(1), Box::new(Expression::FloatLiteral(test_loc(2), 1.1)), Box::new(Expression::FloatLiteral(test_loc(3), 2.2)));
                let result = state.infer_expression(&e, &Type::Int);
                println!("{:#?}", result);
                assert!(result.is_err());
            }

            #[test]
            fn test_infer_divide_variable() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                state.local_type_context.insert("a".to_string(), Type::Float);
                state.local_type_context.insert("b".to_string(), Type::Float);

                let e = Expression::Divide(test_loc(1), Box::new(Expression::Variable(test_loc(2), "a".to_string())), Box::new(Expression::Variable(test_loc(3), "b".to_string())));
                let result = state.infer_expression(&e, &Type::Float);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }
        }

        #[cfg(test)]
        mod modulo {
            use super::*;

            #[test]
            fn test_infer_modulo_int() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Modulo(test_loc(1), Box::new(Expression::IntegerLiteral(test_loc(2), 1)), Box::new(Expression::IntegerLiteral(test_loc(3), 2)));
                let result = state.infer_expression(&e, &Type::Int);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_add_modulo_err() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Modulo(test_loc(1), Box::new(Expression::IntegerLiteral(test_loc(2), 1)), Box::new(Expression::IntegerLiteral(test_loc(3), 2)));
                let result = state.infer_expression(&e, &Type::Float);
                println!("{:#?}", result);
                assert!(result.is_err());
            }

            #[test]
            fn test_infer_modulo_float() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Modulo(test_loc(1), Box::new(Expression::FloatLiteral(test_loc(2), 1.1)), Box::new(Expression::FloatLiteral(test_loc(3), 2.2)));
                let result = state.infer_expression(&e, &Type::Float);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_modulo_float_err() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Modulo(test_loc(1), Box::new(Expression::FloatLiteral(test_loc(2), 1.1)), Box::new(Expression::FloatLiteral(test_loc(3), 2.2)));
                let result = state.infer_expression(&e, &Type::Int);
                println!("{:#?}", result);
                assert!(result.is_err());
            }

            #[test]
            fn test_infer_modulo_variable() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                state.local_type_context.insert("a".to_string(), Type::Float);
                state.local_type_context.insert("b".to_string(), Type::Float);

                let e = Expression::Modulo(test_loc(1), Box::new(Expression::Variable(test_loc(2), "a".to_string())), Box::new(Expression::Variable(test_loc(3), "b".to_string())));
                let result = state.infer_expression(&e, &Type::Float);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }
        }

        #[cfg(test)]
        mod add {
            use super::*;

            #[test]
            fn test_infer_add_int() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Add(test_loc(1), Box::new(Expression::IntegerLiteral(test_loc(2), 1)), Box::new(Expression::IntegerLiteral(test_loc(3), 2)));
                let result = state.infer_expression(&e, &Type::Int);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_add_err() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Add(test_loc(1), Box::new(Expression::IntegerLiteral(test_loc(2), 1)), Box::new(Expression::IntegerLiteral(test_loc(3), 2)));
                let result = state.infer_expression(&e, &Type::Float);
                println!("{:#?}", result);
                assert!(result.is_err());
            }

            #[test]
            fn test_infer_add_float() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Add(test_loc(1), Box::new(Expression::FloatLiteral(test_loc(2), 1.1)), Box::new(Expression::FloatLiteral(test_loc(3), 2.2)));
                let result = state.infer_expression(&e, &Type::Float);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_add_float_err() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Add(test_loc(1), Box::new(Expression::FloatLiteral(test_loc(2), 1.1)), Box::new(Expression::FloatLiteral(test_loc(3), 2.2)));
                let result = state.infer_expression(&e, &Type::Int);
                println!("{:#?}", result);
                assert!(result.is_err());
            }

            #[test]
            fn test_infer_add_variable() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                state.local_type_context.insert("a".to_string(), Type::Float);
                state.local_type_context.insert("b".to_string(), Type::Float);

                let e = Expression::Modulo(test_loc(1), Box::new(Expression::Variable(test_loc(2), "a".to_string())), Box::new(Expression::Variable(test_loc(3), "b".to_string())));
                let result = state.infer_expression(&e, &Type::Float);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }
        }

        #[cfg(test)]
        mod subtract {
            use super::*;

            #[test]
            fn test_infer_subtract_int() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Subtract(test_loc(1), Box::new(Expression::IntegerLiteral(test_loc(2), 1)), Box::new(Expression::IntegerLiteral(test_loc(3), 2)));
                let result = state.infer_expression(&e, &Type::Int);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_subtract_err() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Subtract(test_loc(1), Box::new(Expression::IntegerLiteral(test_loc(2), 1)), Box::new(Expression::IntegerLiteral(test_loc(3), 2)));
                let result = state.infer_expression(&e, &Type::Float);
                println!("{:#?}", result);
                assert!(result.is_err());
            }

            #[test]
            fn test_infer_subtract_float() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Subtract(test_loc(1), Box::new(Expression::FloatLiteral(test_loc(2), 1.1)), Box::new(Expression::FloatLiteral(test_loc(3), 2.2)));
                let result = state.infer_expression(&e, &Type::Float);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_subtract_float_err() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Subtract(test_loc(1), Box::new(Expression::FloatLiteral(test_loc(2), 1.1)), Box::new(Expression::FloatLiteral(test_loc(3), 2.2)));
                let result = state.infer_expression(&e, &Type::Int);
                println!("{:#?}", result);
                assert!(result.is_err());
            }

            #[test]
            fn test_infer_subtract_variable() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                state.local_type_context.insert("a".to_string(), Type::Float);
                state.local_type_context.insert("b".to_string(), Type::Float);

                let e = Expression::Subtract(test_loc(1), Box::new(Expression::Variable(test_loc(2), "a".to_string())), Box::new(Expression::Variable(test_loc(3), "b".to_string())));
                let result = state.infer_expression(&e, &Type::Float);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }
        }

        #[cfg(test)]
        mod shift_left {
            use super::*;

            #[test]
            fn test_infer_shift_left_int() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::ShiftLeft(test_loc(1), Box::new(Expression::IntegerLiteral(test_loc(2), 1)), Box::new(Expression::IntegerLiteral(test_loc(3), 2)));
                let result = state.infer_expression(&e, &Type::Int);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_shift_left_int_err() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::ShiftLeft(test_loc(1), Box::new(Expression::IntegerLiteral(test_loc(2), 1)), Box::new(Expression::IntegerLiteral(test_loc(3), 2)));
                let result = state.infer_expression(&e, &Type::Float);
                println!("{:#?}", result);
                assert!(result.is_err());
            }

            #[test]
            fn test_infer_shift_left_variable() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                state.local_type_context.insert("a".to_string(), Type::Int);
                state.local_type_context.insert("b".to_string(), Type::Int);

                let e = Expression::ShiftLeft(test_loc(1), Box::new(Expression::Variable(test_loc(2), "a".to_string())), Box::new(Expression::Variable(test_loc(3), "b".to_string())));
                let result = state.infer_expression(&e, &Type::Int);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }
        }

        #[cfg(test)]
        mod shift_right {
            use super::*;

            #[test]
            fn test_infer_shift_right_int() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::ShiftRight(test_loc(1), Box::new(Expression::IntegerLiteral(test_loc(2), 1)), Box::new(Expression::IntegerLiteral(test_loc(3), 2)));
                let result = state.infer_expression(&e, &Type::Int);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_shift_right_int_err() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::ShiftRight(test_loc(1), Box::new(Expression::IntegerLiteral(test_loc(2), 1)), Box::new(Expression::IntegerLiteral(test_loc(3), 2)));
                let result = state.infer_expression(&e, &Type::Float);
                println!("{:#?}", result);
                assert!(result.is_err());
            }

            #[test]
            fn test_infer_shift_right_variable() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                state.local_type_context.insert("a".to_string(), Type::Int);
                state.local_type_context.insert("b".to_string(), Type::Int);

                let e = Expression::ShiftRight(test_loc(1), Box::new(Expression::Variable(test_loc(2), "a".to_string())), Box::new(Expression::Variable(test_loc(3), "b".to_string())));
                let result = state.infer_expression(&e, &Type::Int);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }
        }

        #[cfg(test)]
        mod greater {
            use super::*;

            #[test]
            fn test_infer_greater_int() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Greater(test_loc(1), Box::new(Expression::IntegerLiteral(test_loc(2), 1)), Box::new(Expression::IntegerLiteral(test_loc(3), 2)));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_greater_float() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Greater(test_loc(1), Box::new(Expression::FloatLiteral(test_loc(2), 1.1)), Box::new(Expression::FloatLiteral(test_loc(3), 2.1)));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_greater_err_operands() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Greater(test_loc(1), Box::new(Expression::FloatLiteral(test_loc(2), 1.1)), Box::new(Expression::IntegerLiteral(test_loc(3), 2)));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_err());
            }

            #[test]
            fn test_infer_greater_err_result() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Greater(test_loc(1), Box::new(Expression::IntegerLiteral(test_loc(2), 1)), Box::new(Expression::IntegerLiteral(test_loc(3), 2)));
                let result = state.infer_expression(&e, &Type::Int);
                println!("{:#?}", result);
                assert!(result.is_err());
            }

            #[test]
            fn test_infer_greater_variable() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                state.local_type_context.insert("a".to_string(), Type::Int);
                state.local_type_context.insert("b".to_string(), Type::Int);

                let e = Expression::Greater(test_loc(1), Box::new(Expression::Variable(test_loc(2), "a".to_string())), Box::new(Expression::Variable(test_loc(3), "b".to_string())));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }
        }

        #[cfg(test)]
        mod greater_or_equal {
            use super::*;

            #[test]
            fn test_infer_greater_or_equal_int() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Greq(test_loc(1), Box::new(Expression::IntegerLiteral(test_loc(2), 1)), Box::new(Expression::IntegerLiteral(test_loc(3), 2)));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_greater_or_equal_float() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Greq(test_loc(1), Box::new(Expression::FloatLiteral(test_loc(2), 1.1)), Box::new(Expression::FloatLiteral(test_loc(3), 2.1)));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_greater_or_equal_err_operands() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Greq(test_loc(1), Box::new(Expression::FloatLiteral(test_loc(2), 1.1)), Box::new(Expression::IntegerLiteral(test_loc(3), 2)));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_err());
            }

            #[test]
            fn test_infer_greater_or_equal_err_result() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Greq(test_loc(1), Box::new(Expression::IntegerLiteral(test_loc(2), 1)), Box::new(Expression::IntegerLiteral(test_loc(3), 2)));
                let result = state.infer_expression(&e, &Type::Int);
                println!("{:#?}", result);
                assert!(result.is_err());
            }

            #[test]
            fn test_infer_greater_or_equal_variable() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                state.local_type_context.insert("a".to_string(), Type::Int);
                state.local_type_context.insert("b".to_string(), Type::Int);

                let e = Expression::Greq(test_loc(1), Box::new(Expression::Variable(test_loc(2), "a".to_string())), Box::new(Expression::Variable(test_loc(3), "b".to_string())));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }
        }

        #[cfg(test)]
        mod lesser_or_equal {
            use super::*;

            #[test]
            fn test_infer_lesser_or_equal_int() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Leq(test_loc(1), Box::new(Expression::IntegerLiteral(test_loc(2), 1)), Box::new(Expression::IntegerLiteral(test_loc(3), 2)));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_lesser_or_equal_float() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Leq(test_loc(1), Box::new(Expression::FloatLiteral(test_loc(2), 1.1)), Box::new(Expression::FloatLiteral(test_loc(3), 2.1)));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_lesser_or_equal_err_operands() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Leq(test_loc(1), Box::new(Expression::FloatLiteral(test_loc(2), 1.1)), Box::new(Expression::IntegerLiteral(test_loc(3), 2)));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_err());
            }

            #[test]
            fn test_infer_lesser_or_equal_err_result() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Leq(test_loc(1), Box::new(Expression::IntegerLiteral(test_loc(2), 1)), Box::new(Expression::IntegerLiteral(test_loc(3), 2)));
                let result = state.infer_expression(&e, &Type::Int);
                println!("{:#?}", result);
                assert!(result.is_err());
            }

            #[test]
            fn test_infer_lesser_or_equal_variable() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                state.local_type_context.insert("a".to_string(), Type::Int);
                state.local_type_context.insert("b".to_string(), Type::Int);

                let e = Expression::Leq(test_loc(1), Box::new(Expression::Variable(test_loc(2), "a".to_string())), Box::new(Expression::Variable(test_loc(3), "b".to_string())));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }
        }

        #[cfg(test)]
        mod lesser {
            use super::*;

            #[test]
            fn test_infer_lesser_int() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Lesser(test_loc(1), Box::new(Expression::IntegerLiteral(test_loc(2), 1)), Box::new(Expression::IntegerLiteral(test_loc(3), 2)));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_lesser_float() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Lesser(test_loc(1), Box::new(Expression::FloatLiteral(test_loc(2), 1.1)), Box::new(Expression::FloatLiteral(test_loc(3), 2.1)));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_lesser_err_operands() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Lesser(test_loc(1), Box::new(Expression::FloatLiteral(test_loc(2), 1.1)), Box::new(Expression::IntegerLiteral(test_loc(3), 2)));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_err());
            }

            #[test]
            fn test_infer_lesser_err_result() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Lesser(test_loc(1), Box::new(Expression::IntegerLiteral(test_loc(2), 1)), Box::new(Expression::IntegerLiteral(test_loc(3), 2)));
                let result = state.infer_expression(&e, &Type::Int);
                println!("{:#?}", result);
                assert!(result.is_err());
            }

            #[test]
            fn test_infer_lesser_variable() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                state.local_type_context.insert("a".to_string(), Type::Int);
                state.local_type_context.insert("b".to_string(), Type::Int);

                let e = Expression::Lesser(test_loc(1), Box::new(Expression::Variable(test_loc(2), "a".to_string())), Box::new(Expression::Variable(test_loc(3), "b".to_string())));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }
        }

        #[cfg(test)]
        mod eq {
            use super::*;

            #[test]
            fn test_infer_eq_int() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Eq(test_loc(1), Box::new(Expression::IntegerLiteral(test_loc(2), 1)), Box::new(Expression::IntegerLiteral(test_loc(3), 2)));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_eq_bool() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Eq(test_loc(1), Box::new(Expression::BoolLiteral(test_loc(2), true)), Box::new(Expression::BoolLiteral(test_loc(3), false)));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_eq_char() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Eq(test_loc(1), Box::new(Expression::CharacterLiteral(test_loc(2), 'c')), Box::new(Expression::CharacterLiteral(test_loc(3), 'b')));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_eq_float() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Eq(test_loc(1), Box::new(Expression::FloatLiteral(test_loc(2), 1.1)), Box::new(Expression::FloatLiteral(test_loc(3), 2.1)));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_eq_string() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Eq(test_loc(1), Box::new(Expression::StringLiteral(test_loc(2), "bla".to_string())), Box::new(Expression::StringLiteral(test_loc(3), "blie".to_string())));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_eq_err() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Eq(test_loc(1), Box::new(Expression::StringLiteral(test_loc(2), "bla".to_string())), Box::new(Expression::BoolLiteral(test_loc(3), true)));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_err());
            }
        }

        #[cfg(test)]
        mod neq {
            use super::*;

            #[test]
            fn test_infer_neq_int() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Eq(test_loc(1), Box::new(Expression::IntegerLiteral(test_loc(2), 1)), Box::new(Expression::IntegerLiteral(test_loc(3), 2)));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_neq_bool() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Eq(test_loc(1), Box::new(Expression::BoolLiteral(test_loc(2), true)), Box::new(Expression::BoolLiteral(test_loc(3), false)));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_neq_char() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Neq(test_loc(1), Box::new(Expression::CharacterLiteral(test_loc(2), 'c')), Box::new(Expression::CharacterLiteral(test_loc(3), 'b')));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_neq_float() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Neq(test_loc(1), Box::new(Expression::FloatLiteral(test_loc(2), 1.1)), Box::new(Expression::FloatLiteral(test_loc(3), 2.1)));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_neq_string() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Neq(test_loc(1), Box::new(Expression::StringLiteral(test_loc(2), "bla".to_string())), Box::new(Expression::StringLiteral(test_loc(3), "blie".to_string())));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_neq_err() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Neq(test_loc(1), Box::new(Expression::StringLiteral(test_loc(2), "bla".to_string())), Box::new(Expression::BoolLiteral(test_loc(3), true)));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_err());
            }
        }

        #[cfg(test)]
        mod and {
            use super::*;

            #[test]
            fn test_infer_and() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::And(test_loc(1), Box::new(Expression::BoolLiteral(test_loc(2), true)), Box::new(Expression::BoolLiteral(test_loc(3), false)));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_and_err_operands() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::And(test_loc(1), Box::new(Expression::FloatLiteral(test_loc(2), 1.1)), Box::new(Expression::IntegerLiteral(test_loc(3), 2)));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_err());
            }

            #[test]
            fn test_infer_and_err_result() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::And(test_loc(1), Box::new(Expression::BoolLiteral(test_loc(2), true)), Box::new(Expression::BoolLiteral(test_loc(3), false)));
                let result = state.infer_expression(&e, &Type::Int);
                println!("{:#?}", result);
                assert!(result.is_err());
            }

            #[test]
            fn test_infer_and_variable() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                state.local_type_context.insert("a".to_string(), Type::Bool);
                state.local_type_context.insert("b".to_string(), Type::Bool);

                let e = Expression::And(test_loc(1), Box::new(Expression::Variable(test_loc(2), "a".to_string())), Box::new(Expression::Variable(test_loc(3), "b".to_string())));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }
        }

        #[cfg(test)]
        mod or {
            use super::*;

            #[test]
            fn test_infer_or() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Or(test_loc(1), Box::new(Expression::BoolLiteral(test_loc(2), true)), Box::new(Expression::BoolLiteral(test_loc(3), false)));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_or_err_operands() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Or(test_loc(1), Box::new(Expression::FloatLiteral(test_loc(2), 1.1)), Box::new(Expression::IntegerLiteral(test_loc(3), 2)));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_err());
            }

            #[test]
            fn test_infer_or_err_result() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                let e = Expression::Or(test_loc(1), Box::new(Expression::BoolLiteral(test_loc(2), true)), Box::new(Expression::BoolLiteral(test_loc(3), false)));
                let result = state.infer_expression(&e, &Type::Int);
                println!("{:#?}", result);
                assert!(result.is_err());
            }

            #[test]
            fn test_infer_or_variable() {
                let ast = test_ast();
                let mut state = test_state(&ast);

                state.local_type_context.insert("a".to_string(), Type::Bool);
                state.local_type_context.insert("b".to_string(), Type::Bool);

                let e = Expression::Or(test_loc(1), Box::new(Expression::Variable(test_loc(2), "a".to_string())), Box::new(Expression::Variable(test_loc(3), "b".to_string())));
                let result = state.infer_expression(&e, &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }
        }

        #[cfg(test)]
        mod tuple {
            use super::*;

            #[test]
            fn test_infer_tuple_1() {
                let ast = test_ast();
                let mut state = test_state(&ast);
                let expression = Expression::TupleLiteral(test_loc(1), vec![Expression::IntegerLiteral(test_loc(2), 123), Expression::BoolLiteral(test_loc(3), true)]);

                let result = state.infer_expression(&expression, &Type::Variable("a".to_string()));
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_tuple_2() {
                let ast = test_ast();
                let mut state = test_state(&ast);
                let expression = Expression::TupleLiteral(test_loc(1), vec![Expression::IntegerLiteral(test_loc(2), 123), Expression::BoolLiteral(test_loc(3), true)]);
                let etype = Type::Tuple(vec![Type::Variable("a".to_string()), Type::Variable("b".to_string())]);

                let result = state.infer_expression(&expression, &etype);
                println!("{:#?}", result);
                assert!(result.is_ok());
                let map = &result.unwrap();
            }
        }

        #[cfg(test)]
        mod list {
            use super::*;

            #[test]
            fn test_infer_list_1() {
                let ast = test_ast();
                let mut state = test_state(&ast);
                let expression = Expression::EmptyListLiteral(test_loc(1));
                let etype = Type::List(Box::new(Type::Int));

                let result = state.infer_expression(&expression, &etype);
                println!("{:#?}", result);
                assert!(result.is_ok())
            }

            #[test]
            fn test_infer_list_2() {
                let ast = test_ast();
                let mut state = test_state(&ast);
                let expression = Expression::ShorthandListLiteral(test_loc(1), vec![Expression::BoolLiteral(test_loc(2), true)]);
                let etype = Type::List(Box::new(Type::Bool));

                let result = state.infer_expression(&expression, &etype);
                println!("{:#?}", result);
                assert!(result.is_ok())
            }

            #[test]
            fn test_infer_list_3() {
                let ast = test_ast();
                let mut state = test_state(&ast);
                let expression = Expression::ShorthandListLiteral(test_loc(1), vec![Expression::BoolLiteral(test_loc(2), true)]);
                let etype = Type::List(Box::new(Type::Variable("a".to_string())));

                let result = state.infer_expression(&expression, &etype);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_list_4() {
                let ast = test_ast();
                let mut state = test_state(&ast);
                let expression = Expression::ShorthandListLiteral(test_loc(1), vec![Expression::BoolLiteral(test_loc(2), true)]);
                let etype = Type::Variable("a".to_string());

                let result = state.infer_expression(&expression, &etype);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_list_5() {
                let ast = test_ast();
                let mut state = test_state(&ast);
                let expression = Expression::LonghandListLiteral(test_loc(1), Box::new(Expression::BoolLiteral(test_loc(2), true)), Box::new(Expression::EmptyListLiteral(test_loc(3))));
                let etype = Type::Variable("a".to_string());

                let result = state.infer_expression(&expression, &etype);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }
        }

        #[cfg(test)]
        mod adt {
            use super::*;

            /*
            Tests the following code:

            :: Test = A Bool | B Int

            Is "A true" valid?
            */
            #[test]
            fn test_infer_adt_1() {
                let mut ast = test_ast();
                ast.type_declarations = vec![CustomType::ADT(test_loc(1), ADTDefinition {
                    name: "TEST".to_string(),
                    type_variables: vec![],
                    constructors: vec![
                        ("A".to_string(), ADTConstructor { name: "A".to_string(), elements: vec![Type::Bool] }),
                        ("B".to_string(), ADTConstructor { name: "B".to_string(), elements: vec![Type::Int] })
                    ].into_iter().collect(),
                })];


                let mut state = test_state(&ast);
                let expression = Expression::ADTTypeConstructor(test_loc(1), "A".to_string(), vec![Expression::BoolLiteral(test_loc(2), true)]);
                let etype = Type::Variable("a".to_string());

                let result = state.infer_expression(&expression, &etype);
                println!("{:#?}", result);
                assert!(result.is_ok());
                let result = result.unwrap();
            }

            /*
            Tests the following code:

            :: Test a b = A a | B b

            Is "A true" valid?
            */
            #[test]
            fn test_infer_adt_2_bool() {
                let mut ast = test_ast();
                ast.type_declarations = vec![CustomType::ADT(test_loc(1), ADTDefinition {
                    name: "TEST".to_string(),
                    type_variables: vec!["a".to_string(), "b".to_string()],
                    constructors: vec![
                        ("A".to_string(), ADTConstructor { name: "A".to_string(), elements: vec![Type::Variable("a".to_string())] }),
                        ("B".to_string(), ADTConstructor { name: "B".to_string(), elements: vec![Type::Variable("b".to_string())] })
                    ].into_iter().collect(),
                })];


                let mut state = test_state(&ast);
                let expression = Expression::ADTTypeConstructor(test_loc(2), "A".to_string(), vec![Expression::BoolLiteral(test_loc(3), true)]);
                let etype = Type::Variable("a".to_string());

                let result = state.infer_expression(&expression, &etype);
                println!("{:#?}", result);
                assert!(result.is_ok());
                let result = result.unwrap();
                assert_eq!(&("a".to_string(), Type::UserType("TEST".to_string(), vec![Type::Bool, Type::Variable("v2".to_string())])), result.get(0).unwrap());
            }

            /*
            Tests the following code:

            :: Test a b = A a | B b

            Is "B "test"" valid?
            */
            #[test]
            fn test_infer_adt_2_string() {
                let mut ast = test_ast();
                ast.type_declarations = vec![CustomType::ADT(test_loc(1), ADTDefinition {
                    name: "TEST".to_string(),
                    type_variables: vec!["a".to_string(), "b".to_string()],
                    constructors: vec![
                        ("A".to_string(), ADTConstructor { name: "A".to_string(), elements: vec![Type::Variable("a".to_string())] }),
                        ("B".to_string(), ADTConstructor { name: "B".to_string(), elements: vec![Type::Variable("b".to_string())] })
                    ].into_iter().collect(),
                })];


                let mut state = test_state(&ast);
                let expression = Expression::ADTTypeConstructor(test_loc(2), "B".to_string(), vec![Expression::StringLiteral(test_loc(3), "test".to_string())]);
                let etype = Type::Variable("a".to_string());

                let result = state.infer_expression(&expression, &etype);
                println!("{:#?}", result);
                assert!(result.is_ok());
                let result = result.unwrap();
                assert_eq!(&("a".to_string(), Type::UserType("TEST".to_string(), vec![Type::Variable("v1".to_string()), Type::String])), result.get(0).unwrap());
            }

            /*
            Tests the following code:

            :: Test a b = A Int a | B String b

            Is A "test" [] valid? => NO!
            */
            #[test]
            fn test_infer_adt_3() {
                let mut ast = test_ast();
                ast.type_declarations = vec![CustomType::ADT(test_loc(1), ADTDefinition {
                    name: "TEST".to_string(),
                    type_variables: vec!["a".to_string(), "b".to_string()],
                    constructors: vec![
                        ("A".to_string(), ADTConstructor { name: "A".to_string(), elements: vec![Type::Int, Type::Variable("a".to_string())] }),
                        ("B".to_string(), ADTConstructor { name: "B".to_string(), elements: vec![Type::String, Type::Variable("b".to_string())] })
                    ].into_iter().collect(),
                })];


                let mut state = test_state(&ast);
                let expression = Expression::ADTTypeConstructor(test_loc(2), "A".to_string(), vec![Expression::StringLiteral(test_loc(3), "test".to_string()), Expression::EmptyListLiteral(test_loc(4))]);
                let etype = Type::Variable("a".to_string());

                let result = state.infer_expression(&expression, &etype);
                println!("{:#?}", result);
                assert!(result.is_err());
            }
        }

        #[cfg(test)]
        mod record {
            use super::*;

            #[test]
            fn test_infer_record_missing_fields() {
                let mut ast = test_ast();
                ast.type_declarations = vec![CustomType::Record(test_loc(1), RecordDefinition {
                    name: "A".to_string(),
                    type_variables: vec![],
                    fields: vec![
                        ("a".to_string(), Type::Int),
                        ("b".to_string(), Type::String)
                    ].into_iter().collect(),
                })];

                let mut state = test_state(&ast);
                println!("State: {:#?}", state.record_name_to_definition);
                let expression = Expression::Record(test_loc(2), "A".to_string(), vec![("a".to_string(), Expression::StringLiteral(test_loc(3), "test".to_string()))]);
                let etype = Type::Variable("a".to_string());

                let result = state.infer_expression(&expression, &etype);
                println!("{:#?}", result);
                assert!(result.is_err());
            }

            #[test]
            fn test_infer_record_missing_undefined_fields() {
                let mut ast = test_ast();
                ast.type_declarations = vec![CustomType::Record(test_loc(1), RecordDefinition {
                    name: "A".to_string(),
                    type_variables: vec![],
                    fields: vec![
                        ("a".to_string(), Type::Int),
                        ("b".to_string(), Type::String)
                    ].into_iter().collect(),
                })];

                let mut state = test_state(&ast);
                let expression = Expression::Record(test_loc(2), "A".to_string(), vec![
                    ("aaa".to_string(), Expression::StringLiteral(test_loc(3), "test".to_string())),
                    ("a".to_string(), Expression::IntegerLiteral(test_loc(4), 1)),
                    ("b".to_string(), Expression::StringLiteral(test_loc(4), "test".to_string()))
                ]);
                let etype = Type::Variable("a".to_string());

                let result = state.infer_expression(&expression, &etype);
                println!("{:#?}", result);
                assert!(result.is_err());
            }

            #[test]
            fn test_infer_record_simple() {
                let mut ast = test_ast();
                ast.type_declarations = vec![CustomType::Record(test_loc(1), RecordDefinition {
                    name: "A".to_string(),
                    type_variables: vec![],
                    fields: vec![
                        ("a".to_string(), Type::Int),
                        ("b".to_string(), Type::String)
                    ].into_iter().collect(),
                })];

                let mut state = test_state(&ast);
                let expression = Expression::Record(test_loc(2), "A".to_string(), vec![
                    ("a".to_string(), Expression::IntegerLiteral(test_loc(3), 1)),
                    ("b".to_string(), Expression::StringLiteral(test_loc(4), "test".to_string()))
                ]);
                let etype = Type::Variable("a".to_string());

                let result = state.infer_expression(&expression, &etype);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_record_variable() {
                let mut ast = test_ast();
                ast.type_declarations = vec![CustomType::Record(test_loc(1), RecordDefinition {
                    name: "A".to_string(),
                    type_variables: vec!["a".to_string()],
                    fields: vec![
                        ("a".to_string(), Type::Variable("a".to_string())),
                        ("b".to_string(), Type::String)
                    ].into_iter().collect(),
                })];

                let mut state = test_state(&ast);
                let expression = Expression::Record(test_loc(2), "A".to_string(), vec![
                    ("a".to_string(), Expression::IntegerLiteral(test_loc(3), 1)),
                    ("b".to_string(), Expression::StringLiteral(test_loc(4), "test".to_string()))
                ]);
                let etype = Type::Variable("y0".to_string());

                let result = state.infer_expression(&expression, &etype);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_record_variable_err() {
                let mut ast = test_ast();
                ast.type_declarations = vec![CustomType::Record(test_loc(1), RecordDefinition {
                    name: "A".to_string(),
                    type_variables: vec!["a".to_string()],
                    fields: vec![
                        ("a".to_string(), Type::Variable("a".to_string())),
                        ("b".to_string(), Type::String)
                    ].into_iter().collect(),
                })];

                let mut state = test_state(&ast);
                let expression = Expression::Record(test_loc(2), "A".to_string(), vec![
                    ("a".to_string(), Expression::IntegerLiteral(test_loc(3), 1)),
                    ("b".to_string(), Expression::CharacterLiteral(test_loc(4), 'c'))
                ]);
                let etype = Type::Variable("y0".to_string());

                let result = state.infer_expression(&expression, &etype);
                println!("{:#?}", result);
                assert!(result.is_err());
            }
        }

        #[cfg(test)]
        mod call {
            use std::collections::HashSet;

            use super::*;

            #[test]
            fn test_infer_call_simple() {
                let mut ast = test_ast();
                ast.function_declarations = vec![FunctionDeclaration {
                    location: test_loc(1),
                    name: "f".to_string(),
                    function_type: Some(TypeScheme {
                        bound_variables: HashSet::new(),
                        enclosed_type:
                        Type::Function(vec![Type::String, Type::Int], Box::new(Type::Int)),
                    }),
                    function_bodies: vec![],
                }];

                let mut state = test_state(&ast);
                let expression = Expression::Call(test_loc(2), "f".to_string(),
                                                  vec![Expression::StringLiteral(test_loc(3), "Hello".to_string()), Expression::IntegerLiteral(test_loc(4), 15)]);

                let result = state.infer_expression(&expression, &Type::Int);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_call_simple_err() {
                let mut ast = test_ast();
                ast.function_declarations = vec![FunctionDeclaration {
                    location: test_loc(1),
                    name: "f".to_string(),
                    function_type: Some(TypeScheme {
                        bound_variables: HashSet::new(),
                        enclosed_type:
                        Type::Function(vec![Type::String, Type::Int], Box::new(Type::Int)),
                    }),
                    function_bodies: vec![],
                }];

                let mut state = test_state(&ast);
                let expression = Expression::Call(test_loc(2), "f".to_string(),
                                                  vec![Expression::IntegerLiteral(test_loc(3), 15), Expression::StringLiteral(test_loc(4), "Hello".to_string())]);
                let etype = Type::Variable("a".to_string());

                let result = state.infer_expression(&expression, &etype);
                println!("{:#?}", result);
                assert!(result.is_err());
            }

            #[test]
            fn test_infer_call_variable() {
                let mut ast = test_ast();
                ast.function_declarations = vec![FunctionDeclaration {
                    location: test_loc(1),
                    name: "f".to_string(),
                    function_type: Some(TypeScheme {
                        bound_variables: {
                            let mut set = HashSet::new();
                            set.insert("a".to_string());
                            set
                        },
                        enclosed_type:
                        Type::Function(vec![Type::Variable("a".to_string()), Type::Variable("a".to_string())], Box::new(Type::Variable("a".to_string()))),
                    }),
                    function_bodies: vec![],
                }];

                let mut state = test_state(&ast);
                let expression = Expression::Call(test_loc(2), "f".to_string(),
                                                  vec![Expression::IntegerLiteral(test_loc(3), 15), Expression::IntegerLiteral(test_loc(4), 12)]);

                let result = state.infer_expression(&expression, &Type::Int);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_call_variable_err() {
                let mut ast = test_ast();
                ast.function_declarations = vec![FunctionDeclaration {
                    location: test_loc(1),
                    name: "f".to_string(),
                    function_type: Some(TypeScheme {
                        bound_variables: {
                            let mut set = HashSet::new();
                            set.insert("a".to_string());
                            set
                        },
                        enclosed_type:
                        Type::Function(vec![Type::Variable("a".to_string()), Type::Variable("a".to_string())], Box::new(Type::Variable("a".to_string()))),
                    }),
                    function_bodies: vec![],
                }];

                let mut state = test_state(&ast);
                let expression = Expression::Call(test_loc(2), "f".to_string(),
                                                  vec![Expression::IntegerLiteral(test_loc(3), 15), Expression::BoolLiteral(test_loc(4), true)]);

                let result = state.infer_expression(&expression, &Type::Int);
                println!("{:#?}", result);
                assert!(result.is_err());
            }

            #[test]
            fn test_infer_call_variables_err() {
                let mut ast = test_ast();
                ast.function_declarations = vec![FunctionDeclaration {
                    location: test_loc(1),
                    name: "f".to_string(),
                    function_type: Some(TypeScheme {
                        bound_variables: {
                            let mut set = HashSet::new();
                            set.insert("a".to_string());
                            set
                        },
                        enclosed_type:
                        Type::Function(vec![Type::Variable("a".to_string()), Type::Variable("a".to_string())], Box::new(Type::Variable("a".to_string()))),
                    }),
                    function_bodies: vec![],
                }];

                let mut state = test_state(&ast);
                let expression = Expression::Call(test_loc(2), "f".to_string(),
                                                  vec![Expression::IntegerLiteral(test_loc(3), 15), Expression::BoolLiteral(test_loc(4), true)]);

                let result = state.infer_expression(&expression, &Type::Int);
                println!("{:#?}", result);
                assert!(result.is_err());
            }
        }
    }

    #[cfg(test)]
    mod match_expression {
        use super::*;

        #[cfg(test)]
        mod simple {
            use super::*;

            #[test]
            fn test_match_int() {
                let ast = test_ast();
                let mut state = test_state(&ast);
                let result = state.infer_match_expression(&MatchExpression::IntLiteral(test_loc(1), 18), &Type::Int);
                println!("{:#?}", result);
                assert!(result.is_ok())
            }

            #[test]
            fn test_match_char() {
                let ast = test_ast();
                let mut state = test_state(&ast);
                let result = state.infer_match_expression(&MatchExpression::CharLiteral(test_loc(1), 'c'), &Type::Char);
                println!("{:#?}", result);
                assert!(result.is_ok())
            }

            #[test]
            fn test_match_string() {
                let ast = test_ast();
                let mut state = test_state(&ast);
                let result = state.infer_match_expression(&MatchExpression::StringLiteral(test_loc(1), "hello".to_string()), &Type::String);
                println!("{:#?}", result);
                assert!(result.is_ok())
            }

            #[test]
            fn test_match_bool() {
                let ast = test_ast();
                let mut state = test_state(&ast);
                let result = state.infer_match_expression(&MatchExpression::BoolLiteral(test_loc(1), true), &Type::Bool);
                println!("{:#?}", result);
                assert!(result.is_ok())
            }

            #[test]
            fn test_match_identifier() {
                let ast = test_ast();
                let mut state = test_state(&ast);
                let result = state.infer_match_expression(&MatchExpression::Identifier(test_loc(1), "a".to_string()), &Type::Bool);
                println!("{:#?}", result);
                println!("{:#?}", state.local_type_context);
                assert!(result.is_ok())
            }
        }

        #[cfg(test)]
        mod tuple {
            use super::*;

            #[test]
            fn test_infer_match_tuple_simple() {
                let ast = test_ast();
                let mut state = test_state(&ast);
                let result = state.infer_match_expression(&MatchExpression::Tuple(test_loc(1), vec![
                    MatchExpression::IntLiteral(test_loc(2), 18),
                    MatchExpression::BoolLiteral(test_loc(3), true)
                ]), &Type::Tuple(vec![Type::Int, Type::Bool]));

                println!("{:#?}", result);
                assert!(result.is_ok())
            }

            #[test]
            fn test_infer_match_tuple_simple_err() {
                let ast = test_ast();
                let mut state = test_state(&ast);
                let result = state.infer_match_expression(&MatchExpression::Tuple(test_loc(1), vec![
                    MatchExpression::IntLiteral(test_loc(2), 18),
                    MatchExpression::IntLiteral(test_loc(3), 19)
                ]), &Type::Tuple(vec![Type::Int, Type::Bool]));

                println!("{:#?}", result);
                assert!(result.is_err())
            }

            #[test]
            fn test_infer_match_tuple_variable() {
                let ast = test_ast();
                let mut state = test_state(&ast);
                let result = state.infer_match_expression(&MatchExpression::Tuple(test_loc(1), vec![
                    MatchExpression::IntLiteral(test_loc(2), 18),
                    MatchExpression::IntLiteral(test_loc(3), 19)
                ]), &Type::Variable("a".to_string()));

                println!("{:#?}", result);
                assert!(result.is_ok());

                let result = result.unwrap();
                assert_eq!(result.get(0).unwrap(), &("a".to_string(), Type::Tuple(vec![Type::Int, Type::Int])));
            }
        }

        #[cfg(test)]
        mod shorthand_list {
            use super::*;

            #[test]
            fn test_infer_match_list_simple() {
                let ast = test_ast();
                let mut state = test_state(&ast);
                let result = state.infer_match_expression(&MatchExpression::ShorthandList(test_loc(1), vec![
                    MatchExpression::IntLiteral(test_loc(2), 18),
                    MatchExpression::IntLiteral(test_loc(3), 19)
                ]), &Type::List(Box::new(Type::Int)));

                println!("{:#?}", result);
                assert!(result.is_ok())
            }

            #[test]
            fn test_infer_match_list_simple_err() {
                let ast = test_ast();
                let mut state = test_state(&ast);
                let result = state.infer_match_expression(&MatchExpression::ShorthandList(test_loc(1), vec![
                    MatchExpression::IntLiteral(test_loc(2), 18),
                    MatchExpression::BoolLiteral(test_loc(3), true)
                ]), &Type::List(Box::new(Type::Int)));

                println!("{:#?}", result);
                assert!(result.is_err())
            }

            #[test]
            fn test_infer_match_list_simple_err_return() {
                let ast = test_ast();
                let mut state = test_state(&ast);
                let result = state.infer_match_expression(&MatchExpression::ShorthandList(test_loc(1), vec![
                    MatchExpression::IntLiteral(test_loc(2), 18),
                    MatchExpression::IntLiteral(test_loc(3), 19)
                ]), &Type::List(Box::new(Type::Bool)));

                println!("{:#?}", result);
                assert!(result.is_err())
            }
        }

        #[cfg(test)]
        mod longhand_list {
            use super::*;

            #[test]
            fn test_infer_match_list_simple() {
                let ast = test_ast();
                let mut state = test_state(&ast);
                let result = state.infer_match_expression(
                    &MatchExpression::LonghandList(test_loc(1),
                                                   Box::new(MatchExpression::IntLiteral(test_loc(2), 18)),
                                                   Box::new(MatchExpression::LonghandList(test_loc(3),
                                                                                          Box::new(MatchExpression::IntLiteral(test_loc(4), 19)),
                                                                                          Box::new(MatchExpression::ShorthandList(test_loc(5), vec![]))))),
                    &Type::List(Box::new(Type::Int)));

                println!("{:#?}", result);
                assert!(result.is_ok())
            }

            #[test]
            fn test_infer_match_list_simple_err() {
                let ast = test_ast();
                let mut state = test_state(&ast);
                let result = state.infer_match_expression(
                    &MatchExpression::LonghandList(test_loc(1),
                                                   Box::new(MatchExpression::IntLiteral(test_loc(2), 18)),
                                                   Box::new(MatchExpression::LonghandList(test_loc(3),
                                                                                          Box::new(MatchExpression::BoolLiteral(test_loc(4), true)),
                                                                                          Box::new(MatchExpression::ShorthandList(test_loc(5), vec![]))))),
                    &Type::List(Box::new(Type::Int)));

                println!("{:#?}", result);
                assert!(result.is_err())
            }

            #[test]
            fn test_infer_match_list_simple_err_return() {
                let ast = test_ast();
                let mut state = test_state(&ast);
                let result = state.infer_match_expression(
                    &MatchExpression::LonghandList(test_loc(1),
                                                   Box::new(MatchExpression::IntLiteral(test_loc(2), 18)),
                                                   Box::new(MatchExpression::LonghandList(test_loc(3),
                                                                                          Box::new(MatchExpression::IntLiteral(test_loc(4), 19)),
                                                                                          Box::new(MatchExpression::ShorthandList(test_loc(5), vec![]))))),
                    &Type::List(Box::new(Type::Bool)));

                println!("{:#?}", result);
                assert!(result.is_err())
            }
        }

        #[cfg(test)]
        mod adt {
            use super::*;

            #[test]
            fn test_infer_record_missing_fields() {
                let mut ast = test_ast();
                ast.type_declarations = vec![CustomType::Record(test_loc(1), RecordDefinition {
                    name: "A".to_string(),
                    type_variables: vec![],
                    fields: vec![
                        ("a".to_string(), Type::Int),
                        ("b".to_string(), Type::String)
                    ].into_iter().collect(),
                })];

                let mut state = test_state(&ast);
                println!("State: {:#?}", state.record_name_to_definition);
                let expression = Expression::Record(test_loc(2), "A".to_string(), vec![("a".to_string(), Expression::StringLiteral(test_loc(3), "test".to_string()))]);
                let etype = Type::Variable("a".to_string());

                let result = state.infer_expression(&expression, &etype);
                println!("{:#?}", result);
                assert!(result.is_err());
            }
        }

        #[cfg(test)]
        mod record {
            use super::*;

            #[test]
            fn test_infer_record_undefined_field() {
                let mut ast = test_ast();
                ast.type_declarations = vec![CustomType::Record(test_loc(1), RecordDefinition {
                    name: "A".to_string(),
                    type_variables: vec![],
                    fields: vec![].into_iter().collect(),
                })];

                let mut state = test_state(&ast);
                let expression = MatchExpression::Record(test_loc(2), "A".to_string(), vec!["a".to_string()]);
                let etype = Type::Variable("a".to_string());

                let result = state.infer_match_expression(&expression, &etype);
                println!("{:#?}", result);
                assert!(result.is_err());
            }

            #[test]
            fn test_infer_record_simple() {
                let mut ast = test_ast();
                ast.type_declarations = vec![CustomType::Record(test_loc(1), RecordDefinition {
                    name: "A".to_string(),
                    type_variables: vec![],
                    fields: vec![("a".to_string(), Type::Int)].into_iter().collect(),
                })];

                let mut state = test_state(&ast);
                let expression = MatchExpression::Record(test_loc(2), "A".to_string(), vec!["a".to_string()]);
                let etype = Type::Variable("a".to_string());

                let result = state.infer_match_expression(&expression, &etype);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }

            #[test]
            fn test_infer_record_variable() {
                let mut ast = test_ast();
                ast.type_declarations = vec![CustomType::Record(test_loc(1), RecordDefinition {
                    name: "A".to_string(),
                    type_variables: vec!["c".to_string()],
                    fields: vec![("a".to_string(), Type::Variable("c".to_string()))].into_iter().collect(),
                })];

                let mut state = test_state(&ast);
                let expression = MatchExpression::Record(test_loc(2), "A".to_string(), vec!["a".to_string()]);
                let etype = Type::Variable("a".to_string());

                let result = state.infer_match_expression(&expression, &etype);
                println!("{:#?}", result);
                assert!(result.is_ok());
            }
        }
    }

    fn test_state(ast: &AST) -> InferencerState {
        InferencerState {
            main: &ast.main,
            adt_type_constructor_to_type: build_adt_cache(&ast.type_declarations),
            record_name_to_definition: build_record_cache(&ast.type_declarations),
            type_variable_iterator: Box::new(VariableNameStream { n: 1 }),
            global_type_context: build_function_scheme_cache(&ast.function_declarations),
            local_type_context: HashMap::new(),
        }
    }

    fn test_loc(n: usize) -> Location {
        Location {
            file: "TEST".to_string(),
            function: "TEST".to_string(),
            line: n,
            col: n,
        }
    }

    fn test_ast() -> AST {
        AST {
            function_declarations: vec![],
            type_declarations: vec![],
            main: Expression::IntegerLiteral(test_loc(0), 1),
        }
    }
}


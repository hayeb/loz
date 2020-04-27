use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Error, Formatter};
use std::iter;

use crate::{
    ADTDefinition, Expression, FunctionDefinition, FunctionRule, Location,
    MatchExpression, Module, RecordDefinition, Type, TypeScheme, TypeVar,
};
use crate::inferencer::substitutor::{substitute, substitute_list, substitute_type};
use crate::inferencer::unifier::{unify, unify_one_of};

mod grapher;
mod substitutor;
mod unifier;

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
    UndefinedType(String),

    OperatorArgumentTypesNotEqual(String, Type, Type),
    CannotCompareFunctions(String, Type),

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

    ExpectedRecordType(Type),
    ExpectedRecordFieldAccessor(Type),

    UndefinedVariable(String),

    MissingMainFunction,
}

#[derive(Debug)]
pub struct TypedModule {
    pub module_name: String,
    pub module_file_name: String,
    pub function_name_to_declaration: HashMap<String, FunctionDefinition>,
    pub adt_name_to_definition: HashMap<String, ADTDefinition>,
    pub record_name_to_definition: HashMap<String, RecordDefinition>,
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
        use InferenceErrorType::*;
        write_error_context(f, &self.context)?;
        match &self.err {
            UnificationError(a, b) => write!(f, "Could not unify expected type\n\t{}\nwith inferred type\n\t{}", b, a),
            UnificationErrorMultiple(a, b) => write!(f, "Could not unify one of \n\t{}\nwith inferred type\n\t{}", a.into_iter().map(|a| a.to_string()).collect::<Vec<String>>().join(", "), b),
            UnboundTypeVariable(v) => write!(f, "Unbound type variable '{}'", v),
            WrongNumberOfTypes(left, right) => write!(f, "Expected {} types, got {}", left, right),

            FunctionDeclaredTypeMismatch(declared, derived) => write!(f, "Declared type\n\t{}\nnot equal to inferred type\n\t{}", declared, derived),
            FunctionDerivedTypeMismatch(expected, derived, location_derived) => write!(f, "Derived type from previous body at line {}\n\t{}\ncould not be unified with current derived body type\n\t{}", location_derived.line, expected, derived),

            FunctionMultiplyDefined(name, location) => write!(f, "Function {} already defined, encountered earlier at {}", name, location),
            UndefinedFunction(name) => write!(f, "Function {} undefined", name),
            UndefinedType(name) => write!(f, "Type {} undefined", name),

            OperatorArgumentTypesNotEqual(name, left_type, right_type)
            => write!(f, "Operator '{}' argument types not equal.\n\tLeft:  {}\n\tRight: {}", name, left_type, right_type),
            CannotCompareFunctions(operator_name, argument_type)
            => write!(f, "Operator {} cannot compare function types {}", operator_name, argument_type),

            TypeMultiplyDefined(name, location) => write!(f, "Type {} already defined, encountered earlier at {}", name, location),
            TypeConstructorMultiplyDefined(constructor_name, defined_in_type, defined_in_location) => write!(f, "Type constructor {} already defined in type {} at {}", constructor_name, defined_in_type, defined_in_location),
            // ADT
            UndefinedTypeConstructor(name) => write!(f, "Undefined type constructor {}", name),
            WrongNumberConstructorArguments(name, expected, got) => write!(f, "Expected {} arguments to type constructor {}, got {}", expected, name, got),

            // Record
            UndefinedRecord(name) => write!(f, "Record with name {} is not defined", name),

            UndefinedRecordFields(name, undefined_fields) if undefined_fields.len() == 1
            => write!(f, "Field {} is not defined in record {}", undefined_fields.join(","), name),
            UndefinedRecordFields(name, undefined_fields)
            => write!(f, "Fields [{}] are not defined in record {}", undefined_fields.join(","), name),

            MissingRecordFields(name, missing_fields_values) if missing_fields_values.len() == 1
            => write!(f, "Field {} is missing a value in record {}", missing_fields_values.join(","), name),
            MissingRecordFields(name, missing_fields_values)
            => write!(f, "Fields [{}] are missing a value in record {}", missing_fields_values.join(","), name),

            ExpectedRecordType(got)
            => write!(f, "Expected record type on LHS of '.', got {}", got),

            ExpectedRecordFieldAccessor(got)
            => write!(f, "Expected record field accessor on RLHS of '.', got {}", got),

            UndefinedVariable(name) => write!(f, "Variable {} is not defined", name),

            MissingMainFunction => write!(f, "Missing main function")
        }
    }
}

fn write_error_context(f: &mut Formatter<'_>, context: &ErrorContext) -> Result<(), Error> {
    if context.function.is_empty() {
        write!(f, "{}@[{}:{}]:\n", context.file, context.line, context.col)
    } else {
        write!(
            f,
            "{}::{}@[{}:{}]:\n",
            context.file, context.function, context.line, context.col
        )
    }
}

#[derive(Debug)]
pub struct InferencerResult {}

struct VariableNameStream {
    n: usize,
}

impl Iterator for VariableNameStream {
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {
        let i = self.n;
        self.n += 1;
        Some(format!("v{}", i.to_string()))
    }
}

#[derive(Clone)]
pub struct InferencerOptions {
    pub print_types: bool,
    pub is_main_module: bool,
}

struct InferencerState<'a> {
    type_variable_iterator: Box<dyn Iterator<Item=String>>,
    options: InferencerOptions,

    frames: Vec<InferencerFrame<'a>>,
}

#[derive(Debug)]
struct InferencerFrame<'a> {
    adt_name_to_definition: HashMap<String, &'a ADTDefinition>,
    record_name_to_definition: HashMap<String, &'a RecordDefinition>,
    type_scheme_context: HashMap<String, TypeScheme>,
}

#[derive(Debug)]
pub struct ExternalDefinitions {
    pub adt_name_to_definition: HashMap<String, ADTDefinition>,
    pub record_name_to_definition: HashMap<String, RecordDefinition>,
    pub function_name_to_definition: HashMap<String, FunctionDefinition>,
}

pub fn infer(
    module: Module,
    options: InferencerOptions,
    external_definitions: &ExternalDefinitions,
) -> Result<TypedModule, Vec<InferenceError>> {
    let mut infer_state = InferencerState::new(&module, options.clone(), &external_definitions)?;
    let components = grapher::to_components(&module.function_declarations);
    infer_state.infer(module.file_name.clone(), components)?;

    let toplevel_frame = infer_state.frames.first().unwrap();
    Ok(TypedModule {
        module_name: module.name.clone(),
        module_file_name: module.file_name.clone(),
        function_name_to_declaration: module.function_declarations.iter()
            .map(|d| (d.name.clone(), FunctionDefinition {
                function_type: add_inferred_type(&toplevel_frame, &d.name, d.function_type.clone())
                , .. d.clone()
            }))
            .collect(),
        adt_name_to_definition: module.adt_definitions.into_iter()
            .map(|d| (d.name.clone(), d))
            .collect(),
        record_name_to_definition: module.record_definitions.into_iter()
            .map(|d| (d.name.clone(), d))
            .collect(),
    })
}

fn add_inferred_type(toplevel_frame: &InferencerFrame, name: &String, existing_type: Option<TypeScheme>) -> Option<TypeScheme> {
    if let Some(t) = existing_type {
        return Some(t)
    }
    return toplevel_frame.type_scheme_context.get(name).cloned()

}

fn build_function_scheme_cache(
    function_declarations: &Vec<FunctionDefinition>,
    external_definitions: &ExternalDefinitions,
) -> HashMap<String, TypeScheme> {

    function_declarations
        .iter()
        .filter(|d| d.function_type.is_some())
        .map(|d| (d.name.clone(), d.function_type.clone().unwrap()))
        .chain(external_definitions.function_name_to_definition.iter().map(|(d, definition)| (d.clone(), definition.function_type.clone().unwrap())))
        .collect()
}

fn build_adt_cache<'a>(type_declarations: &'a Vec<ADTDefinition>, external_definitions: &'a ExternalDefinitions) -> HashMap<String, &'a ADTDefinition> {
    type_declarations
        .iter()
        .map(|adt| (adt.name.clone(), adt))
        .chain(external_definitions.adt_name_to_definition.iter().map(|(n, d)| (n.clone(), d)))
        .collect()
}

fn build_record_cache<'a>(type_declarations: &'a Vec<RecordDefinition>, external_definitions: &'a ExternalDefinitions) -> HashMap<String, &'a RecordDefinition> {
    type_declarations
        .iter()
        .map(|record| (record.name.clone(), record))
        .chain(external_definitions.record_name_to_definition.iter().map(|(n, d)| (n.clone(), d)))
        .collect()
}

impl<'a> InferencerState<'a> {
    fn new(
        module: &'a Module,
        options: InferencerOptions,
        external_definitions: &'a ExternalDefinitions
    ) -> Result<InferencerState<'a>, Vec<InferenceError>> {
        // 1. Check whether all functions are uniquely defined.
        check_unique_definitions(&module, &external_definitions)?;

        // 2. Register all functions which have a type.
        let function_name_to_type = build_function_scheme_cache(&module.function_declarations, external_definitions);

        // 3. Check whether all called functions are defined
        check_function_calls_defined(
            &module.function_declarations,
            &module.function_declarations
                .iter()
                .map(|d| d.name.clone())
                .chain(external_definitions.function_name_to_definition.keys().cloned())
                .collect(),
        )?;

        // 4. Register all user-defined types.
        let adt_name_to_definition = build_adt_cache(&module.adt_definitions, &external_definitions);

        let record_name_to_definition = build_record_cache(&module.record_definitions, &external_definitions);

        // 5. Check whether al referred types are defined
        let defined_adt_names = (&module
            .adt_definitions)
            .iter()
            .map(|d| d.name.clone())
            .collect();
        let defined_record_names = (&module
            .record_definitions)
            .iter()
            .map(|d| d.name.clone())
            .collect();

        check_type_references_defined(&module.function_declarations, &defined_adt_names, &defined_record_names)?;

        return Ok(InferencerState {
            options,
            type_variable_iterator: Box::new(VariableNameStream { n: 1 }),
            frames: vec![InferencerFrame {
                adt_name_to_definition,
                record_name_to_definition: record_name_to_definition,
                type_scheme_context: function_name_to_type,
            }],
        });
    }
}

fn check_type_references_defined(
    function_declarations: &Vec<FunctionDefinition>,
    defined_adt_names: &HashSet<String>,
    defined_record_names: &HashSet<String>,
) -> Result<(), Vec<InferenceError>> {
    let mut errors = Vec::new();
    for d in function_declarations {
        if let Some(function_type) = &d.function_type {
            let referenced_types = function_type.enclosed_type.referenced_custom_types();
            for referenced_type_name in referenced_types {
                if !defined_adt_names.contains(&referenced_type_name) && !defined_record_names.contains(&referenced_type_name) {
                    errors.push(InferenceError::from_loc(
                        d.location.clone(),
                        InferenceErrorType::UndefinedType(referenced_type_name.clone()),
                    ));
                }
            }
        }

        for b in &d.function_bodies {
            let mut local_adt_definitions: HashSet<String> = (&b.local_adt_definitions)
                .iter()
                .map(|d| d.name.clone())
                .collect();
            local_adt_definitions.extend(defined_adt_names.clone());
            let mut local_record_definitions: HashSet<String> = (&b.local_record_definitions)
                .iter()
                .map(|d| d.name.clone())
                .collect();
            local_record_definitions.extend(defined_record_names.clone());

            let lfd_errors = check_type_references_defined(
                &b.local_function_definitions,
                &local_adt_definitions,
                &local_record_definitions
            );
            if let Err(lfd_errors) = lfd_errors {
                errors.extend(lfd_errors);
            }
        }
    }

    if errors.len() > 0 {
        return Err(errors);
    }
    Ok(())
}

fn check_function_calls_defined(
    declarations: &Vec<FunctionDefinition>,
    defined_functions: &HashSet<String>,
) -> Result<(), Vec<InferenceError>> {
    let mut errors = Vec::new();
    for d in declarations {
        for b in &d.function_bodies {
            let mut defined_variables = HashSet::new();

            for me in &b.match_expressions {
                defined_variables.extend(me.variables());
            }

            let mut local_defined_functions = HashSet::new();

            for d in &b.local_function_definitions {
                defined_variables.insert(d.name.clone());
                local_defined_functions.insert(d.name.clone());
            }

            for f in defined_functions {
                local_defined_functions.insert(f.clone());
            }

            if let Err(errs) = check_function_calls_defined(
                &b.local_function_definitions,
                &local_defined_functions,
            ) {
                errors.extend(errs);
            }

            for r in &b.rules {
                match r {
                    FunctionRule::ConditionalRule(_, cond, result) => {
                        errors.extend(
                            cond.references(false)
                                .into_iter()
                                .filter(|(name, _)| {
                                    !defined_functions.contains(name)
                                        && !defined_variables.contains(name)
                                })
                                .map(|(name, loc)| {
                                    InferenceError::from_loc(
                                        loc,
                                        InferenceErrorType::UndefinedFunction(name.clone()),
                                    )
                                }),
                        );
                        errors.extend(
                            result
                                .references(false)
                                .into_iter()
                                .filter(|(name, _)| {
                                    !defined_functions.contains(name)
                                        && !defined_variables.contains(name)
                                })
                                .map(|(name, loc)| {
                                    InferenceError::from_loc(
                                        loc,
                                        InferenceErrorType::UndefinedFunction(name.clone()),
                                    )
                                }),
                        );
                    }
                    FunctionRule::ExpressionRule(_, expression) => {
                        errors.extend(
                            expression
                                .references(false)
                                .into_iter()
                                .filter(|(name, _)| {
                                    !defined_functions.contains(name)
                                        && !defined_variables.contains(name)
                                })
                                .map(|(name, loc)| {
                                    InferenceError::from_loc(
                                        loc,
                                        InferenceErrorType::UndefinedFunction(name.clone()),
                                    )
                                }),
                        );
                    }
                    FunctionRule::LetRule(_, match_expression, expression) => {
                        defined_variables.extend(match_expression.variables());

                        errors.extend(
                            expression
                                .references(false)
                                .into_iter()
                                .filter(|(name, _)| {
                                    !defined_functions.contains(name)
                                        && !defined_variables.contains(name)
                                })
                                .map(|(name, loc)| {
                                    InferenceError::from_loc(
                                        loc,
                                        InferenceErrorType::UndefinedFunction(name.clone()),
                                    )
                                }),
                        );
                    }
                }
            }
        }
    }
    if errors.len() > 0 {
        return Err(errors);
    }
    Ok(())
}

fn check_unique_definitions(ast: &Module, external_definitions: &ExternalDefinitions) -> Result<(), Vec<InferenceError>> {
    let mut type_errors = Vec::new();

    // 1. Ensure there are no functions multiply defined
    let mut function_names: HashMap<String, Location> = HashMap::new();

    function_names.extend(external_definitions.function_name_to_definition.iter().map(|(name, d)| (name.clone(), d.location.clone())));

    for d in &ast.function_declarations {
        if function_names.contains_key(&d.name) {
            type_errors.push(InferenceError::from_loc(
                d.location.clone(),
                InferenceErrorType::FunctionMultiplyDefined(
                    d.name.clone(),
                    function_names.get(&d.name).unwrap().clone(),
                ),
            ));
        } else {
            function_names.insert(d.name.clone(), d.location.clone());
        }
    }

    // 2. Ensure no ADTs with the same name are defined
    // 3. Ensure all ADT constructors are unique
    // 4. Ensure no records with the same name are defined
    let mut adt_names: HashMap<String, Location> = HashMap::new();
    let mut adt_constructors: HashMap<String, (String, Location)> = HashMap::new();
    for (name, definition) in &external_definitions.adt_name_to_definition {
        adt_names.insert(name.clone(), definition.location.clone());

        for (constructor_name, constructor_definition) in &definition.constructors {
            adt_constructors.insert(constructor_name.clone(), (name.clone(), definition.location.clone()));
        }
    }
    for adt_definition in &ast.adt_definitions {
        // 1. Check whether some other type with this name is defined
        if adt_names.contains_key(&adt_definition.name) {
            type_errors.push(InferenceError::from_loc(
                adt_definition.location.clone(),
                InferenceErrorType::TypeMultiplyDefined(
                    adt_definition.name.clone(),
                    adt_names.get(&adt_definition.name).unwrap().clone(),
                ),
            ));
            continue;
        }

        // 2. Check whether all constructors are uniquely defined
        for (constructor_name, alternative) in &adt_definition.constructors {
            if adt_constructors.contains_key(constructor_name) {
                let (defined_in, defined_in_location) =
                    adt_constructors.get(constructor_name).unwrap();
                type_errors.push(InferenceError::from_loc(
                    adt_definition.location.clone(),
                    InferenceErrorType::TypeConstructorMultiplyDefined(
                        constructor_name.clone(),
                        defined_in.clone(),
                        defined_in_location.clone(),
                    ),
                ))
            } else {
                // 3. Check whether a constructor only uses defined type variables, if any.
                for variable_name in alternative
                    .elements
                    .iter()
                    .flat_map(|e| e.collect_free_type_variables().into_iter())
                {
                    if !adt_definition.type_variables.contains(&variable_name) {
                        type_errors.push(InferenceError::from_loc(
                            adt_definition.location.clone(),
                            InferenceErrorType::UnboundTypeVariable(
                                variable_name.clone(),
                            ),
                        ))
                    }
                }
                adt_constructors.insert(
                    constructor_name.clone(),
                    (adt_definition.name.clone(), adt_definition.location.clone()),
                );
            }
        }

        adt_names.insert(adt_definition.name.clone(), adt_definition.location.clone());
    }

    let mut record_names: HashMap<String, Location> = external_definitions.record_name_to_definition.iter()
        .map(|(n, d)| (n.clone(), d.location.clone()))
        .collect();
    for record_definition in &ast.record_definitions {
        if record_names.contains_key(&record_definition.name) {
            type_errors.push(InferenceError::from_loc(
                record_definition.location.clone(),
                InferenceErrorType::TypeMultiplyDefined(
                    record_definition.name.clone(),
                    record_names.get(&record_definition.name).unwrap().clone(),
                ),
            ));
            continue;
        }
        record_names.insert(record_definition.name.clone(), record_definition.location.clone());
    }

    if type_errors.len() > 0 {
        return Err(type_errors);
    }
    Ok(())
}

fn map_unify(
    loc: Location,
    r: Result<Vec<(TypeVar, Type)>, InferenceErrorType>,
) -> Result<Vec<(TypeVar, Type)>, Vec<InferenceError>> {
    r.map_err(|e| vec![InferenceError::from_loc(loc.clone(), e)])
}

impl<'a> InferencerState<'a> {
    fn fresh(&mut self) -> Type {
        Type::Variable(self.type_variable_iterator.next().unwrap())
    }

    fn add_type(&mut self, name: String, t: Type) {
        self.add_type_scheme(
            name,
            TypeScheme {
                bound_variables: HashSet::new(),
                enclosed_type: t,
            },
        );
    }

    fn get_type(&self, name: &str) -> Option<Type> {
        self.get_type_scheme(name).map(|ts| ts.enclosed_type)
    }

    fn add_type_scheme(&mut self, name: String, ts: TypeScheme) {
        self.frames
            .last_mut()
            .unwrap()
            .type_scheme_context
            .insert(name, ts);
    }

    fn get_type_scheme(&self, name: &str) -> Option<TypeScheme> {
        for frame in self.frames.iter().rev() {
            if frame.type_scheme_context.contains_key(name) {
                return frame.type_scheme_context.get(name).cloned();
            }
        }
        None
    }

    fn get_adt_definition_by_constructor_name(&self, name: &str) -> Option<&ADTDefinition> {
        for frame in self.frames.iter().rev() {
            for (_, adt_def) in frame.adt_name_to_definition.iter() {
                if adt_def.constructors.contains_key(name) {
                    return Some(adt_def);
                }
            }
        }
        None
    }

    fn get_record_definition_by_name(&self, name: &str) -> Option<&RecordDefinition> {
        for frame in self.frames.iter().rev() {
            if let Some(def) = frame.record_name_to_definition.get(name) {
                return Some(def);
            }
        }
        None
    }

    fn add_adt_definition(&mut self, def: &'a ADTDefinition) {
        self.frames
            .last_mut()
            .unwrap()
            .adt_name_to_definition
            .insert(def.name.clone(), def);
    }

    fn add_record_definition(&mut self, def: &'a RecordDefinition) {
        self.frames
            .last_mut()
            .unwrap()
            .record_name_to_definition
            .insert(def.name.clone(), def);
    }

    fn push_frame(&mut self) {
        self.frames.push(InferencerFrame {
            adt_name_to_definition: HashMap::new(),
            record_name_to_definition: HashMap::new(),
            type_scheme_context: HashMap::new(),
        });
    }

    fn pop_frame(&mut self) {
        self.frames.pop();
    }

    fn extend_type_environment(&mut self, with: &Vec<(TypeVar, Type)>) {
        for frame in self.frames.iter_mut() {
            frame.type_scheme_context = frame
                .type_scheme_context
                .iter()
                .map(|(n, t)| (n.clone(), substitutor::substitute(with, &t)))
                .collect();
        }
    }

    fn infer(
        &mut self,
        file_name: String,
        components: Vec<Vec<&'a FunctionDefinition>>,
    ) -> Result<(), Vec<InferenceError>> {
        self.infer_connected_components(components)?;

        if self.options.is_main_module {
            if let None = self.get_type_scheme("main") {
                return Err(vec![InferenceError::from_loc(
                    Location {
                        file: file_name,
                        function: "".to_string(),
                        line: 1,
                        col: 1,
                    },
                    InferenceErrorType::MissingMainFunction,
                )]);
            }
        }

        Ok(())
    }

    fn infer_connected_components<'b>(
        &mut self,
        components: Vec<Vec<&'a FunctionDefinition>>,
    ) -> Result<(), Vec<InferenceError>> {
        for component in components {
            // Generate fresh variables for all declarations in a component
            for d in &component {
                let fresh = self.fresh();
                self.add_type(d.name.clone(), fresh);
            }

            // Infer every declaration
            for d in &component {
                let subs = self.infer_function_declaration(d)?;
                self.extend_type_environment(&subs);
            }

            // Generalize all declarations in a component

            for d in &component {
                let derived_scheme = self.get_type_scheme(&d.name).unwrap();
                let generalized_scheme = self.generalize(derived_scheme.enclosed_type.clone());

                if self.options.print_types {
                    println!(
                        "Type for function '{}': {}",
                        d.name.clone(),
                        generalized_scheme
                    );
                }
                self.add_type_scheme(d.name.clone(), generalized_scheme);
            }
        }
        Ok(())
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

        TypeScheme {
            bound_variables: free,
            enclosed_type: t,
        }
    }

    fn infer_function_declaration(
        &mut self,
        declaration: &'a FunctionDefinition,
    ) -> Result<Vec<(TypeVar, Type)>, Vec<InferenceError>> {
        let mut function_type = self.fresh();
        let mut function_type_location_mutated = declaration.location.clone();

        self.push_frame();

        for body in (&declaration.function_bodies).into_iter() {
            self.push_frame();

            // Infer all arguments. This introduces new variables in the local type context.
            let mut current_match_types = Vec::new();
            let mut current_return_type = self.fresh();
            for me in &body.match_expressions {
                let fresh = self.fresh();
                let subs = self.infer_match_expression(me, &fresh)?;
                self.extend_type_environment(&subs);
                current_match_types = substitute_list(&subs, &current_match_types);
                current_match_types.push(substitute_type(&subs, &fresh));
            }

            for adt_definition in &body.local_adt_definitions {
                self.add_adt_definition(adt_definition)
            }
            for record_definition in &body.local_record_definitions {
                self.add_record_definition(record_definition)
            }

            // TODO: Remove expensive clone?
            let components = grapher::to_components(&body.local_function_definitions);
            self.infer_connected_components(components)?;

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

                        let rhs_type = substitute_type(&subs, &fresh);
                        let subs = self.infer_expression(&expression, &rhs_type)?;
                        self.extend_type_environment(&subs);
                        current_match_types = substitute_list(&subs, &current_match_types);
                        current_return_type = substitute_type(&subs, &current_return_type);
                    }
                }
            }

            self.pop_frame();

            let derived_function_type = if current_match_types.len() > 0 {
                Type::Function(current_match_types, Box::new(current_return_type))
            } else {
                current_return_type
            };

            match unify(&derived_function_type, &function_type) {
                Ok(subs) => {
                    self.extend_type_environment(&subs);
                    let new_function_type = substitute_type(&subs, &function_type);
                    if new_function_type != function_type {
                        function_type_location_mutated = body.location.clone();
                    }
                    function_type = new_function_type;
                }
                Err(_) => {
                    return Err(vec![InferenceError::from_loc(
                        body.location.clone(),
                        InferenceErrorType::FunctionDerivedTypeMismatch(
                            function_type,
                            derived_function_type.clone(),
                            function_type_location_mutated.clone(),
                        ),
                    )]);
                }
            }
        }

        let mut derived_scheme = self.get_type_scheme(&declaration.name).unwrap().clone();

        self.pop_frame();

        let subs = map_unify(
            declaration.location.clone(),
            unify(&derived_scheme.enclosed_type, &function_type),
        )?;
        self.extend_type_environment(&subs);

        if let Some(declared_scheme) = &declaration.function_type {
            derived_scheme = substitute(&subs, &derived_scheme);

            let subs = map_unify(
                declaration.location.clone(),
                unify(
                    &derived_scheme.enclosed_type,
                    &declared_scheme.enclosed_type,
                ),
            )?;
            self.extend_type_environment(&subs);

            let substituted_type = substitute_type(&subs, &declared_scheme.enclosed_type);

            let declared_substituted_scheme = TypeScheme {
                bound_variables: substituted_type.clone().collect_free_type_variables(),
                enclosed_type: substituted_type.clone(),
            };
            if &declared_substituted_scheme != declared_scheme {
                return Err(vec![InferenceError::from_loc(
                    declaration.location.clone(),
                    InferenceErrorType::FunctionDeclaredTypeMismatch(
                        declared_scheme.enclosed_type.clone(),
                        substituted_type.clone(),
                    ),
                )]);
            }
            Ok(Vec::new())
        } else {
            Ok(Vec::new())
        }
    }

    fn infer_match_expression(
        &mut self,
        me: &MatchExpression,
        expected_type: &Type,
    ) -> Result<Vec<(TypeVar, Type)>, Vec<InferenceError>> {
        let subs = match me {
            MatchExpression::IntLiteral(loc, _) => {
                map_unify(loc.clone(), unify(&Type::Int, expected_type))?
            }
            MatchExpression::CharLiteral(loc, _) => {
                map_unify(loc.clone(), unify(&Type::Char, expected_type))?
            }
            MatchExpression::StringLiteral(loc, _) => {
                map_unify(loc.clone(), unify(&Type::String, expected_type))?
            }
            MatchExpression::BoolLiteral(loc, _) => {
                map_unify(loc.clone(), unify(&Type::Bool, expected_type))?
            }

            MatchExpression::Identifier(_, name) => {
                self.add_type(name.clone(), expected_type.clone());
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

                map_unify(
                    loc.clone(),
                    unify(&Type::Tuple(element_types), &expected_type),
                )
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

                let tail_subs =
                    self.infer_match_expression(tail, &Type::List(Box::new(head_type.clone())))?;
                self.extend_type_environment(&tail_subs);

                let tail_type = substitute_type(&tail_subs, &Type::List(Box::new(head_type)));
                map_unify(loc.clone(), unify(&tail_type, &expected_type)).map(|r| {
                    let mut nr = Vec::new();
                    nr.extend(head_subs);
                    nr.extend(tail_subs);
                    nr.extend(r);
                    nr
                })?
            }
            MatchExpression::ADT(loc, constructor_name, constructor_arguments) => {
                let adt_definition = match self
                    .get_adt_definition_by_constructor_name(constructor_name)
                {
                    Some(d) => d.clone(),
                    None => {
                        return Err(vec![InferenceError::from_loc(
                            loc.clone(),
                            InferenceErrorType::UndefinedTypeConstructor(constructor_name.clone()),
                        )]);
                    }
                };
                let adt_constructor_definition =
                    adt_definition.constructors.get(constructor_name).unwrap();

                if adt_constructor_definition.elements.len() != constructor_arguments.len() {
                    return Err(vec![InferenceError::from_loc(
                        loc.clone(),
                        InferenceErrorType::WrongNumberConstructorArguments(
                            constructor_name.clone(),
                            adt_constructor_definition.elements.len(),
                            constructor_arguments.len(),
                        ),
                    )]);
                }

                let mut type_variable_to_type = HashMap::new();
                for v in &adt_definition.type_variables {
                    type_variable_to_type.insert(v.clone(), self.fresh());
                }

                let instantiated_definition_argument_types = substitute_list(
                    &type_variable_to_type.clone().into_iter().collect(),
                    &adt_constructor_definition.elements,
                );

                let mut argument_types = Vec::new();
                let mut union_subs = Vec::new();
                for arg in constructor_arguments {
                    let fresh = self.fresh();
                    let subs = self.infer_match_expression(&arg, &fresh)?;
                    union_subs.extend(subs.clone());
                    argument_types.push(substitute_type(&subs, &fresh));
                }

                let mut argument_substitutions = Vec::new();
                for ((l, r), ex) in argument_types
                    .iter()
                    .zip(instantiated_definition_argument_types.iter())
                    .zip(constructor_arguments.iter())
                {
                    let subs = map_unify(ex.locate(), unify(&l, &r))?;
                    argument_substitutions = subs;
                }

                union_subs.extend(argument_substitutions.clone());

                type_variable_to_type = type_variable_to_type
                    .iter()
                    .map(|(name, t)| (name.clone(), substitute_type(&argument_substitutions, t)))
                    .collect();

                let mut concrete_types = Vec::new();
                for tv in &adt_definition.type_variables {
                    concrete_types.push(type_variable_to_type.get(tv).unwrap().clone());
                }

                map_unify(
                    loc.clone(),
                    unify(
                        &Type::UserType(adt_definition.name.clone(), concrete_types),
                        expected_type,
                    ),
                )?
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

                map_unify(
                    loc.clone(),
                    unify(&Type::List(Box::new(element_type)), expected_type),
                )
                    .map(|mut r| {
                        r.extend(union_subs);
                        r
                    })?
            }

            MatchExpression::Wildcard(_loc) => Vec::new(),
            MatchExpression::Record(loc, name, fields) => {
                let record_definition = match self.get_record_definition_by_name(name) {
                    Some(d) => d.clone(),
                    None => {
                        return Err(vec![InferenceError::from_loc(
                            loc.clone(),
                            InferenceErrorType::UndefinedRecord(name.clone()),
                        )]);
                    }
                };

                let undefined_fields: Vec<String> = fields
                    .into_iter()
                    .filter(|n| !record_definition.fields.contains_key(*n))
                    .map(|n| n.clone())
                    .collect();

                if undefined_fields.len() > 0 {
                    return Err(vec![InferenceError::from_loc(
                        loc.clone(),
                        InferenceErrorType::UndefinedRecordFields(name.clone(), undefined_fields),
                    )]);
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
                    instantiated_field_types.insert(
                        field.clone(),
                        substitute_type(
                            &type_variable_to_type.clone().into_iter().collect(),
                            record_definition.fields.get(field).unwrap(),
                        ),
                    );
                }

                /*
                    Unify with the required type, which might be (Data Int String Int)
                    For instance:
                        v0 -> Int,
                        v1 -> String,
                        v2 -> Int,
                */
                let subs = map_unify(
                    loc.clone(),
                    unify(&Type::UserType(name.clone(), variables), &expected_type),
                )?;

                // For every field used in the match expression, add a variable with the discovered type.
                let mut field_to_type = HashMap::new();
                for (field_name, field_type) in instantiated_field_types {
                    self.add_type(field_name.clone(), substitute_type(&subs, &field_type));
                    field_to_type.insert(field_name.clone(), substitute_type(&subs, &field_type));
                }
                subs
            }
        };
        Ok(subs)
    }

    fn infer_binary_expression(
        &mut self,
        loc: &Location,
        l: &Expression,
        r: &Expression,
        sub_types: &Vec<Type>,
        name: String,
        type_transformer: impl FnOnce(String, &Type, &Type) -> Type,
        expected_type: &Type,
    ) -> Result<Vec<(TypeVar, Type)>, Vec<InferenceError>> {
        let fresh_l = self.fresh();
        let subs_l_1 = self.infer_expression(l, &fresh_l)?;
        self.extend_type_environment(&subs_l_1);

        let l_type = &substitute_type(&subs_l_1, &fresh_l);
        let subs_l_2 = map_unify(l.locate(), unify_one_of(sub_types, l_type))?;
        self.extend_type_environment(&subs_l_2);

        let fresh_r = self.fresh();
        let subs_r_1 = self.infer_expression(r, &fresh_r)?;
        self.extend_type_environment(&subs_r_1);

        let r_type = &substitute_type(&subs_r_1, &fresh_r);
        let subs_r_2 = map_unify(r.locate(), unify_one_of(sub_types, r_type))?;
        self.extend_type_environment(&subs_r_2);

        let l_type = substitute_type(&subs_l_2, l_type);
        let r_type = substitute_type(&subs_r_2, r_type);
        let subs_e = map_unify(loc.clone(), unify(&l_type, &r_type))?;
        self.extend_type_environment(&subs_e);

        let l_type = substitute_type(&subs_e, &l_type);
        let r_type = substitute_type(&subs_e, &r_type);
        map_unify(
            loc.clone(),
            unify(&type_transformer(name, &l_type, &r_type), expected_type),
        )
            .map(|rs| {
                let mut ns = Vec::new();
                ns.extend(subs_l_1);
                ns.extend(subs_l_2);
                ns.extend(subs_r_1);
                ns.extend(subs_r_2);
                ns.extend(subs_e);
                ns.extend(rs);
                ns
            })
    }

    fn infer_expression(
        &mut self,
        e: &Expression,
        expected_type: &Type,
    ) -> Result<Vec<(TypeVar, Type)>, Vec<InferenceError>> {
        let static_type_combinator =
            |result_type: Type| |_, _ltype: &Type, _rtype: &Type| result_type;
        let binary_number_type_combinator =
            |op: String, l_type: &Type, r_type: &Type| match (l_type, r_type) {
                (Type::Int, Type::Int) => Type::Int,
                (Type::Float, Type::Float) => Type::Float,
                t => panic!(
                    "Unable to determine result type for operator '{}': {:#?}",
                    op.clone(),
                    t
                ),
            };
        let res = match e {
            Expression::BoolLiteral(loc, _) => {
                map_unify(loc.clone(), unify(&Type::Bool, &expected_type))?
            }
            Expression::StringLiteral(loc, _) => {
                map_unify(loc.clone(), unify(&Type::String, &expected_type))?
            }
            Expression::CharacterLiteral(loc, _) => {
                map_unify(loc.clone(), unify(&Type::Char, &expected_type))?
            }
            Expression::IntegerLiteral(loc, _) => {
                map_unify(loc.clone(), unify(&Type::Int, &expected_type))?
            }
            Expression::FloatLiteral(loc, _) => {
                map_unify(loc.clone(), unify(&Type::Float, &expected_type))?
            }

            Expression::Negation(loc, e) => {
                let subs = self.infer_expression(e, &Type::Bool)?;
                self.extend_type_environment(&subs);
                map_unify(loc.clone(), unify(&Type::Bool, expected_type)).map(|rs| {
                    let mut ns = Vec::new();
                    ns.extend(subs);
                    ns.extend(rs);
                    ns
                })?
            }

            Expression::Minus(loc, e) => {
                let fresh = self.fresh();
                let s1 = self.infer_expression(e, &fresh)?;
                self.extend_type_environment(&s1);

                let e_type = substitute_type(&s1, &fresh);
                let s2 = map_unify(
                    e.locate(),
                    unify_one_of(&vec![Type::Int, Type::Float], &e_type),
                )?;
                self.extend_type_environment(&s2);

                map_unify(loc.clone(), unify(&e_type, expected_type)).map(|rs| {
                    let mut ns = Vec::new();
                    ns.extend(s1);
                    ns.extend(s2);
                    ns.extend(rs);
                    ns
                })?
            }

            Expression::Times(loc, l, r) => self.infer_binary_expression(
                loc,
                l,
                r,
                &vec![Type::Int, Type::Float],
                "*".to_string(),
                binary_number_type_combinator,
                expected_type,
            )?,

            Expression::Divide(loc, l, r) => self.infer_binary_expression(
                loc,
                l,
                r,
                &vec![Type::Int, Type::Float],
                "/".to_string(),
                binary_number_type_combinator,
                expected_type,
            )?,

            Expression::Modulo(loc, l, r) => self.infer_binary_expression(
                loc,
                l,
                r,
                &vec![Type::Int, Type::Float],
                "%".to_string(),
                binary_number_type_combinator,
                expected_type,
            )?,

            Expression::Add(loc, l, r) => self.infer_binary_expression(
                loc,
                l,
                r,
                &vec![Type::Int, Type::Float],
                "+".to_string(),
                binary_number_type_combinator,
                expected_type,
            )?,

            Expression::Subtract(loc, l, r) => self.infer_binary_expression(
                loc,
                l,
                r,
                &vec![Type::Int, Type::Float],
                "-".to_string(),
                binary_number_type_combinator,
                expected_type,
            )?,

            Expression::ShiftLeft(loc, l, r) => self.infer_binary_expression(
                loc,
                l,
                r,
                &vec![Type::Int],
                "<<".to_string(),
                static_type_combinator(Type::Int),
                expected_type,
            )?,

            Expression::ShiftRight(loc, l, r) => self.infer_binary_expression(
                loc,
                l,
                r,
                &vec![Type::Int],
                ">>".to_string(),
                static_type_combinator(Type::Int),
                expected_type,
            )?,

            Expression::Greater(loc, l, r) => self.infer_binary_expression(
                loc,
                l,
                r,
                &vec![Type::Int, Type::Float],
                ">".to_string(),
                static_type_combinator(Type::Bool),
                expected_type,
            )?,

            Expression::Greq(loc, l, r) => self.infer_binary_expression(
                loc,
                l,
                r,
                &vec![Type::Int, Type::Float],
                ">=".to_string(),
                static_type_combinator(Type::Bool),
                expected_type,
            )?,

            Expression::Leq(loc, l, r) => self.infer_binary_expression(
                loc,
                l,
                r,
                &vec![Type::Int, Type::Float],
                "<=".to_string(),
                static_type_combinator(Type::Bool),
                expected_type,
            )?,

            Expression::Lesser(loc, l, r) => self.infer_binary_expression(
                loc,
                l,
                r,
                &vec![Type::Int, Type::Float],
                "<".to_string(),
                static_type_combinator(Type::Bool),
                expected_type,
            )?,

            Expression::Eq(loc, l, r) => {
                let fresh_l = self.fresh();
                let subs_l = self.infer_expression(l, &fresh_l)?;
                self.extend_type_environment(&subs_l);

                let fresh_r = self.fresh();
                let subs_r = self.infer_expression(r, &fresh_r)?;
                self.extend_type_environment(&subs_r);

                let type_l = substitute_type(&subs_l, &fresh_l);
                let type_r = substitute_type(&subs_r, &fresh_r);

                if let Type::Function(_, _) = type_l {
                    return Err(vec![InferenceError::from_loc(
                        loc.clone(),
                        InferenceErrorType::CannotCompareFunctions("==".to_string(), type_l),
                    )]);
                }

                if let Type::Function(_, _) = type_r {
                    return Err(vec![InferenceError::from_loc(
                        loc.clone(),
                        InferenceErrorType::CannotCompareFunctions("==".to_string(), type_l),
                    )]);
                }

                let subs = match unify(&type_l, &type_r) {
                    Ok(subs) => subs,
                    Err(_unification_error) => {
                        return Err(vec![InferenceError::from_loc(
                            loc.clone(),
                            InferenceErrorType::OperatorArgumentTypesNotEqual(
                                "==".to_string(),
                                type_l,
                                type_r,
                            ),
                        )]);
                    }
                };

                map_unify(loc.clone(), unify(&Type::Bool, expected_type)).map(|nr| {
                    let mut ns = Vec::new();
                    ns.extend(subs_l);
                    ns.extend(subs_r);
                    ns.extend(subs);
                    ns.extend(nr);
                    ns
                })?
            }

            Expression::Neq(loc, l, r) => {
                let fresh_l = self.fresh();
                let subs_l = self.infer_expression(l, &fresh_l)?;
                self.extend_type_environment(&subs_l);

                let fresh_r = self.fresh();
                let subs_r = self.infer_expression(r, &fresh_r)?;
                self.extend_type_environment(&subs_r);

                let type_l = substitute_type(&subs_l, &fresh_l);
                let type_r = substitute_type(&subs_r, &fresh_r);

                if let Type::Function(_, _) = type_l {
                    return Err(vec![InferenceError::from_loc(
                        loc.clone(),
                        InferenceErrorType::CannotCompareFunctions("!=".to_string(), type_l),
                    )]);
                }

                if let Type::Function(_, _) = type_r {
                    return Err(vec![InferenceError::from_loc(
                        loc.clone(),
                        InferenceErrorType::CannotCompareFunctions("!=".to_string(), type_l),
                    )]);
                }

                let subs = match unify(&type_l, &type_r) {
                    Ok(subs) => subs,
                    Err(_unification_error) => {
                        return Err(vec![InferenceError::from_loc(
                            loc.clone(),
                            InferenceErrorType::OperatorArgumentTypesNotEqual(
                                "!=".to_string(),
                                type_l,
                                type_r,
                            ),
                        )]);
                    }
                };
                self.extend_type_environment(&subs);

                map_unify(loc.clone(), unify(&Type::Bool, expected_type)).map(|nr| {
                    let mut ns = Vec::new();
                    ns.extend(subs_l);
                    ns.extend(subs_r);
                    ns.extend(subs);
                    ns.extend(nr);
                    ns
                })?
            }

            Expression::And(loc, l, r) => self.infer_binary_expression(
                loc,
                l,
                r,
                &vec![Type::Bool],
                "&&".to_string(),
                static_type_combinator(Type::Bool),
                expected_type,
            )?,

            Expression::Or(loc, l, r) => self.infer_binary_expression(
                loc,
                l,
                r,
                &vec![Type::Bool],
                "||".to_string(),
                static_type_combinator(Type::Bool),
                expected_type,
            )?,

            Expression::RecordFieldAccess(loc, l, r) => {
                let fresh = self.fresh();
                let subs_lhs = self.infer_expression(l, &fresh)?;
                self.extend_type_environment(&subs_lhs);

                let lhs_type = substitute_type(&subs_lhs, &fresh);
                let (name, _arguments) = match lhs_type {
                    Type::UserType(name, arguments) => (name, arguments),
                    t => {
                        return Err(vec![InferenceError::from_loc(
                            l.locate(),
                            InferenceErrorType::ExpectedRecordType(t),
                        )]);
                    }
                };

                let record_definition = match self.get_record_definition_by_name(&name) {
                    Some(record_definition) => record_definition,
                    None => return Err(vec![]),
                };

                let field = match &**r {
                    Expression::Variable(_, field_name) => field_name,
                    rhs => {
                        let fresh = self.fresh();
                        let subs = self.infer_expression(rhs, &fresh)?;
                        return Err(vec![InferenceError::from_loc(
                            rhs.locate(),
                            InferenceErrorType::ExpectedRecordType(substitute_type(&subs, &fresh)),
                        )]);
                    }
                };

                let field_type = match record_definition.fields.get(field) {
                    Some(field_type) => field_type,
                    None => {
                        return Err(vec![InferenceError::from_loc(
                            r.locate(),
                            InferenceErrorType::UndefinedRecordFields(
                                record_definition.name.clone(),
                                vec![field.clone()],
                            ),
                        )]);
                    }
                };

                map_unify(loc.clone(), unify(&field_type, expected_type))?
            }

            Expression::Variable(loc, name) => {
                let variable_type = match self.get_type(name) {
                    None => {
                        return Err(vec![InferenceError::from_loc(
                            loc.clone(),
                            InferenceErrorType::UndefinedVariable(name.clone()),
                        )]);
                    }
                    Some(vtype) => vtype,
                };

                map_unify(loc.clone(), unify(&variable_type, expected_type))?
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
                map_unify(loc.clone(), unify(&Type::Tuple(types), &expected_type)).map(
                    |mut r| {
                        r.extend(union_subs);
                        r
                    },
                )?
            }
            Expression::EmptyListLiteral(loc) => {
                let fresh = self.fresh();
                map_unify(
                    loc.clone(),
                    unify(&Type::List(Box::new(fresh)), &expected_type),
                )?
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
                map_unify(
                    loc.clone(),
                    unify(&Type::List(Box::new(list_type)), &expected_type),
                )
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
                let tail_subs =
                    self.infer_expression(&tail, &Type::List(Box::new(head_type.clone())))?;
                self.extend_type_environment(&tail_subs);

                let tail_type =
                    Type::List(Box::new(substitute_type(&tail_subs, &head_type.clone())));
                map_unify(loc.clone(), unify(&tail_type, expected_type)).map(|r| {
                    let mut nr = Vec::new();
                    nr.extend(head_subs);
                    nr.extend(tail_subs);
                    nr.extend(r);
                    nr
                })?
            }
            Expression::ADTTypeConstructor(loc, name, arguments) => {
                let adt_definition = match self.get_adt_definition_by_constructor_name(name) {
                    Some(d) => d.clone(),
                    None => {
                        return Err(vec![InferenceError::from_loc(
                            loc.clone(),
                            InferenceErrorType::UndefinedTypeConstructor(name.clone()),
                        )]);
                    }
                };
                let adt_constructor_definition = adt_definition.constructors.get(name).unwrap();

                if adt_constructor_definition.elements.len() != arguments.len() {
                    return Err(vec![InferenceError::from_loc(
                        loc.clone(),
                        InferenceErrorType::WrongNumberConstructorArguments(
                            name.clone(),
                            adt_constructor_definition.elements.len(),
                            arguments.len(),
                        ),
                    )]);
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

                let instantiated_definition_argument_types = substitute_list(
                    &type_variable_to_type.clone().into_iter().collect(),
                    &adt_constructor_definition.elements,
                );

                let mut argument_types = Vec::new();
                let mut union_subs = Vec::new();
                for arg in arguments {
                    let fresh = self.fresh();
                    let subs = self.infer_expression(&arg, &fresh)?;
                    self.extend_type_environment(&subs);
                    union_subs.extend(subs.clone());
                    argument_types.push(substitute_type(&subs, &fresh));
                }

                let mut argument_substitutions = Vec::new();
                for ((l, r), ex) in argument_types
                    .iter()
                    .zip(instantiated_definition_argument_types.iter())
                    .zip(arguments.iter())
                {
                    let subs = map_unify(ex.locate(), unify(&l, &r))?;
                    self.extend_type_environment(&subs);
                    union_subs.extend(subs.clone());
                    argument_substitutions.extend(subs);
                }

                type_variable_to_type = type_variable_to_type
                    .iter()
                    .map(|(name, t)| (name.clone(), substitute_type(&argument_substitutions, t)))
                    .collect();

                let mut concrete_types = Vec::new();
                for tv in &adt_definition.type_variables {
                    concrete_types.push(type_variable_to_type.get(tv).unwrap().clone());
                }

                map_unify(
                    loc.clone(),
                    unify(
                        &Type::UserType(adt_definition.name.clone(), concrete_types),
                        expected_type,
                    ),
                )
                    .map(|rs| {
                        union_subs.extend(rs);
                        union_subs
                    })?
            }
            Expression::Record(loc, name, fields) => {
                let record_definition = match self.get_record_definition_by_name(name) {
                    Some(d) => d.clone(),
                    None => {
                        return Err(vec![InferenceError::from_loc(
                            loc.clone(),
                            InferenceErrorType::UndefinedRecord(name.clone()),
                        )]);
                    }
                };

                let mut errors = Vec::new();

                let undefined_fields: Vec<String> = fields
                    .iter()
                    .filter(|(n, _)| !record_definition.fields.contains_key(n))
                    .map(|(n, _)| n.clone())
                    .collect();

                if undefined_fields.len() > 0 {
                    errors.push(InferenceError::from_loc(
                        loc.clone(),
                        InferenceErrorType::UndefinedRecordFields(name.clone(), undefined_fields),
                    ))
                }

                let missing_fields: Vec<String> = record_definition
                    .fields
                    .iter()
                    .filter(|(n, _)| {
                        !fields
                            .iter()
                            .map(|(name, _)| name.clone())
                            .collect::<Vec<String>>()
                            .contains(n)
                    })
                    .map(|(n, _)| n.clone())
                    .collect();

                if missing_fields.len() > 0 {
                    errors.push(InferenceError::from_loc(
                        loc.clone(),
                        InferenceErrorType::MissingRecordFields(name.clone(), missing_fields),
                    ))
                }

                if errors.len() > 0 {
                    return Err(errors);
                }

                let mut type_variable_to_type = HashMap::new();
                for v in &record_definition.type_variables {
                    type_variable_to_type.insert(v.clone(), self.fresh());
                }

                let instantiated_field_definition_types: HashMap<String, Type> = record_definition
                    .fields
                    .iter()
                    .map(|(field_name, field_type)| {
                        (
                            field_name.clone(),
                            substitute_type(
                                &type_variable_to_type.clone().into_iter().collect(),
                                field_type,
                            ),
                        )
                    })
                    .collect();

                let mut field_types = Vec::new();
                let mut field_location: HashMap<String, Location> = HashMap::new();
                let mut union_subs = Vec::new();
                for (name, expression) in fields {
                    let fresh = self.fresh();
                    let subs = self.infer_expression(&expression, &fresh)?;
                    self.extend_type_environment(&subs);
                    union_subs.extend(subs.clone());
                    field_types.push((name.clone(), substitute_type(&subs, &fresh)));
                    field_location.insert(name.clone(), expression.locate());
                }

                let mut field_substitutions = Vec::new();
                for (name, inferred_type) in field_types.iter() {
                    let defined_type = instantiated_field_definition_types.get(name).unwrap();
                    let subs = map_unify(
                        field_location.get(name).unwrap().clone(),
                        unify(&inferred_type, defined_type),
                    )?;
                    self.extend_type_environment(&subs);
                    field_substitutions.extend(subs);
                }

                type_variable_to_type = type_variable_to_type
                    .iter()
                    .map(|(name, t)| (name.clone(), substitute_type(&field_substitutions, t)))
                    .collect();

                union_subs.extend(field_substitutions);

                let mut concrete_types = Vec::new();
                for tv in &record_definition.type_variables {
                    concrete_types.push(type_variable_to_type.get(tv).unwrap().clone());
                }

                map_unify(
                    loc.clone(),
                    unify(
                        &Type::UserType(record_definition.name.clone(), concrete_types),
                        expected_type,
                    ),
                )
                    .map(|rs| {
                        let mut ns = Vec::new();
                        ns.extend(union_subs);
                        ns.extend(rs);
                        ns
                    })?
            }
            Expression::Call(loc, name, arguments) => {
                let function_type = match self.get_type_scheme(name) {
                    None => {
                        return Err(vec![InferenceError::from_loc(
                            loc.clone(),
                            InferenceErrorType::UndefinedFunction(name.clone()),
                        )]);
                    }
                    Some(ft) => ft,
                };

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

                let instantiated_function_type = self.instantiate(&function_type);

                let defined_number_function_arguments = match &instantiated_function_type {
                    Type::Function(from, _to) => from.len(),
                    _ => 0,
                };

                let fresh_result = self.fresh();
                let result_subs = if defined_number_function_arguments > arguments.len() {
                    // f ::: Int Char Bool -> String
                    // # g = f i // g :: Char Bool String
                    // Currying
                    let (defined_from, defined_to) = match instantiated_function_type {
                        Type::Function(from, to) => (from, to),
                        t => unreachable!("{}", t),
                    };

                    let (l, r) = defined_from.split_at(arguments.len());

                    let curry_adjusted_instantiated_function_type = Type::Function(
                        l.to_vec(),
                        Box::new(Type::Function(r.to_vec(), defined_to)),
                    );

                    map_unify(
                        loc.clone(),
                        unify(
                            &Type::Function(argument_types, Box::new(fresh_result.clone())),
                            &curry_adjusted_instantiated_function_type,
                        ),
                    )?
                } else {
                    map_unify(
                        loc.clone(),
                        unify(
                            &Type::Function(argument_types, Box::new(fresh_result.clone())),
                            &instantiated_function_type,
                        ),
                    )?
                };
                self.extend_type_environment(&result_subs);

                let result_type = substitute_type(&result_subs, &fresh_result.clone());

                map_unify(loc.clone(), unify(&result_type, &expected_type)).map(|s| {
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
            Expression::Lambda(loc, arguments, body) => {
                let mut argument_types = Vec::new();
                let mut union_subs = Vec::new();
                for a in arguments {
                    let fresh = self.fresh();
                    let subs = self.infer_match_expression(a, &fresh)?;
                    self.extend_type_environment(&subs);
                    let match_type = substitute_type(&subs, &fresh);
                    union_subs.extend(subs.clone());
                    argument_types = substitute_list(&subs, &argument_types);
                    argument_types.push(match_type);
                }

                let fresh = self.fresh();
                let subs = self.infer_expression(body, &fresh)?;
                self.extend_type_environment(&subs);
                let return_type = substitute_type(&subs, &fresh);
                argument_types = substitute_list(&subs, &argument_types);

                map_unify(
                    loc.clone(),
                    unify(
                        &Type::Function(argument_types, Box::new(return_type)),
                        &expected_type,
                    ),
                )
                    .map(|rs| {
                        let mut ns = Vec::new();
                        ns.extend(union_subs);
                        ns.extend(subs);
                        ns.extend(rs);
                        ns
                    })?
            }
        };

        Ok(res)
    }
}

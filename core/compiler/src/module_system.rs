use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::PathBuf;
use std::rc::Rc;

use crate::ast::{
    ADTConstructor, ADTDefinition, FunctionDefinition, Import, Location, Module, RecordDefinition,
};
use crate::inferencer::{infer, ExternalDefinitions, InferencerOptions, TypedModule};
use crate::module_system::ModuleErrorType::ModuleNotFound;
use crate::parser;
use crate::parser::parse;

#[derive(Debug)]
pub enum Error {
    FileError(std::io::Error),
    ParseError(Vec<crate::parser::ParseError>),
    InferenceError(Vec<crate::inferencer::InferenceError>),
    ModuleError(Vec<ModuleError>),
}

#[derive(Debug)]
pub struct ModuleError {
    pub location: Rc<Location>,
    pub error: ModuleErrorType,
}

impl ModuleError {
    fn from_loc(loc: &Rc<Location>, e: ModuleErrorType) -> Self {
        return ModuleError {
            location: Rc::clone(loc),
            error: e,
        };
    }
}

#[derive(Debug)]
pub enum ModuleErrorType {
    ModuleNotFound(Rc<String>),

    DefinitionInMultipleImportedModules(
        String,     // Type of definition: Function, record, adt, ...
        Rc<String>, // Name of definition
        Rc<String>, // First module with definition
        Rc<String>, // Current module that also contains the same definition
    ),

    ModuleAliasMultiplyDefined(Rc<String>, Rc<Location>),

    FunctionNotDefinedInModule(Rc<String>, Rc<String>),
    TypeNotDefinedInModule(Rc<String>, Rc<String>),
}

/*
        A -> B, C
        B -> D
        C -> E

        Parse Queue         Infer Queue         Step
        [A]                 []                  Start
        []                  []                  Parsing A
        [B]                 []                  Insert import B to parse stack
        [C, B]              []                  Insert import C to parse stack
        [C, B]              [A]                 Insert A to infer stack
        [C]                 [A]                 Parsing B
        [D, C]              [A]                 Insert import D to parse stack
        [D, C]              [B, A]              Insert B to infer stack
        [D]                 [B, A]              Parsing C
        [E, D]              [B, A]              Insert import E to parse stack
        [E, D]              [C, B, A]           Insert C to infer queue
        [E]                 [C, B, A]           Parsing D
        [E]                 [D, C, B, A]        Insert D to infer queue
        []                  [D, C, B, A]        Parsing E
        []                  [E, D, C, B, A]     Insert E to infer queue
*/

#[derive(Debug, Clone)]
enum ModuleName {
    ModuleName(Rc<String>),
    ModuleFileName(Rc<String>),
}

impl ModuleName {
    fn name(&self) -> Rc<String> {
        match self {
            ModuleName::ModuleName(n) => Rc::clone(n),
            ModuleName::ModuleFileName(n) => {
                let pb = PathBuf::from(n.to_string());
                return Rc::new(String::from(pb.file_stem().unwrap().to_str().unwrap()));
            }
        }
    }
}

pub struct CompilerOptions {
    pub current_directory: PathBuf,
    pub loz_home: PathBuf,

    pub extra_module_search_path: Vec<PathBuf>,

    pub print_ast: bool,
    pub print_types: bool,
    pub execute: bool,
}

pub fn compile_modules(
    main_module: String,
    compiler_options: &CompilerOptions,
) -> Result<(TypedModule, HashMap<Rc<String>, Rc<TypedModule>>), Error> {
    let module_search_path = build_module_search_path(
        compiler_options.current_directory.clone(),
        compiler_options.extra_module_search_path.clone(),
    );
    let infer_stack: Vec<Module> = parse_modules(
        vec![(
            ModuleName::ModuleFileName(Rc::new(main_module.clone())),
            Rc::new(Location {
                module: Rc::new(main_module.clone()),
                function: Rc::new("".to_string()),
                line: 1,
                col: 1,
            }),
        )],
        module_search_path,
    )?;

    let mut inferred_modules_by_name: HashMap<Rc<String>, Rc<TypedModule>> = HashMap::new();

    let mut infer_stack_peekable = infer_stack.into_iter().peekable();
    while let Some(module) = infer_stack_peekable.next() {
        let module_name = module.name.clone();
        println!("Inferring module: {}.. ", module_name);

        let mut errors = Vec::new();

        // 1. Retrieve all dependencies
        let mut imported_records: HashMap<Rc<String>, Rc<RecordDefinition>> = HashMap::new();
        let mut imported_adts: HashMap<Rc<String>, Rc<ADTDefinition>> = HashMap::new();
        let mut imported_functions: HashMap<Rc<String>, Rc<FunctionDefinition>> = HashMap::new();

        let mut existing_module_names: HashMap<Rc<String>, Rc<Location>> = HashMap::new();

        for import in &module.imports {
            let imported_module_name = import_to_module(&import);
            let typed_module =
                Rc::clone(inferred_modules_by_name.get(&imported_module_name).unwrap());

            match import.borrow() {
                Import::ImportMembers(loc, n, members) => {
                    existing_module_names.insert(Rc::clone(n), Rc::clone(loc));
                    for m in members {
                        if m.chars().next().unwrap().is_ascii_uppercase() {
                            if let Some(record_definition) =
                                typed_module.record_name_to_definition.get(m)
                            {
                                if let Some(existing) =
                                    imported_records.insert(m.clone(), Rc::clone(record_definition))
                                {
                                    errors.push(ModuleError::from_loc(
                                        loc,
                                        ModuleErrorType::DefinitionInMultipleImportedModules(
                                            "Record".to_string(),
                                            Rc::clone(m),
                                            Rc::clone(&existing.location.module),
                                            Rc::clone(&record_definition.location.module),
                                        ),
                                    ))
                                }
                            } else if let Some(adt_definition) =
                                typed_module.adt_name_to_definition.get(m)
                            {
                                if let Some(existing) =
                                    imported_adts.insert(m.clone(), Rc::clone(adt_definition))
                                {
                                    errors.push(ModuleError::from_loc(
                                        loc,
                                        ModuleErrorType::DefinitionInMultipleImportedModules(
                                            "ADT".to_string(),
                                            Rc::clone(m),
                                            Rc::clone(&existing.location.module),
                                            Rc::clone(&adt_definition.location.module),
                                        ),
                                    ))
                                }
                            } else {
                                errors.push(ModuleError::from_loc(
                                    loc,
                                    ModuleErrorType::TypeNotDefinedInModule(
                                        imported_module_name.clone(),
                                        m.clone(),
                                    ),
                                ));
                            }
                        } else {
                            if let Some(function) = typed_module.function_name_to_definition.get(m)
                            {
                                if let Some(existing) =
                                    imported_functions.insert(m.clone(), Rc::clone(function))
                                {
                                    errors.push(ModuleError::from_loc(
                                        loc,
                                        ModuleErrorType::DefinitionInMultipleImportedModules(
                                            "Function".to_string(),
                                            Rc::clone(m),
                                            Rc::clone(&existing.location.module),
                                            Rc::clone(&function.location.module),
                                        ),
                                    ))
                                }
                            } else {
                                errors.push(ModuleError::from_loc(
                                    loc,
                                    ModuleErrorType::FunctionNotDefinedInModule(
                                        imported_module_name.clone(),
                                        m.clone(),
                                    ),
                                ));
                            }
                        }
                    }
                }
                Import::ImportModule(loc, n, None) => {
                    if let Some(existing) =
                        existing_module_names.insert(Rc::clone(n), Rc::clone(loc))
                    {
                        errors.push(ModuleError::from_loc(
                            loc,
                            ModuleErrorType::ModuleAliasMultiplyDefined(Rc::clone(n), existing),
                        ))
                    }
                    let added_adts: HashMap<Rc<String>, Rc<ADTDefinition>> = typed_module
                        .adt_name_to_definition
                        .iter()
                        .map(|(n, d)| (n.clone(), Rc::clone(d)))
                        .collect();

                    for (n, d) in added_adts.iter() {
                        if let Some(existing_adt) = imported_adts.get(n) {
                            errors.push(ModuleError::from_loc(
                                loc,
                                ModuleErrorType::DefinitionInMultipleImportedModules(
                                    "ADT".to_string(),
                                    Rc::clone(n),
                                    Rc::clone(&existing_adt.location.module),
                                    Rc::clone(&d.location.module),
                                ),
                            ))
                        }
                    }
                    imported_adts.extend(added_adts);

                    let added_records: HashMap<Rc<String>, Rc<RecordDefinition>> = typed_module
                        .record_name_to_definition
                        .iter()
                        .map(|(n, d)| (n.clone(), Rc::clone(d)))
                        .collect();

                    for (n, d) in added_records.iter() {
                        if let Some(existing_record) = imported_records.get(n) {
                            errors.push(ModuleError::from_loc(
                                loc,
                                ModuleErrorType::DefinitionInMultipleImportedModules(
                                    "Record".to_string(),
                                    Rc::clone(n),
                                    Rc::clone(&existing_record.location.module),
                                    Rc::clone(&d.location.module),
                                ),
                            ))
                        }
                    }
                    imported_records.extend(added_records);

                    let added_functions: HashMap<Rc<String>, Rc<FunctionDefinition>> = typed_module
                        .function_name_to_definition
                        .iter()
                        .map(|(n, d)| (n.clone(), Rc::clone(d)))
                        .collect();
                    for (n, d) in added_functions.iter() {
                        if let Some(existing_function) = imported_functions.get(n) {
                            errors.push(ModuleError::from_loc(
                                loc,
                                ModuleErrorType::DefinitionInMultipleImportedModules(
                                    "Function".to_string(),
                                    Rc::clone(n),
                                    Rc::clone(&existing_function.location.module),
                                    Rc::clone(&d.location.module),
                                ),
                            ))
                        }
                    }
                    imported_functions.extend(added_functions);
                }
                Import::ImportModule(loc, _, Some(alias)) => {
                    if let Some(existing) =
                        existing_module_names.insert(Rc::clone(alias), Rc::clone(loc))
                    {
                        errors.push(ModuleError::from_loc(
                            loc,
                            ModuleErrorType::ModuleAliasMultiplyDefined(Rc::clone(alias), existing),
                        ))
                    }
                    imported_adts.extend(typed_module.adt_name_to_definition.iter().map(
                        |(name, d)| {
                            (
                                prefix_module_name(alias, &name),
                                prefix_constructor_names(alias, Rc::clone(d)),
                            )
                        },
                    ));
                    imported_records.extend(
                        typed_module
                            .record_name_to_definition
                            .iter()
                            .map(|(name, d)| (prefix_module_name(alias, &name), Rc::clone(d))),
                    );
                    imported_functions.extend(
                        typed_module
                            .function_name_to_definition
                            .iter()
                            .map(|(name, d)| (prefix_module_name(alias, &name), Rc::clone(d))),
                    );
                }
            }
        }
        if errors.len() > 0 {
            return Err(Error::ModuleError(errors));
        }

        let external_definitions = ExternalDefinitions {
            adt_name_to_definition: imported_adts,
            record_name_to_definition: imported_records,
            function_name_to_definition: imported_functions,
        };

        let module_inference_options = InferencerOptions {
            print_types: compiler_options.print_types,
            is_main_module: infer_stack_peekable.peek().is_none(),
        };

        match infer(module, module_inference_options, &external_definitions) {
            Ok(module) => {
                if infer_stack_peekable.peek().is_none() {
                    return Ok((module, inferred_modules_by_name));
                }
                inferred_modules_by_name.insert(module.module_name.clone(), Rc::new(module));
            }
            Err(errors) => return Err(Error::InferenceError(errors)),
        };
    }

    unreachable!()
}

fn parse_modules(
    mut parse_stack: Vec<(ModuleName, Rc<Location>)>,
    module_search_path: Vec<PathBuf>,
) -> Result<Vec<Module>, Error> {
    let mut infer_stack: Vec<Module> = Vec::new();
    let mut parsed_modules = HashSet::new();
    while let Some((module, loc)) = parse_stack.pop() {
        let (module_file_name, module_contents) =
            resolve_module(&module_search_path, module.clone(), &loc)?;
        println!("Parsing module {}..", module.name());
        let parsed_module = parse(module_file_name, module.name(), module_contents)?;

        for i in &parsed_module.imports {
            if parsed_modules.insert(import_to_module(i)) {
                parse_stack.insert(
                    0,
                    (
                        ModuleName::ModuleName(import_to_module(i)),
                        import_to_location(i),
                    ),
                );
            }
        }

        infer_stack.insert(0, parsed_module);
    }
    Ok(infer_stack)
}

fn resolve_module(
    module_search_path: &Vec<PathBuf>,
    module_name: ModuleName,
    module_location: &Rc<Location>,
) -> Result<(String, String), Error> {
    for search_directory in module_search_path {
        match &module_name {
            ModuleName::ModuleName(name) => {
                let mut module_path_buffer = search_directory.clone();
                for module_name_component in name.split(".") {
                    module_path_buffer.push(module_name_component);
                }
                module_path_buffer.set_extension("loz");
                if module_path_buffer.is_file() {
                    return Ok((
                        module_path_buffer.to_str().unwrap().to_string(),
                        fs::read_to_string(module_path_buffer).map_err(|e| Error::FileError(e))?,
                    ));
                }
            }
            ModuleName::ModuleFileName(file_name) => {
                let file_name_string = file_name.to_string();
                let module_path_buffer = PathBuf::from(file_name_string);
                if module_path_buffer.is_file() {
                    return Ok((
                        module_path_buffer.to_str().unwrap().to_string(),
                        fs::read_to_string(module_path_buffer).map_err(|e| Error::FileError(e))?,
                    ));
                }
            }
        }
    }
    Err(Error::ModuleError(vec![ModuleError::from_loc(
        module_location,
        ModuleNotFound(module_name.name()),
    )]))
}

fn import_to_module(import: &Import) -> Rc<String> {
    match import {
        Import::ImportMembers(_, module_name, _) => Rc::clone(module_name),
        Import::ImportModule(_, module_name, _) => Rc::clone(module_name),
    }
}

fn import_to_location(import: &Import) -> Rc<Location> {
    match import {
        Import::ImportMembers(loc, _, _) => Rc::clone(loc),
        Import::ImportModule(loc, _, _) => Rc::clone(loc),
    }
}

impl From<std::io::Error> for Error {
    fn from(error: std::io::Error) -> Self {
        Error::FileError(error)
    }
}

impl From<parser::ParseError> for Error {
    fn from(error: parser::ParseError) -> Self {
        Error::ParseError(vec![error])
    }
}

fn prefix_module_name(module: &Rc<String>, identifier: &String) -> Rc<String> {
    let mut prefixed_module = String::new();
    prefixed_module.push_str(module.as_ref());
    prefixed_module.push_str("::");
    prefixed_module.push_str(identifier);
    return Rc::new(prefixed_module);
}

fn prefix_constructor_names(
    module: &Rc<String>,
    adt_definition: Rc<ADTDefinition>,
) -> Rc<ADTDefinition> {
    Rc::new(ADTDefinition {
        constructors: adt_definition
            .constructors
            .iter()
            .map(|(n, c)| {
                let prefixed_name = prefix_module_name(module, &n);
                (
                    Rc::clone(&prefixed_name),
                    Rc::new(ADTConstructor {
                        name: Rc::clone(&prefixed_name),
                        elements: c.elements.iter().map(Rc::clone).collect(),
                    }),
                )
            })
            .collect(),
        name: adt_definition.name.clone(),
        location: adt_definition.location.clone(),
        type_variables: adt_definition.type_variables.clone(),
    })
}

fn build_module_search_path(cwd: PathBuf, module_path_entries: Vec<PathBuf>) -> Vec<PathBuf> {
    let mut search_path = Vec::new();
    search_path.push(cwd);
    for m in module_path_entries {
        search_path.push(m)
    }
    search_path
}

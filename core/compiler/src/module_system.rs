use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};

use crate::{ADTDefinition, FunctionDefinition, Import, Location, Module, parser, RecordDefinition, ADTConstructor};
use crate::inferencer::{infer, InferenceError, InferencerOptions, TypedModule, ExternalDefinitions};
use crate::parser::parse;
use crate::module_system::ModuleError::ModuleNotFound;
use crate::Expression::ADTTypeConstructor;

#[derive(Debug)]
pub enum Error {
    FileError(std::io::Error),
    ParseError(Vec<crate::parser::ParseError>),
    InferenceError(Vec<crate::inferencer::InferenceError>),
    ModuleError(Vec<ModuleError>),
}

#[derive(Debug)]
pub enum ModuleError {
    ModuleNotFound(String),

    LocalDefinitionAlsoInImportedModule(),
    DefinitionInMultipleImportedModules(),

    ModuleAliasMultiplyDefined(),

    FunctionNotDefinedInModule(Location, String, String),
    TypeNotDefinedInModule(Location, String, String),
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

pub fn compile_modules(main_module: &str, working_directory: &PathBuf, infer_options: &InferencerOptions) -> Result<TypedModule, Error> {
    // 1. Push the main module to the compile stack
    let mut parse_stack: Vec<String> = Vec::new();
    parse_stack.push(main_module.to_string());
    let mut infer_stack: Vec<Module> = Vec::new();

    while let Some(module) = parse_stack.pop() {
        println!("Parsing module {} in CWD {:?}", module, working_directory);
        let module_file_name = module_file_name(working_directory, module.to_string());
        println!("Module file name: {:?}", module_file_name);
        let file_contents = fs::read_to_string(module_file_name.clone()).map_err(|e| Error::ModuleError(vec![ModuleNotFound(module.clone())]))?;
        let parsed_module = parse(&module_file_name.to_str().unwrap().to_string(), module.to_string(), &file_contents)?;

        for i in &parsed_module.imports {
            let imported_module_name = import_to_module(i);
            println!("Adding module {} to top of parse stack", imported_module_name);
            parse_stack.insert(0, imported_module_name);
        }

        infer_stack.insert(0, parsed_module);
    }

    let mut inferred_modules_by_name : HashMap<String, TypedModule> = HashMap::new();

    let mut infer_stack_peekable = infer_stack.into_iter().peekable();
    while let Some(module) = infer_stack_peekable.next() {
        let module_name =  module.name.clone();
        println!("Inferring module: {}", module_name);

        let mut errors = Vec::new();

        // 1. Retrieve all dependencies
        let mut imported_records: HashMap<String, RecordDefinition> = HashMap::new();
        let mut imported_adts: HashMap<String, ADTDefinition> = HashMap::new();
        let mut imported_functions: HashMap<String, FunctionDefinition> = HashMap::new();

        for import in &module.imports {
            let imported_module_name = import_to_module(&import);
            let mut typed_module = inferred_modules_by_name.remove(&imported_module_name).unwrap();
            println!("Typed module: {:?}", typed_module);

            match import {
                Import::ImportMembers(loc, _, members) => {
                    for m in members {
                        if m.chars().next().unwrap().is_ascii_uppercase() {
                            if let Some(record_definition) = typed_module.record_name_to_definition.remove(m) {
                                imported_records.insert(m.clone(), record_definition);
                            } else if let Some(adt_definition) = typed_module.adt_name_to_definition.remove(m) {
                                imported_adts.insert(m.clone(), adt_definition);
                            } else {
                                errors.push(ModuleError::TypeNotDefinedInModule(loc.clone(), imported_module_name.clone(), m.clone()));
                            }
                        } else {
                            if let Some(function) = typed_module.function_name_to_declaration.remove(m) {
                                println!("Inserting imported function: {}", function.name);
                                imported_functions.insert(m.clone(), function);
                            } else {
                                errors.push(ModuleError::FunctionNotDefinedInModule(loc.clone(), imported_module_name.clone(), m.clone()));
                            }
                        }
                    }
                }
                Import::ImportModule(loc, _, None) => {
                    imported_adts.extend(typed_module.adt_name_to_definition.into_iter().map(|(n, d)| (n, d)));
                    imported_records.extend(typed_module.record_name_to_definition.into_iter().map(|(n, d)| (n, d)));
                    imported_functions.extend(typed_module.function_name_to_declaration.into_iter().map(|(n, d)| (n, d)));
                }
                Import::ImportModule(loc, _, Some(alias)) => {
                    imported_adts.extend(typed_module.adt_name_to_definition.into_iter()
                        .map(|(name, d)| (prefix_module_name(alias.clone(), &name), prefix_constructor_names(alias.clone(), d))));
                    imported_records.extend(typed_module.record_name_to_definition.into_iter()
                        .map(|(name, d)| (prefix_module_name(alias.clone(), &name), d)));
                    imported_functions.extend(typed_module.function_name_to_declaration.into_iter()
                        .map(|(name, d)| (prefix_module_name(alias.clone(), &name), d)));
                }
            }
        }

        let external_definitions = ExternalDefinitions {
            adt_name_to_definition: imported_adts,
            record_name_to_definition: imported_records,
            function_name_to_definition: imported_functions
        };

        println!("External definitions: {:?}", external_definitions);

        let mut module_inference_options = infer_options.clone();

        // Last module is the main module
        module_inference_options.is_main_module = infer_stack_peekable.peek().is_none();

        match infer(module, module_inference_options, &external_definitions) {
            Ok(ast) => inferred_modules_by_name.insert(module_name, ast),
            Err(errors) => return Err(Error::InferenceError(errors)),
        };
    }

    Ok(inferred_modules_by_name.remove(main_module).unwrap())
}

fn module_file_name(working_directory: &PathBuf, module_name: String) -> PathBuf {
    let mut tpb = working_directory.clone();
    tpb.push(module_name.clone());
    if tpb.is_file() {
        return tpb
    }

    let mut module_path_buffer = working_directory.clone();
    for module_name_component in module_name.split(".") {
        module_path_buffer.push(module_name_component);
    }
    module_path_buffer.set_extension("loz");
    module_path_buffer
}

fn import_to_module(import: &Import) -> String {
    match import {
        Import::ImportMembers(_, module_name, _) => module_name.clone(),
        Import::ImportModule(_, module_name, _) => module_name.clone(),
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

fn prefix_module_name(mut module: String, identifier: &String) -> String {
    module.push_str("::");
    module.push_str(identifier);
    return module;
}

fn prefix_constructor_names(module: String, adt_definition: ADTDefinition) -> ADTDefinition {
   ADTDefinition {
        constructors: adt_definition.constructors.into_iter()
            .map(|(n, c)| {
                let prefixed_name = prefix_module_name(module.clone(), &n);
                (prefixed_name.clone(), ADTConstructor {
                    name: prefixed_name.clone(),
                    elements: c.elements
                })
            } )
            .collect(),
        .. adt_definition
    }
}


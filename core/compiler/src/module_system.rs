use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{PathBuf};

use crate::{ADTConstructor, ADTDefinition, FunctionDefinition, Import, Location, Module, parser, RecordDefinition};
use crate::inferencer::{ExternalDefinitions, infer, InferencerOptions, TypedModule};
use crate::module_system::ModuleError::ModuleNotFound;
use crate::parser::parse;
use std::rc::Rc;
use std::fmt::{Display, Formatter};
use core::fmt;

#[derive(Debug)]
pub enum Error {
    FileError(std::io::Error),
    ParseError(Vec<crate::parser::ParseError>),
    InferenceError(Vec<crate::inferencer::InferenceError>),
    ModuleError(Vec<ModuleError>),
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Error::FileError(e) => write!(f, "{}", e),
            Error::ParseError(pes)
            => write!(f, "{}", pes.iter().map(|pe| pe.to_string()).collect::<Vec<String>>()
                    .join("\n")),
            Error::InferenceError(ies)
            => write!(f, "{}", ies.iter().map(|pe| pe.to_string()).collect::<Vec<String>>()
                .join("\n")),
            Error::ModuleError(mes)
            => write!(f, "{}", mes.iter().map(|pe| pe.to_string()).collect::<Vec<String>>()
                .join("\n")),
        }
    }
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

impl Display for ModuleError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "Module error: ")?;
        match self {
            ModuleNotFound(name) => write!(f, "Module '{}' not found", name),
            ModuleError::LocalDefinitionAlsoInImportedModule() => write!(f, "Local definition also in imported module"),
            ModuleError::DefinitionInMultipleImportedModules() => write!(f, "DefinitionInMultipleImportedModules"),
            ModuleError::ModuleAliasMultiplyDefined() => write!(f, "ModuleAliasMultiplyDefined"),
            ModuleError::FunctionNotDefinedInModule(_, module, function) => write!(f, "Function '{}' not found in module '{}'", function, module),
            ModuleError::TypeNotDefinedInModule(_,module, type_name) => write!(f, "Type '{}' not found in module '{}'", type_name, module),
        }
    }
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
    ModuleName(String),
    ModuleFileName(String),
}

impl ModuleName {
    fn name(&self) -> String {
        match self {
            ModuleName::ModuleName(n) => n.clone(),
            ModuleName::ModuleFileName(n) => n.clone(),
        }
    }
}

pub fn compile_modules(main_module: String, infer_options: &InferencerOptions) -> Result<TypedModule, Error> {
    let infer_stack: Vec<Module> = parse_modules(vec![ModuleName::ModuleFileName(main_module.clone())], PathBuf::from(&main_module).parent().unwrap().to_path_buf())?;

    let mut inferred_modules_by_name: HashMap<String, Rc<TypedModule>> = HashMap::new();

    let mut infer_stack_peekable = infer_stack.into_iter().peekable();
    while let Some(module) = infer_stack_peekable.next() {
        let module_name = module.name.clone();
        println!("Inferring module: {}", module_name);

        let mut errors = Vec::new();

        // 1. Retrieve all dependencies
        let mut imported_records: HashMap<String, Rc<RecordDefinition>> = HashMap::new();
        let mut imported_adts: HashMap<String, Rc<ADTDefinition>> = HashMap::new();
        let mut imported_functions: HashMap<String, Rc<FunctionDefinition>> = HashMap::new();

        for import in &module.imports {
            let imported_module_name = import_to_module(&import);
            let typed_module = Rc::clone(inferred_modules_by_name.get(&imported_module_name).unwrap());

            match import {
                Import::ImportMembers(loc, _, members) => {
                    for m in members {
                        if m.chars().next().unwrap().is_ascii_uppercase() {
                            if let Some(record_definition) = typed_module.record_name_to_definition.get(m) {
                                imported_records.insert(m.clone(), Rc::clone(record_definition));
                            } else if let Some(adt_definition) = typed_module.adt_name_to_definition.get(m) {
                                imported_adts.insert(m.clone(), Rc::clone(adt_definition));
                            } else {
                                errors.push(ModuleError::TypeNotDefinedInModule(loc.clone(), imported_module_name.clone(), m.clone()));
                            }
                        } else {
                            if let Some(function) = typed_module.function_name_to_declaration.get(m) {
                                imported_functions.insert(m.clone(), Rc::clone(function));
                            } else {
                                errors.push(ModuleError::FunctionNotDefinedInModule(loc.clone(), imported_module_name.clone(), m.clone()));
                            }
                        }
                    }
                }
                Import::ImportModule(_, _, None) => {
                    imported_adts.extend(typed_module.adt_name_to_definition.iter().map(|(n, d)| (n.clone(), Rc::clone(d))));
                    imported_records.extend(typed_module.record_name_to_definition.iter().map(|(n, d)| (n.clone(), Rc::clone(d))));
                    imported_functions.extend(typed_module.function_name_to_declaration.iter().map(|(n, d)| (n.clone(), Rc::clone(d))));
                }
                Import::ImportModule(_, _, Some(alias)) => {
                    imported_adts.extend(typed_module.adt_name_to_definition.iter()
                        .map(|(name, d)| (prefix_module_name(alias.clone(), &name), prefix_constructor_names(alias.clone(), Rc::clone(d)))));
                    imported_records.extend(typed_module.record_name_to_definition.iter()
                        .map(|(name, d)| (prefix_module_name(alias.clone(), &name), Rc::clone(d))));
                    imported_functions.extend(typed_module.function_name_to_declaration.iter()
                        .map(|(name, d)| (prefix_module_name(alias.clone(), &name), Rc::clone(d))));
                }
            }
        }

        let external_definitions = ExternalDefinitions {
            adt_name_to_definition: imported_adts,
            record_name_to_definition: imported_records,
            function_name_to_definition: imported_functions,
        };

        let mut module_inference_options = infer_options.clone();

        // Last module is the main module
        module_inference_options.is_main_module = infer_stack_peekable.peek().is_none();

        match infer(module, module_inference_options, &external_definitions) {
            Ok(module) => {
                let module = add_external_definitions(module, external_definitions);
                if infer_stack_peekable.peek().is_none() {
                    return Ok(module);
                }
                inferred_modules_by_name.insert(module.module_name.clone(), Rc::new(module));
            }
            Err(errors) => return Err(Error::InferenceError(errors)),
        };
    }

    unreachable!()
}

fn parse_modules(mut parse_stack: Vec<ModuleName>, working_directory: PathBuf) -> Result<Vec<Module>, Error> {
    let mut infer_stack: Vec<Module> = Vec::new();
    let mut parsed_modules = HashSet::new();
    while let Some(module) = parse_stack.pop() {
        let module_file_name = module_file_name(&working_directory, module.clone());
        let file_contents = fs::read_to_string(module_file_name.clone()).map_err(|_| Error::ModuleError(vec![ModuleNotFound(module.clone().name())]))?;
        println!("Parsing module {}", module.name());
        let parsed_module = parse(&module_file_name.to_str().unwrap().to_string(), module.name(), &file_contents)?;

        for i in &parsed_module.imports {
            if parsed_modules.insert(import_to_module(i)) {
                parse_stack.insert(0, ModuleName::ModuleName(import_to_module(i)));
            }
        }

        infer_stack.insert(0, parsed_module);
    }
    println!("Infer stack: {}", infer_stack.iter().map(|m| m.name.clone()).collect::<Vec<String>>().join(", "));
    Ok(infer_stack)
}

fn module_file_name(working_directory: &PathBuf, module_name: ModuleName) -> PathBuf {
    match module_name {
        ModuleName::ModuleName(name) => {
            let mut module_path_buffer = working_directory.clone();
            for module_name_component in name.split(".") {
                module_path_buffer.push(module_name_component);
            }
            module_path_buffer.set_extension("loz");
            module_path_buffer
        }
        ModuleName::ModuleFileName(file_name) => {
            PathBuf::from(file_name)
        }
    }
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

fn prefix_constructor_names(module: String, adt_definition: Rc<ADTDefinition>) -> Rc<ADTDefinition> {
    Rc::new(ADTDefinition {
        constructors: adt_definition.constructors.iter()
            .map(|(n, c)| {
                let prefixed_name = prefix_module_name(module.clone(), &n);
                (prefixed_name.clone(), ADTConstructor {
                    name: prefixed_name.clone(),
                    elements: c.elements.iter().map(Rc::clone).collect(),
                })
            })
            .collect(),
        name: adt_definition.name.clone(),
        location: adt_definition.location.clone(),
        type_variables: adt_definition.type_variables.clone()
    })
}

fn add_external_definitions(module: TypedModule, external_definitions: ExternalDefinitions) -> TypedModule {
    TypedModule {
        record_name_to_definition: module.record_name_to_definition.into_iter().chain(external_definitions.record_name_to_definition.into_iter()).collect(),
        adt_name_to_definition: module.adt_name_to_definition.into_iter().chain(external_definitions.adt_name_to_definition.into_iter()).collect(),
        function_name_to_declaration: module.function_name_to_declaration.into_iter().chain(external_definitions.function_name_to_definition.into_iter()).collect()
        ,
        ..module
    }
}

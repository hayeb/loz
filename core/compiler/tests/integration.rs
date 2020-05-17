use std::fmt::{Display, Formatter};
use std::path::{Path, PathBuf};
use std::{fs, io};

use loz_compiler::inferencer::{InferencerOptions, TypedModule};
use loz_compiler::interpreter::{interpret, InterpreterError, Value};
use loz_compiler::module_system;
use loz_compiler::module_system::{compile_modules, Error};
use loz_compiler::rewriter::rewrite;
use std::collections::HashMap;
use std::rc::Rc;

#[test]
fn test_ok_files() -> Result<(), io::Error> {
    compile_files("tests/programs/ok", |res| res.is_ok())
}

#[test]
fn test_parse_err_files() -> Result<(), io::Error> {
    compile_files("tests/programs/parse_err", |res| match res {
        Err(Error::ParseError(_)) => true,
        _ => false,
    })
}

#[test]
fn test_type_err_files() -> Result<(), io::Error> {
    compile_files("tests/programs/type_err", |res| match res {
        Err(Error::InferenceError(_)) => true,
        _ => false,
    })
}

#[test]
fn test_module_err_files() -> Result<(), io::Error> {
    compile_files("tests/programs/module_err", |res| match res {
        Err(Error::ModuleError(_)) => true,
        _ => false,
    })
}

fn compile_files(
    directory: &str,
    f: impl Fn(
        &Result<(TypedModule, HashMap<Rc<String>, Rc<TypedModule>>), module_system::Error>,
    ) -> bool,
) -> Result<(), io::Error> {
    for entry in fs::read_dir(Path::new(directory))? {
        let entry = entry?;
        let mut path = entry.path();
        if path.to_str().unwrap().ends_with(".res") || path.to_str().unwrap().ends_with(".skip") {
            continue;
        }

        if path.is_dir() {
            path.push("A.loz")
        }

        println!(
            "### Compiling program {}...",
            path.clone().to_str().unwrap()
        );

        let res = compile_modules(
            path.clone().to_str().unwrap().to_string(),
            &InferencerOptions {
                print_types: false,
                is_main_module: true,
            },
        );
        println!("Result: {:#?}", res);
        assert!(f(&res));

        if let Ok((ast, typed_modules)) = res {
            let mut result_value_path = path.clone().to_str().unwrap().to_string();

            if Path::new(&format!("{}.skip", result_value_path)).exists() {
                println!("Skipping execution...");
                continue;
            }

            let runtime_module = rewrite(ast, typed_modules);

            let result_value_string = fs::read_to_string(format!("{}.res", result_value_path))?;
            let result = match interpret(runtime_module) {
                Ok(value) => format!("{}", value),
                Err(err) => format!("{}", err),
            };
            assert_eq!(result_value_string, result);
            println!("Verified interpreter result: Ok");
        }
    }
    Ok(())
}

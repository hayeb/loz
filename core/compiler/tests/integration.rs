use loz_compiler::{inferencer, module_system};
use loz_compiler::inferencer::{InferenceError, InferencerOptions, TypedModule, ExternalDefinitions};
use loz_compiler::interpreter::{interpret, InterpreterError, Value};
use loz_compiler::parser;
use loz_compiler::parser::ParseError;
use std::fmt::{Display, Formatter};
use std::path::{Path, PathBuf};
use std::{fmt, fs, io, env};
use itertools::Itertools;
use loz_compiler::module_system::{compile_modules, Error};

#[test]
fn test_ok_files() -> Result<(), io::Error> {
    env::set_current_dir(Path::new("tests/programs/ok"));
    compile_files(".", |res| res.is_ok())
}

#[test]
fn test_parse_err_files() -> Result<(), io::Error> {
    env::set_current_dir(Path::new("tests/programs/parse_err"));
    compile_files(".", |res| match res {
        Err(Error::ParseError(e)) => true,
        _ => false
    })
}

#[test]
fn test_type_err_files() -> Result<(), io::Error> {
    env::set_current_dir(Path::new("tests/programs/type_err"));
    compile_files(".", |res| match res {
        Err(Error::InferenceError(e)) => true,
        _ => false
    })
}

fn compile_files(dir: &str, f: impl Fn(&Result<TypedModule, module_system::Error>) -> bool) -> Result<(), io::Error> {
    for entry in fs::read_dir(env::current_dir().unwrap())? {
        let entry = entry?;
        let mut path = entry.path();
        if path.to_str().unwrap().ends_with(".res")
            || path.to_str().unwrap().ends_with(".skip")
        {
            continue;
        }

        let mut wd = env::current_dir().unwrap();

        if path.is_dir() {
            wd.push(path.components().last().unwrap().as_os_str());
            path.push("A.loz");
        }

        println!(
            "### Compiling program {}...",
            path.clone().to_str().unwrap()
        );

        let res = compile_modules(path.clone().to_str().unwrap(), &wd, &InferencerOptions {
            print_types: false,
            is_main_module: true
        });
        assert!(f(&res));
    }
    Ok(())
}

use crate::CompileResult::Compiled;
use loz_compiler::inferencer;
use loz_compiler::inferencer::{InferenceError, InferencerOptions, TypedAST};
use loz_compiler::interpreter::{interpret, InterpreterError, Value};
use loz_compiler::parser;
use loz_compiler::parser::ParseError;
use std::fmt::{Display, Formatter};
use std::path::{Path, PathBuf};
use std::{fmt, fs, io};

#[test]
fn test_ok_files() -> Result<(), io::Error> {
    compile_files("tests/programs/ok", |res| res.compiled())
}

#[test]
fn test_parse_err_files() -> Result<(), io::Error> {
    compile_files("tests/programs/parse_err", |res| res.parse_error())
}

#[test]
fn test_type_err_files() -> Result<(), io::Error> {
    compile_files("tests/programs/type_err", |res| res.inference_error())
}

enum CompileResult {
    Compiled(TypedAST),

    ParseError(ParseError),

    InferenceError(Vec<InferenceError>),
}

impl CompileResult {
    fn compiled(&self) -> bool {
        match self {
            CompileResult::Compiled(_) => true,
            _ => false,
        }
    }

    fn parse_error(&self) -> bool {
        match self {
            CompileResult::ParseError(_) => true,
            _ => false,
        }
    }

    fn inference_error(&self) -> bool {
        match self {
            CompileResult::InferenceError(_) => true,
            _ => false,
        }
    }
}

impl Display for CompileResult {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            CompileResult::Compiled(_) => write!(f, "Ok"),
            CompileResult::ParseError(pe) => {
                let pe_string = pe.to_string();

                let mut result = String::from("");
                for l in pe_string.lines() {
                    result.extend("\t".chars());
                    result.extend(l.chars());
                    result.extend("\n".chars())
                }
                write!(f, "Parse error: \n{}", result)
            }
            CompileResult::InferenceError(inference_errors) => write!(
                f,
                "Inference errors:\n\t\t{}",
                inference_errors
                    .into_iter()
                    .map(|ie| ie.to_string())
                    .collect::<Vec<String>>()
                    .join("\n\t\t")
            ),
        }
    }
}

fn compile_files(dir: &str, f: impl Fn(&CompileResult) -> bool) -> Result<(), io::Error> {
    let r = fs::read_dir(dir)?;
    for entry in r {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir()
            || path.to_str().unwrap().ends_with(".res")
            || path.to_str().unwrap().ends_with(".skip")
        {
            continue;
        }

        println!(
            "### Compiling program {}...",
            path.clone().to_str().unwrap()
        );
        let res = compile_file(path.clone());
        println!("\t### Type inferencing \n\t\t{}", res);
        assert!(f(&res));

        if let Compiled(ast) = res {
            let mut result_value_path = path.clone().to_str().unwrap().to_string();

            if Path::new(&format!("{}.skip", result_value_path)).exists() {
                println!("\t### Skipping execution");
                continue;
            }

            let result_value_string = fs::read_to_string(format!("{}.res", result_value_path))?;
            let result = match interpret(&ast) {
                Ok(value) => format!("{}", value),
                Err(err) => format!("{}", err),
            };
            assert_eq!(result_value_string, result);
            println!("\t### Verified interpreter result\n\t\tOk");
        }
    }
    Ok(())
}

fn compile_file(path: PathBuf) -> CompileResult {
    let file_contents = fs::read_to_string(&path).unwrap();

    let ast = match parser::parse(&path.to_str().unwrap().to_string(), &file_contents) {
        Ok(ast) => ast,
        Err(parse_error) => return CompileResult::ParseError(parse_error),
    };

    println!("\t### Parsing\n\t\tOk");

    match inferencer::infer(
        &ast,
        path.to_str().unwrap().to_string(),
        InferencerOptions {
            print_types: false,
            is_main_module: true,
        },
    ) {
        Ok(typed_ast) => CompileResult::Compiled(typed_ast),
        Err(inference_errors) => CompileResult::InferenceError(inference_errors),
    }
}

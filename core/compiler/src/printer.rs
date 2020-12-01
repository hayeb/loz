use std::fmt::{Display, Formatter};

use crate::module_system::{Error, ModuleError, ModuleErrorType};
use crate::{Location, Type, TypeScheme};
use std::fmt;

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Error::FileError(e) => write!(f, "{}", e),
            Error::ParseError(pes) => write!(
                f,
                "{}",
                pes.iter()
                    .map(|pe| pe.to_string())
                    .collect::<Vec<String>>()
                    .join("\n")
            ),
            Error::InferenceError(ies) => write!(
                f,
                "{}",
                ies.iter()
                    .map(|pe| pe.to_string())
                    .collect::<Vec<String>>()
                    .join("\n")
            ),
            Error::ModuleError(mes) => write!(
                f,
                "{}",
                mes.iter()
                    .map(|pe| pe.to_string())
                    .collect::<Vec<String>>()
                    .join("\n")
            ),
        }
    }
}

impl Display for Location {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(
            f,
            "{}::{}[{}:{}]",
            self.module, self.function, self.line, self.col
        )
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Type::Bool => write!(f, "Bool"),
            Type::Char => write!(f, "Char"),
            Type::String => write!(f, "String"),
            Type::Int => write!(f, "Int"),
            Type::Float => write!(f, "Float"),
            Type::UserType(t, type_arguments) if type_arguments.len() == 0 => write!(f, "{}", t),
            Type::UserType(t, type_arguments) => write!(
                f,
                "({} {})",
                t,
                type_arguments
                    .into_iter()
                    .map(|(_, e)| e.to_string())
                    .collect::<Vec<String>>()
                    .join(" ")
            ),
            Type::Variable(name) => write!(f, "{}", name),
            Type::Tuple(elements) => write!(
                f,
                "({})",
                elements
                    .into_iter()
                    .map(|e| e.to_string())
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            Type::List(e) => write!(f, "[{}]", e),
            Type::Function(from, to) => write!(
                f,
                "({} -> {})",
                from.iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<String>>()
                    .join(" "),
                to.to_string()
            ),
        }
    }
}

impl Display for TypeScheme {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        if self.bound_variables.len() > 0 {
            write!(
                f,
                "∀{}: {}",
                self.bound_variables
                    .iter()
                    .map(|s| s.to_string())
                    .collect::<Vec<String>>()
                    .join(" "),
                self.enclosed_type
            )
        } else {
            write!(f, "{}", self.enclosed_type)
        }
    }
}
impl Display for ModuleError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.location, self.error)
    }
}
impl Display for ModuleErrorType {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            ModuleErrorType::ModuleNotFound(name) => write!(f, "Module '{}' not found", name),
            ModuleErrorType::DefinitionInMultipleImportedModules(
                dt,
                name,
                original_module,
                current_module,
            ) => write!(
                f,
                "{} '{}' imported from module '{}' but also earlier from module '{}'",
                dt, name, current_module, original_module
            ),
            ModuleErrorType::ModuleAliasMultiplyDefined(alias, loc_b) => write!(
                f,
                "Module alias '{}' defined earlier at [{}:{}]",
                alias, loc_b.line, loc_b.col
            ),
            ModuleErrorType::FunctionNotDefinedInModule(module, function) => write!(
                f,
                "Function '{}' not found in module '{}'",
                function, module
            ),
            ModuleErrorType::TypeNotDefinedInModule(module, type_name) => {
                write!(f, "Type '{}' not found in module '{}'", type_name, module)
            }
        }
    }
}

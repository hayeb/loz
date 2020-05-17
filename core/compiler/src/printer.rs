use std::fmt::{Display, Formatter};

use crate::ast::{Location, Type, TypeScheme};

impl Display for Location {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(
            f,
            "{}::{}[{}:{}]",
            self.file, self.function, self.line, self.col
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
                "{} {}",
                t,
                type_arguments
                    .into_iter()
                    .map(|e| e.to_string())
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

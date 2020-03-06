use std::collections::HashMap;

use crate::parser::{Type, TypeScheme, TypeVar};

pub fn substitute(substitutions: &HashMap<TypeVar, Type>, target: &TypeScheme) -> TypeScheme {
    let bound_variables = &target.bound_variables;
    let subs : HashMap<TypeVar, Type> = substitutions.clone().into_iter()
        .filter(|(v, _)| !bound_variables.contains(v))
        .collect();
    TypeScheme { bound_variables: bound_variables.clone(), enclosed_type: substitute_type(&subs, &target.enclosed_type) }
}

pub fn substitute_type(substitutions: &HashMap<TypeVar, Type>, target: &Type) -> Type {
    match target {
        Type::Bool => Type::Bool,
        Type::Char => Type::Char,
        Type::String => Type::String,
        Type::Int => Type::Int,
        Type::Float => Type::Float,

        Type::UserType(name, argument_types)
        => Type::UserType(name.clone(), argument_types.into_iter().map(|t| substitute_type(substitutions, t)).collect()),

        Type::Tuple(element_types) => Type::Tuple(element_types.into_iter().map(|t| substitute_type(substitutions, t)).collect()),
        Type::List(element_type) => Type::List(Box::new(substitute_type(substitutions, element_type.clone().as_ref()))),
        Type::Variable(name) => {
            match substitutions.get(name) {
                None => Type::Variable(name.clone()),
                Some(t) => t.clone(),
            }
        }

        Type::Function(from_types, to_type)
        => Type::Function(from_types.into_iter()
                .map(|t| substitute_type(substitutions, t))
                .collect(),
              Box::new(substitute_type(substitutions, to_type.clone().as_ref())))
    }
}

pub fn substitute_list(substitutions: &HashMap<TypeVar, Type>, targets: &Vec<Type>) -> Vec<Type> {
    targets.into_iter()
        .map(|target| substitute_type(substitutions, target))
        .collect()
}
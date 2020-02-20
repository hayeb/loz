use std::collections::HashMap;

use crate::parser::{Type, TypeVar, TypeScheme};

pub fn substitute(substitutions: &HashMap<TypeVar, Type>, target: &Type) -> Type {
    match target {
        Type::Bool => Type::Bool,
        Type::Char => Type::Char,
        Type::String => Type::String,
        Type::Int => Type::Int,
        Type::Float => Type::Float,

        Type::UserType(name, argument_types)
        => Type::UserType(name.clone(), argument_types.into_iter().map(|t| substitute(substitutions, t)).collect()),

        Type::Tuple(element_types) => Type::Tuple(element_types.into_iter().map(|t| substitute(substitutions, t)).collect()),
        Type::List(element_type) => Type::List(Box::new(substitute(substitutions, element_type.clone().as_ref()))),
        Type::Variable(name) => {
            match substitutions.get(name) {
                None => Type::Variable(name.clone()),
                Some(t) => t.clone(),
            }
        },

        Type::Function(from_types, to_type)
        => Type::Function(from_types.into_iter().map(|t| substitute(substitutions, t)).collect(), Box::new(substitute(substitutions, to_type.clone().as_ref())))
    }
}

pub fn substiture_type_scheme(substitutions: &HashMap<TypeVar, Type>, target: TypeScheme) -> TypeScheme {
    let applicable_subs = substitutions.into_iter()
        .filter(|(s, _)| !target.bound_variables.contains(*s))
        .map(|(s, t)| (s.clone(), t.clone()))
        .collect();

    TypeScheme{bound_variables: target.bound_variables, enclosed_type: substitute(&applicable_subs, &target.enclosed_type)}
}

pub fn substitute_list(substitutions: &HashMap<TypeVar, Type>, targets: &Vec<Type>) -> Vec<Type> {
    targets.into_iter()
        .map(|target| substitute(substitutions, target))
        .collect()
}
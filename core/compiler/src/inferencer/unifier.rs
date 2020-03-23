use crate::{Type, TypeVar};
use crate::inferencer::InferenceErrorType;
use crate::inferencer::substitutor::substitute_type;

pub fn unify(a: &Type, b: &Type) -> Result<Vec<(TypeVar, Type)>, InferenceErrorType> {
    match (a, b) {
        // Basic types always succeed with no unifications
        (Type::Bool, Type::Bool) => Ok(Vec::new()),
        (Type::Char, Type::Char) => Ok(Vec::new()),
        (Type::String, Type::String) => Ok(Vec::new()),
        (Type::Int, Type::Int) => Ok(Vec::new()),
        (Type::Float, Type::Float) => Ok(Vec::new()),

        (Type::UserType(a_name, a_argument_types), Type::UserType(b_name, b_argument_types)) => {
            if a_name != b_name {
                Err(InferenceErrorType::UnificationError(a.clone(), b.clone()))
            } else {
                unify_types(a_argument_types, b_argument_types)
            }
        }

        (Type::Tuple(a_element_types), Type::Tuple(b_element_types)) => {
            unify_types(a_element_types, b_element_types)
        }

        (Type::List(a_type), Type::List(b_type)) => {
            match unify(a_type, b_type) {
                Ok(subs) => Ok(subs),
                Err(InferenceErrorType::UnificationError(l, r)) => Err(InferenceErrorType::UnificationError(Type::List(Box::new(l)), Type::List(Box::new(r)))),
                Err(e) => Err(e)
            }
        }

        (Type::Function(a_from_types, a_to_type), Type::Function(b_from_types, b_to_type))
        => unify_functions(a_from_types, a_to_type, b_from_types, b_to_type),

        (Type::Variable(a_var), Type::Variable(b_var)) if a_var == b_var => Ok(Vec::new()),

        (Type::Variable(a_var), b_type) if !b_type.collect_free_type_variables().contains(a_var) => {
            let mut subs = Vec::new();
            subs.push((a_var.clone(), b_type.clone()));
            Ok(subs)
        }
        (a_type, Type::Variable(b_var)) if !a_type.collect_free_type_variables().contains(b_var) => {
            let mut subs = Vec::new();
            subs.push((b_var.clone(), a_type.clone()));
            Ok(subs)
        }

        (a, b) => Err(InferenceErrorType::UnificationError(a.clone(), b.clone()))
    }
}

pub fn unify_one_of(types: &Vec<Type>, r: &Type) -> Result<Vec<(TypeVar, Type)>, InferenceErrorType> {
    for l in types {
        match unify(&l, &r) {
            Ok(unifiers) => return Ok(unifiers),
            Err(_) => continue,
        }
    }
    Err(InferenceErrorType::UnificationErrorMultiple(types.clone(), r.clone()))
}

fn unify_types(a_types: &Vec<Type>, b_types: &Vec<Type>) -> Result<Vec<(TypeVar, Type)>, InferenceErrorType> {
    if a_types.len() != b_types.len() {
        return Err(InferenceErrorType::WrongNumberOfTypes(a_types.len(), b_types.len()));
    }
    let mut unifiers = Vec::new();
    for (a_argument_type, b_argument_type) in a_types.iter().zip(b_types.iter()) {
        let u = unify(&substitute_type(&unifiers, a_argument_type), &substitute_type(&unifiers, b_argument_type))?;
        unifiers.extend(u);
    }
    Ok(unifiers)
}

fn unify_functions(a_arguments: &Vec<Type>, a_result: &Type, b_arguments: &Vec<Type>, b_result: &Type) -> Result<Vec<(TypeVar, Type)>, InferenceErrorType> {
    if a_arguments.len() != b_arguments.len() {
        return Err(InferenceErrorType::UnificationError(Type::Function(a_arguments.clone(), Box::new(a_result.clone())), Type::Function(b_arguments.clone(), Box::new(b_result.clone()))));
    }

    let mut subs = Vec::new();
    let mut a_result_type = a_result.clone();
    let mut b_result_type = b_result.clone();
    for (a_argument_type, b_argument_type) in a_arguments.iter().zip(b_arguments.iter()) {
        let new_subs = unify(&substitute_type(&subs, a_argument_type), &substitute_type(&subs, b_argument_type))
            .map_err(|_| InferenceErrorType::UnificationError(Type::Function(a_arguments.clone(), Box::new(a_result.clone())), Type::Function(b_arguments.clone(), Box::new(b_result.clone()))))?;
        a_result_type = substitute_type(&new_subs, &a_result_type);
        b_result_type = substitute_type(&new_subs, &b_result_type);

        subs.extend(new_subs);
    }

    let result_unifiers = unify(&substitute_type(&subs, &a_result_type), &substitute_type(&subs, &b_result_type))
        .map_err(|_| InferenceErrorType::UnificationError(Type::Function(a_arguments.clone(), Box::new(a_result.clone())), Type::Function(b_arguments.clone(), Box::new(b_result.clone()))))?;
    subs.extend(result_unifiers);
    Ok(subs.to_owned())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unify_basic_types() {
        assert!(unify(&Type::Bool, &Type::Bool).is_ok());
        assert!(unify(&Type::Int, &Type::Int).is_ok());
        assert!(unify(&Type::Float, &Type::Float).is_ok());
        assert!(unify(&Type::String, &Type::String).is_ok());
        assert!(unify(&Type::Char, &Type::Char).is_ok());
    }

    #[test]
    fn test_variable() {
        let unify_result = unify(&Type::Variable("a".to_string()), &Type::Bool);
        assert!(unify_result.is_ok());
        let unify_result = unify_result.unwrap();
        assert_eq!(unify_result.get(0), Some(&("a".to_string(), Type::Bool)))
    }

    #[test]
    fn test_unify_tuple() {
        assert!(unify(&Type::Tuple(vec![Type::Bool, Type::Int]), &Type::Tuple(vec![Type::Bool, Type::Int])).is_ok());
        assert!(unify(&Type::Tuple(vec![Type::Bool, Type::Int]), &Type::Tuple(vec![Type::Int, Type::Int])).is_err());

        let unify_result = unify(&Type::Tuple(vec![Type::Variable("a".to_string()), Type::Int]), &Type::Tuple(vec![Type::Bool, Type::Int]));
        assert!(unify_result.is_ok());
        let unify_result = unify_result.unwrap();
        assert_eq!(unify_result.get(0), Some(&("a".to_string(), Type::Bool)));

        let unify_result = unify(&Type::Tuple(vec![Type::Bool, Type::Int]), &Type::Tuple(vec![Type::Variable("a".to_string()), Type::Int]));
        assert!(unify_result.is_ok());
        let unify_result = unify_result.unwrap();
        assert_eq!(unify_result.get(0), Some(&("a".to_string(), Type::Bool)))
    }

    #[test]
    fn test_unify_list() {
        assert!(unify(&Type::List(Box::new(Type::Bool)), &Type::List(Box::new(Type::Bool))).is_ok());
        assert!(unify(&Type::List(Box::new(Type::Int)), &Type::List(Box::new(Type::Bool))).is_err());

        let unify_result = unify(&&Type::List(Box::new(Type::Variable("a".to_string()))), &Type::List(Box::new(Type::Bool)));
        assert!(unify_result.is_ok());
        let unify_result = unify_result.unwrap();
        assert_eq!(unify_result.get(0), Some(&("a".to_string(), Type::Bool)));

        let unify_result = unify(&&Type::List(Box::new(Type::Bool)), &Type::List(Box::new(Type::Variable("a".to_string()))));
        assert!(unify_result.is_ok());
        let unify_result = unify_result.unwrap();
        assert_eq!(unify_result.get(0), Some(&("a".to_string(), Type::Bool)))
    }

    #[test]
    fn test_unify_custom_type() {
        let adt_a = Type::UserType("A".to_string(), vec![Type::Bool, Type::Int]);
        let adt_b = Type::UserType("B".to_string(), vec![Type::String]);
        let adt_c = Type::UserType("A".to_string(), vec![Type::Variable("a".to_string()), Type::Variable("b".to_string())]);

        assert!(unify(&adt_a, &Type::Variable("a".to_string())).is_ok());
        assert!(unify(&adt_a, &adt_b).is_err());

        let unify_result = unify(&adt_a, &adt_c);
        assert!(unify_result.is_ok());
        let unify_result = unify_result.unwrap();
        assert_eq!(unify_result.get(0), Some(&("a".to_string(), Type::Bool)));
        assert_eq!(unify_result.get(1), Some(&("b".to_string(), Type::Int)));
    }

    #[test]
    fn test_free_variables() {
        let f_a = Type::Function(vec![Type::Variable("a".to_string())], Box::new(Type::Variable("b".to_string())));
        let b = Type::Variable("a".to_string());

        let unify_result = unify(&f_a, &b);
        assert!(unify_result.is_err());
        let e = unify_result.unwrap_err();
        assert_eq!(e, InferenceErrorType::UnificationError(f_a, b))
    }
}
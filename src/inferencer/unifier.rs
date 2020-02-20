use std::collections::HashMap;

use crate::inferencer::InferenceErrorType;
use crate::parser::Type;
use crate::inferencer::substitutor::substitute;
use std::collections::hash_map::RandomState;

pub fn unify(a: &Type, b: &Type) -> Result<HashMap<String, Type>, InferenceErrorType> {
    match (a, b) {
        // Basic types always succeed with no unifications
        (Type::Bool, Type::Bool) => Ok(HashMap::new()),
        (Type::Char, Type::Char) => Ok(HashMap::new()),
        (Type::String, Type::String) => Ok(HashMap::new()),
        (Type::Int, Type::Int) => Ok(HashMap::new()),
        (Type::Float, Type::Float) => Ok(HashMap::new()),

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

        (Type::Variable(a_var), b_type) if !b_type.collect_free_type_variables().contains(a_var) => {
            let mut subs = HashMap::new();
            subs.insert(a_var.clone(), b_type.clone());
            Ok(subs)
        }
        (a_type, Type::Variable(b_var)) if !a_type.collect_free_type_variables().contains(b_var) => {
            let mut subs = HashMap::new();
            subs.insert(b_var.clone(), a_type.clone());
            Ok(subs)
        }

        (a, b) => Err(InferenceErrorType::UnificationError(a.clone(), b.clone()))
    }
}

pub fn unify_one_of(types: &Vec<Type>, r: &Type) -> Result<HashMap<String, Type>, InferenceErrorType> {
    for l in types {
        match unify(&l, &r) {
            Ok(unifiers) => return Ok(unifiers),
            Err(_) => continue,
        }
    }
    Err(InferenceErrorType::UnificationErrorMultiple(types.clone(), r.clone()))
}

fn unify_types(a_types: &Vec<Type>, b_types: &Vec<Type>) -> Result<HashMap<String, Type>, InferenceErrorType> {
    if a_types.len() != b_types.len() {
        return Err(InferenceErrorType::WrongNumberOfTypes(a_types.len(), b_types.len()));
    }
    let mut unifiers = HashMap::new();
    for (a_argument_type, b_argument_type) in a_types.iter().zip(b_types.iter()) {
        let u = unify(&substitute(&unifiers, a_argument_type), &substitute(&unifiers, b_argument_type))?;
        unifiers.extend(u);
    }
    Ok(unifiers)
}

fn unify_functions(a_arguments: &Vec<Type>, a_result: &Type, b_arguments: &Vec<Type>, b_result: &Type) -> Result<HashMap<String, Type>, InferenceErrorType> {
    let mut argument_unifiers = unify_types(a_arguments, b_arguments)?;

    let result_unifiers = unify(a_result, b_result)?;
    argument_unifiers.extend(result_unifiers);
    Ok(argument_unifiers.to_owned())
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
        assert_eq!(unify_result.get("a"), Some(&Type::Bool))
    }

    #[test]
    fn test_unify_tuple() {
        assert!(unify(&Type::Tuple(vec![Type::Bool, Type::Int]), &Type::Tuple(vec![Type::Bool, Type::Int])).is_ok());
        assert!(unify(&Type::Tuple(vec![Type::Bool, Type::Int]), &Type::Tuple(vec![Type::Int, Type::Int])).is_err());

        let unify_result = unify(&Type::Tuple(vec![Type::Variable("a".to_string()), Type::Int]), &Type::Tuple(vec![Type::Bool, Type::Int]));
        assert!(unify_result.is_ok());
        let unify_result = unify_result.unwrap();
        assert_eq!(unify_result.get("a"), Some(&Type::Bool));

        let unify_result = unify(&Type::Tuple(vec![Type::Bool, Type::Int]), &Type::Tuple(vec![Type::Variable("a".to_string()), Type::Int]));
        assert!(unify_result.is_ok());
        let unify_result = unify_result.unwrap();
        assert_eq!(unify_result.get("a"), Some(&Type::Bool))
    }

    #[test]
    fn test_unify_list() {
        assert!(unify(&Type::List(Box::new(Type::Bool)), &Type::List(Box::new(Type::Bool))).is_ok());
        assert!(unify(&Type::List(Box::new(Type::Int)), &Type::List(Box::new(Type::Bool))).is_err());

        let unify_result = unify(&&Type::List(Box::new(Type::Variable("a".to_string()))), &Type::List(Box::new(Type::Bool)));
        assert!(unify_result.is_ok());
        let unify_result = unify_result.unwrap();
        assert_eq!(unify_result.get("a"), Some(&Type::Bool));

        let unify_result = unify(&&Type::List(Box::new(Type::Bool)), &Type::List(Box::new(Type::Variable("a".to_string()))));
        assert!(unify_result.is_ok());
        let unify_result = unify_result.unwrap();
        assert_eq!(unify_result.get("a"), Some(&Type::Bool))
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
        assert_eq!(unify_result.get("a"), Some(&Type::Bool));
        assert_eq!(unify_result.get("b"), Some(&Type::Int));
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
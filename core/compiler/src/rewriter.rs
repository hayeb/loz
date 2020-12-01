mod flattener;
mod instantiator;
mod renamer;

use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::ast::{
    CaseRule, Expression, FunctionBody, FunctionDefinition, FunctionRule, MatchExpression, Module,
};

use crate::rewriter::flattener::flatten;
use crate::rewriter::instantiator::instantiate;
use crate::rewriter::renamer::rename;
use crate::{ADTConstructor, ADTDefinition, Import, RecordDefinition, Type, TypeScheme};

#[derive(Debug)]
pub struct RuntimeModule {
    pub name: Rc<String>,
    pub main_function_name: Rc<String>,
    pub main_function_type: Rc<Type>,

    pub functions: HashMap<Rc<String>, Monomorphized<FunctionDefinition>>,
    pub adts: HashMap<Rc<String>, Monomorphized<ADTDefinition>>,
    pub records: HashMap<Rc<String>, Monomorphized<RecordDefinition>>,
}

#[derive(Clone, Debug)]
pub struct Monomorphized<T> {
    pub base: Rc<T>,
    pub instances: HashMap<Rc<String>, Rc<T>>,
}

pub fn rewrite(
    main_module: Module,
    modules_by_name: HashMap<Rc<String>, Rc<Module>>,
) -> Rc<RuntimeModule> {
    println!("Building runtime module..");
    println!("Main module: {:#?}", main_module);

    let main_module_name = Rc::clone(&main_module.name);
    let main_function_name = Rc::new(format!("{}::main", &main_module_name));

    let (functions, adts, records) = rename(main_module, modules_by_name);
    let (functions, local_adts, local_records) = flatten(functions);

    let mut combined_adts = HashMap::new();
    combined_adts.extend(adts);
    combined_adts.extend(local_adts);

    let mut combined_records = HashMap::new();
    combined_records.extend(records);
    combined_records.extend(local_records);

    let instantiated = instantiate(
        &main_function_name,
        functions.clone(),
        combined_adts.clone(),
        combined_records.clone(),
    );
    let runtime_module = RuntimeModule {
        name: Rc::clone(&main_module_name),
        main_function_name: Rc::new("main".to_string()),
        main_function_type: Rc::clone(
            &instantiated
                .functions
                .get(&main_function_name)
                .unwrap()
                .function_type
                .as_ref()
                .unwrap()
                .enclosed_type,
        ),
        functions: functions
            .iter()
            .map(|(name, definition)| {
                (
                    Rc::clone(name),
                    Monomorphized {
                        base: Rc::clone(definition),
                        instances: instantiated
                            .functions
                            .iter()
                            .filter(|(n, _)| n.starts_with(&name.to_string()))
                            .map(|(_, d)| (Rc::clone(&d.name), Rc::clone(d)))
                            .collect(),
                    },
                )
            })
            .filter(|(_, m)| m.instances.len() > 0)
            .collect(),
        adts: combined_adts
            .iter()
            .map(|(name, definition)| {
                (
                    Rc::clone(name),
                    Monomorphized {
                        base: Rc::clone(definition),
                        instances: instantiated
                            .adts
                            .iter()
                            .filter(|(n, _)| n.starts_with(&name.to_string()))
                            .map(|(_, d)| (Rc::clone(&d.name), Rc::clone(d)))
                            .collect(),
                    },
                )
            })
            .filter(|(_, m)| m.instances.len() > 0)
            .collect(),
        records: combined_records
            .iter()
            .map(|(name, definition)| {
                (
                    Rc::clone(name),
                    Monomorphized {
                        base: Rc::clone(definition),
                        instances: instantiated
                            .records
                            .iter()
                            .filter(|(n, _)| n.starts_with(&name.to_string()))
                            .map(|(_, d)| (Rc::clone(&d.name), Rc::clone(d)))
                            .collect(),
                    },
                )
            })
            .filter(|(_, m)| m.instances.len() > 0)
            .collect(),
    };

    return Rc::new(runtime_module);
}

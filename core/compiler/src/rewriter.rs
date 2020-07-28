mod renamer;

use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::ast::{
    CaseRule, Expression, FunctionBody, FunctionDefinition, FunctionRule, MatchExpression, Module,
};

use crate::rewriter::renamer::rename;
use crate::{ADTConstructor, ADTDefinition, Import, RecordDefinition, Type, TypeScheme};

#[derive(Debug)]
pub struct RuntimeModule {
    pub name: Rc<String>,
    pub main_function_name: Rc<String>,
    pub main_function_type: Rc<Type>,
    pub functions: HashMap<Rc<String>, Rc<FunctionDefinition>>,
    pub adts: HashMap<Rc<String>, Rc<ADTDefinition>>,
    pub records: HashMap<Rc<String>, Rc<RecordDefinition>>,
}

pub fn rewrite(
    main_module: Module,
    modules_by_name: HashMap<Rc<String>, Rc<Module>>,
) -> Rc<RuntimeModule> {
    println!("Building runtime module..");

    let main_module_name = Rc::clone(&main_module.name);
    let main_function_name = Rc::new(format!("{}::main", &main_module_name));

    let (functions, adts, records) = rename(main_module, modules_by_name);
    let runtime_module = RuntimeModule {
        name: Rc::clone(&main_module_name),
        main_function_name: Rc::new("main".to_string()),
        main_function_type: Rc::clone(&functions.get(&main_function_name).unwrap().function_type.as_ref().unwrap().enclosed_type),
        functions,
        records,
        adts,
    };

    println!("Built runtime module: {:#?}", runtime_module);

    return Rc::new(runtime_module);
}

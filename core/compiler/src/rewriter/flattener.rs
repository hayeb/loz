use super::*;

pub fn flatten(
    functions: HashMap<Rc<String>, Rc<FunctionDefinition>>,
) -> (
    HashMap<Rc<String>, Rc<FunctionDefinition>>,
    HashMap<Rc<String>, Rc<ADTDefinition>>,
    HashMap<Rc<String>, Rc<RecordDefinition>>,
) {
    let mut flattened_functions = HashMap::new();
    let mut flattened_adts = HashMap::new();
    let mut flattened_records = HashMap::new();

    let mut to_flatten: Vec<Rc<FunctionDefinition>> = functions.values().cloned().collect();
    while let Some(fd) = to_flatten.pop() {
        flattened_functions.insert(Rc::clone(&fd.name), Rc::clone(&fd));
        for function_bodies in fd.function_bodies.iter() {
            for (_, local_function_definition) in function_bodies.local_function_definitions.iter()
            {
                to_flatten.insert(0, Rc::clone(local_function_definition));
            }
            for (n, local_adt_definition) in function_bodies.local_adt_definitions.iter() {
                flattened_adts.insert(Rc::clone(n), Rc::clone(local_adt_definition));
            }
            for (n, local_record_definition) in function_bodies.local_record_definitions.iter() {
                flattened_records.insert(Rc::clone(n), Rc::clone(local_record_definition));
            }
        }
    }

    (flattened_functions, flattened_adts, flattened_records)
}

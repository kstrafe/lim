//! Executable emission roots. Validation always runs on the complete program.

use std::collections::{HashMap, HashSet};

use crate::{typecheck::CheckedProgram, typed_body::NodeKind, Item};

pub(crate) fn executable_symbols(checked: &CheckedProgram<'_>) -> HashSet<String> {
    let declarations = checked.declarations();
    let names = checked
        .program()
        .items
        .iter()
        .flat_map(|item| match item {
            Item::Function(function) => vec![function.name.as_str()],
            Item::ThreadTask {
                generated_functions,
                ..
            } => generated_functions
                .iter()
                .map(|function| function.name.as_str())
                .collect(),
            _ => vec![],
        })
        .collect::<Vec<_>>();
    let names_by_id = names
        .iter()
        .filter_map(|name| declarations.function_id(name).map(|id| (id, *name)))
        .collect::<HashMap<_, _>>();
    let mut assembly_names = names
        .iter()
        .map(|name| (crate::codegen::asm_symbol(name), *name))
        .collect::<HashMap<_, _>>();
    let mut thread_workers = HashMap::new();
    for item in &checked.program().items {
        if let Item::ThreadTask {
            name,
            worker,
            generated_functions,
        } = item
        {
            thread_workers.insert(name.as_str(), (name.as_str(), worker.as_str()));
            for function in generated_functions {
                thread_workers.insert(function.name.as_str(), (name.as_str(), worker.as_str()));
            }
            assembly_names.insert(
                format!(".Llim_thread_entry_{}", crate::codegen::asm_symbol(name)),
                name,
            );
        }
    }
    let mut pending = vec!["main".to_owned()];
    let mut retained = HashSet::new();
    while let Some(name) = pending.pop() {
        if !retained.insert(name.clone()) {
            continue;
        }
        if let Some((task, worker)) = thread_workers.get(name.as_str()) {
            retained.insert((*task).to_owned());
            pending.push((*worker).to_owned());
        }
        let Some(body) = declarations.bodies.get(&name) else {
            continue;
        };
        for (index, node) in body.nodes.iter().enumerate() {
            match &node.kind {
                NodeKind::Form {
                    callee: Some(callee),
                    ..
                } => {
                    if let Some(name) = names_by_id.get(callee) {
                        pending.push((*name).to_owned());
                    }
                }
                NodeKind::Form { head, children, .. } if head == "clone" && children.len() == 2 => {
                    // #clone dispatches a concrete hook even for Copy types.
                    // It is not an ordinary source call, but its body (and
                    // transitive calls) must survive executable pruning.
                    if let Some(hook) =
                        declarations.clone_hook_name(body, crate::typed_body::NodeId(index))
                    {
                        pending.push(hook);
                    }
                }
                // Unsafe inline assembly can name functions outside ordinary
                // checked calls. Conservatively retain any referenced symbol
                // in string literals, including addresses and local entries.
                NodeKind::Literal(crate::Expr::String(text)) => {
                    for token in text.split(|c: char| {
                        !(c.is_ascii_alphanumeric() || matches!(c, '_' | '.' | '$'))
                    }) {
                        if let Some(name) = assembly_names.get(token) {
                            pending.push((*name).to_owned());
                        }
                    }
                }
                _ => {}
            }
        }
    }
    retained
}

//! Resolve physical child layouts before emitting their by-value users.
//! Layout installation is not a replacement for either semantic check.

use super::async_prepare::Planning;
use crate::{Expr, Item, Type};
use std::collections::{BTreeSet, HashMap, HashSet};

pub(crate) fn declarations(source: &str) -> Result<Vec<Item>, String> {
    crate::parse(source)
        .map_err(|error| error.to_string())?
        .into_iter()
        .filter(|source| {
            matches!(&source.expr, Expr::List(parts)
            if matches!(parts.first(), Some(Expr::Symbol(head))
                if matches!(head.as_str(), "#struct" | "#enum" | "#type")))
        })
        .map(|source| crate::parse_item(&crate::normalize_keywords(source.expr)))
        .collect()
}

pub(crate) fn emission_order(planning: &Planning) -> Result<Vec<usize>, String> {
    let mut owners = HashMap::new();
    for (index, function) in planning.functions.iter().enumerate() {
        let declaration = planning
            .interfaces
            .function(&function.model.source_name)
            .ok_or("async start interface disappeared during layout ordering")?;
        let Type::Named(frame) = &declaration.return_type else {
            return Err("async start interface has no physical frame identity".into());
        };
        owners.insert(frame.clone(), index);
        owners.insert(format!("{frame}::Cleanup"), index);
    }
    fn collect(
        ty: &Type,
        planning: &Planning,
        owners: &HashMap<String, usize>,
        seen: &mut HashSet<String>,
        dependencies: &mut BTreeSet<usize>,
    ) -> Result<(), String> {
        let ty = crate::typed_ir::resolve_type(ty, &planning.declarations.aliases)?;
        match ty {
            Type::Named(name) => {
                if let Some(owner) = owners.get(&name) {
                    dependencies.insert(*owner);
                } else if seen.insert(name.clone()) {
                    if let Some(fields) = planning.declarations.structs.get(&name) {
                        for field in fields {
                            collect(&field.ty, planning, owners, seen, dependencies)?;
                        }
                    }
                    if let Some(variants) = planning.declarations.enums.get(&name) {
                        for field in variants.iter().flat_map(|variant| &variant.fields) {
                            collect(field, planning, owners, seen, dependencies)?;
                        }
                    }
                }
            }
            Type::Array(_, 0) => {}
            Type::Array(element, _) => collect(&element, planning, owners, seen, dependencies)?,
            // Owning pointers are fixed width, but their payload determines
            // retained-reference provenance. Resolve it before erasing a cell.
            Type::PinOwned(element) | Type::PinShared(element) => {
                collect(&element, planning, owners, seen, dependencies)?
            }
            Type::Tuple(fields) => {
                for field in fields {
                    collect(&field, planning, owners, seen, dependencies)?;
                }
            }
            // Non-owning reference/pointer/slice and atomic descriptors have fixed width.
            _ => {}
        }
        Ok(())
    }
    let mut dependencies = Vec::new();
    for function in &planning.functions {
        let mut names = HashSet::new();
        let mut needed = BTreeSet::new();
        for ty in function
            .graph
            .bindings
            .iter()
            .map(|binding| &binding.ty)
            .chain(function.graph.values.iter().map(|value| &value.ty))
            .chain(function.graph.places.iter().map(|place| &place.ty))
        {
            collect(ty, planning, &owners, &mut names, &mut needed)?;
        }
        dependencies.push(needed.into_iter().collect());
    }
    order(&dependencies)
}

fn order(dependencies: &[Vec<usize>]) -> Result<Vec<usize>, String> {
    // Iterative DFS avoids imposing the host stack limit on long async chains.
    let mut state = vec![0u8; dependencies.len()];
    let mut result = Vec::new();
    for root in 0..dependencies.len() {
        let mut stack = vec![(root, false)];
        while let Some((node, exit)) = stack.pop() {
            if exit {
                state[node] = 2;
                result.push(node);
                continue;
            }
            match state[node] {
                2 => continue,
                1 => return Err("recursive by-value async frame layout dependency".into()),
                _ => {}
            }
            state[node] = 1;
            stack.push((node, true));
            for &dependency in dependencies[node].iter().rev() {
                stack.push((dependency, false));
            }
        }
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn concrete_child_layouts_preserve_source_ids_and_refresh_classification() {
        let source = include_str!("../../examples/async_composition.lim");
        let syntax = crate::prepare_program_syntax(
            source,
            std::path::Path::new("."),
            None,
            &crate::CompileConfig::default(),
            None,
        )
        .unwrap();
        let mut planning = super::super::async_prepare::prepare(&syntax).unwrap();
        assert_eq!(emission_order(&planning).unwrap(), [1, 0]);
        let tick = Type::Named("Tick".into());
        let id = planning.declarations.aggregate_id(&tick).unwrap();
        let count = planning.program.items.len();
        let child = Type::Named("Child-task".into());
        assert!(!planning.linear_types().contains_reference(&child));
        planning
            .install_generated_layouts("(#struct Child-task (#linear) (: view (#ref #u64))) ")
            .unwrap();
        assert_eq!(planning.declarations.aggregate_id(&tick), Some(id));
        assert_eq!(planning.program.items.len(), count);
        assert!(planning.linear_types().contains_reference(&child));
        assert!(!planning
            .declarations
            .deferred_layouts
            .contains_key("Child-task"));
        assert!(planning
            .declarations
            .deferred_layouts
            .contains_key("Parent-task"));
        assert_eq!(
            crate::codegen::storage_word_count(
                &child,
                &planning.declarations.structs,
                &planning.declarations.enums
            )
            .unwrap(),
            1
        );
    }
    #[test]
    fn layout_order_is_dependency_first_and_deterministic() {
        assert_eq!(
            order(&[vec![2, 1], vec![2], vec![], vec![]]).unwrap(),
            [2, 1, 0, 3]
        );
        assert!(order(&[vec![1], vec![0]])
            .unwrap_err()
            .contains("recursive"));
        assert!(order(&[vec![0]]).is_err());
    }
    #[test]
    fn owning_pointers_require_child_provenance_before_parent_classification() {
        let syntax = crate::prepare_program_syntax(
            include_str!("../../examples/async_composition.lim"),
            std::path::Path::new("."),
            None,
            &crate::CompileConfig::default(),
            None,
        )
        .unwrap();
        let mut planning = super::super::async_prepare::prepare(&syntax).unwrap();
        // Isolate the owning descriptor dependency from ordinary by-value uses.
        for function in &mut planning.functions {
            for binding in &mut function.graph.bindings {
                binding.ty = Type::U64;
            }
            for value in &mut function.graph.values {
                value.ty = Type::U64;
            }
            for place in &mut function.graph.places {
                place.ty = Type::U64;
            }
        }
        planning.functions[0].graph.bindings[0].ty =
            Type::PinOwned(Box::new(Type::Named("Child-task".into())));
        assert_eq!(emission_order(&planning).unwrap(), [1, 0]);
    }
    #[test]
    fn long_layout_chains_do_not_recurse_on_the_host_stack() {
        let dependencies = (0..10000)
            .map(|index| {
                if index == 9999 {
                    vec![]
                } else {
                    vec![index + 1]
                }
            })
            .collect::<Vec<_>>();
        let result = order(&dependencies).unwrap();
        assert_eq!(result.len(), 10000);
        assert_eq!(result[0], 9999);
        assert_eq!(result[9999], 0);
    }

    #[test]
    fn zero_length_layout_markers_do_not_require_the_element_layout() {
        let marker = Type::Array(Box::new(Type::Named("Deferred-child".into())), 0);
        assert_eq!(
            crate::codegen::storage_word_count(&marker, &HashMap::new(), &HashMap::new()).unwrap(),
            0
        );
    }
}

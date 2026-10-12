//! Compile-time mapping between typed loan slots and flat value words.
//! A layout is not provenance: only a real typed write supplies loan origins.

use crate::typed_body::{Body, NodeId, NodeKind, ParameterLoanSeed};
use crate::typed_ir::Declarations;
use crate::typed_place::Segment;
use crate::Type;
use std::collections::HashMap;

pub(crate) fn parameter_candidates(
    body: &Body,
    declarations: &Declarations,
) -> Vec<Vec<ParameterLoanSeed>> {
    let mut result = vec![Vec::new(); body.parameter_count];
    if !body
        .word_layouts
        .values()
        .any(|layout| !layout.slots.is_empty())
        && !body
            .call_word_input_requirements
            .values()
            .any(|inputs| !inputs.is_empty())
    {
        return result;
    }
    for (index, binding) in body.bindings.iter().take(body.parameter_count).enumerate() {
        collect_numeric_arrays(
            &binding.ty,
            declarations,
            &mut Vec::new(),
            &mut std::collections::HashSet::new(),
            &mut result[index],
        );
    }
    result
}

fn collect_numeric_arrays(
    ty: &Type,
    declarations: &Declarations,
    path: &mut Vec<Segment>,
    seen: &mut std::collections::HashSet<String>,
    slots: &mut Vec<ParameterLoanSeed>,
) {
    let Ok(ty) = crate::typed_ir::resolve_type(ty, &declarations.aliases) else {
        return;
    };
    match &ty {
        Type::Array(element, length) if **element == Type::U64 => {
            if *length != 0 {
                path.push(Segment::DynamicIndex);
                slots.push(ParameterLoanSeed {
                    storage: path.clone(),
                    mutable: false,
                    pinned: false,
                    owned_allocation: false,
                });
                path.pop();
            }
        }
        Type::Named(name)
            if declarations.structs.contains_key(name) && seen.insert(name.clone()) =>
        {
            for field in &declarations.structs[name] {
                path.push(Segment::Field(
                    declarations.field_id(&ty, &field.name).unwrap(),
                ));
                collect_numeric_arrays(&field.ty, declarations, path, seen, slots);
                path.pop();
            }
            seen.remove(name);
        }
        Type::Tuple(fields) => {
            for (index, field) in fields.iter().enumerate() {
                path.push(Segment::Tuple(index));
                collect_numeric_arrays(field, declarations, path, seen, slots);
                path.pop();
            }
        }
        Type::Array(element, length) => {
            if *length != 0 {
                path.push(Segment::DynamicIndex);
                collect_numeric_arrays(element, declarations, path, seen, slots);
                path.pop();
            }
        }
        _ => (),
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Slot {
    pub path: Vec<Segment>,
    pub offset: usize,
    pub mutable: bool,
    pub pinned: bool,
    pub owned_allocation: bool,
}

#[derive(Clone, Debug)]
pub(crate) struct Layout {
    pub words: usize,
    pub slots: Vec<Slot>,
}

pub(crate) fn layouts(body: &Body, declarations: &Declarations) -> HashMap<NodeId, Layout> {
    body.nodes
        .iter()
        .enumerate()
        .filter_map(|(index, node)| {
            let NodeKind::Form {
                head,
                children,
                callee: None,
                ..
            } = &node.kind
            else {
                return None;
            };
            let ty = match (head.as_str(), children.len()) {
                ("word-write", 4) => body.nodes[children[3].0].ty.as_ref()?,
                ("word-read", 3) => node.ty.as_ref()?,
                ("word-view", 3) => match node.ty.as_ref()? {
                    Type::Reference { target, .. } | Type::PinnedReference { target, .. } => target,
                    _ => return None,
                },
                _ => return None,
            };
            let mut slots = Vec::new();
            // Deferred layouts stay unsupported rather than acquiring fabricated
            // slots from a signature whose physical representation is unknown.
            let words = collect(ty, declarations, &mut Vec::new(), 0, &mut slots).ok()?;
            Some((NodeId(index), Layout { words, slots }))
        })
        .collect()
}

fn collect(
    ty: &Type,
    declarations: &Declarations,
    path: &mut Vec<Segment>,
    offset: usize,
    slots: &mut Vec<Slot>,
) -> Result<usize, String> {
    let ty = crate::typed_ir::resolve_type(ty, &declarations.aliases)?;
    let words =
        crate::codegen::storage_word_count(&ty, &declarations.structs, &declarations.enums)?;
    if declarations.reference_storage_slots(&ty).is_empty() {
        return Ok(words);
    }
    match &ty {
        Type::Reference { .. }
        | Type::PinnedReference { .. }
        | Type::Slice(_)
        | Type::MutableSlice(_)
        | Type::PinOwned(_) => {
            slots.push(Slot {
                path: path.clone(),
                offset,
                mutable: matches!(
                    &ty,
                    Type::Reference { mutable: true, .. }
                        | Type::PinnedReference { mutable: true, .. }
                        | Type::MutableSlice(_)
                        | Type::PinOwned(_)
                ),
                pinned: matches!(&ty, Type::PinnedReference { .. } | Type::PinOwned(_)),
                owned_allocation: matches!(&ty, Type::PinOwned(_)),
            });
        }
        Type::Named(name) if declarations.structs.contains_key(name) => {
            let mut start = offset;
            for field in &declarations.structs[name] {
                path.push(Segment::Field(
                    declarations.field_id(&ty, &field.name).unwrap(),
                ));
                start += collect(&field.ty, declarations, path, start, slots)?;
                path.pop();
            }
        }
        Type::Named(name) if declarations.enums.contains_key(name) => {
            for variant in &declarations.enums[name] {
                let mut start = offset + 1;
                for (index, field) in variant.fields.iter().enumerate() {
                    path.push(Segment::Payload(
                        declarations.variant_id(&ty, &variant.name).unwrap(),
                        index,
                    ));
                    start += collect(field, declarations, path, start, slots)?;
                    path.pop();
                }
            }
        }
        Type::Tuple(fields) => {
            let mut start = offset;
            for (index, field) in fields.iter().enumerate() {
                path.push(Segment::Tuple(index));
                start += collect(field, declarations, path, start, slots)?;
                path.pop();
            }
        }
        Type::Array(element, length) => {
            let mut start = offset;
            for index in 0..*length {
                path.push(Segment::Index(index as u128));
                start += collect(element, declarations, path, start, slots)?;
                path.pop();
            }
        }
        _ => (),
    }
    Ok(words)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn large_numeric_input_uses_one_symbolic_candidate_and_one_exact_requirement() {
        let source = "(#struct Holder (: value (#ref #u64)))
          (#fn read (: words (#array #u64 1000000000)) #u64
            (#let restored Holder (#unsafe (#word-read Holder (#borrow-slice words 7usize 8usize))))
            (#let answer #u64 (#deref (#get restored value)))
            (#forget restored) (#return answer))";
        let declarations = crate::typecheck::resolve_program_for_analysis(
            &crate::parse_program(source).unwrap(),
            true,
        )
        .unwrap();
        let body = &declarations.bodies["read"];
        assert_eq!(body.word_parameter_candidates[0].len(), 1);
        assert_eq!(
            body.word_parameter_candidates[0][0].storage,
            vec![Segment::DynamicIndex]
        );
        assert_eq!(body.word_input_requirements.len(), 1);
        assert_eq!(
            body.word_input_requirements[0].input_storage,
            vec![Segment::Index(7)]
        );
    }
}

//! Compile-time mapping between typed loan slots and flat value words.
//! A layout is not provenance: only a real typed write supplies loan origins.

use crate::typed_body::{Body, NodeId, NodeKind};
use crate::typed_ir::Declarations;
use crate::typed_place::Segment;
use crate::Type;
use std::collections::HashMap;

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

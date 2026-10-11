//! Field-aware owning storage selected from checked aggregate place recipes.
//!
//! The emitter gives each part an independent Empty/Full cell. These layouts
//! describe representation only; source ownership and ordinary emitted-code
//! validation still establish permission to move, rebuild and borrow fields.

use std::collections::BTreeSet;

use super::async_exec::{Action, AddressProjection, AddressRoot, Graph, LoadKind};
use super::async_lend::{Access, Plan};
use crate::linearcheck::LinearTypes;
use crate::typed_body::BindingId;
use crate::typed_ir::{Declarations, FieldId};
use crate::Type;

pub(crate) struct Field {
    pub id: FieldId,
    pub name: String,
    pub ty: Type,
}

pub(crate) struct Layout {
    pub binding: BindingId,
    pub constructor: String,
    pub fields: Vec<Field>,
}

pub(crate) fn layouts(
    graph: &Graph,
    declarations: &Declarations,
    lending: Option<&Plan>,
    types: &LinearTypes,
) -> Result<Vec<Layout>, String> {
    let mut selected = BTreeSet::new();
    for located in graph.blocks.iter().flat_map(|block| &block.actions) {
        let place = match located.action {
            Action::Release { place, .. } | Action::Store { place, .. } => place,
            Action::Load {
                place,
                kind: LoadKind::Read,
                ..
            } if !types.can_repeat(&graph.places[place.0].ty)
                && !matches!(
                    located.source.and_then(|source| lending?.access(source)),
                    Some(Access::Lend(_))
                ) =>
            {
                place
            }
            _ => continue,
        };
        let descriptor = &graph.places[place.0];
        if let (AddressRoot::Local(binding), Some(AddressProjection::Field(_))) =
            (&descriptor.root, descriptor.projections.first())
        {
            // Ordinary Copy, reference-free field stores already have a
            // stable whole-owner representation and need no decomposition.
            if matches!(located.action, Action::Store { .. })
                && types.can_repeat(&descriptor.ty)
                && !types.contains_reference(&descriptor.ty)
            {
                continue;
            }
            selected.insert(binding.0);
        }
    }
    selected
        .into_iter()
        .map(|index| {
            let binding = BindingId(index);
            let Type::Named(constructor) = crate::typed_ir::resolve_type(
                &graph.bindings[binding.0].ty,
                &declarations.aliases,
            )?
            else {
                return Err("field storage requires a concrete struct owner".into());
            };
            let fields = declarations
                .structs
                .get(&constructor)
                .ok_or("field storage owner is not a concrete struct")?;
            let fields = fields
                .iter()
                .map(|field| {
                    Ok(Field {
                        id: declarations
                            .field_id(&Type::Named(constructor.clone()), &field.name)
                            .ok_or("field storage lost its checked field identity")?,
                        name: field.name.clone(),
                        ty: field.ty.clone(),
                    })
                })
                .collect::<Result<Vec<_>, String>>()?;
            Ok(Layout {
                binding,
                constructor,
                fields,
            })
        })
        .collect()
}

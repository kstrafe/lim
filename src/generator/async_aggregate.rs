//! Field-aware owning storage selected from checked aggregate place recipes.
//!
//! The emitter gives each part an independent Empty/Full cell. These layouts
//! describe representation only; source ownership and ordinary emitted-code
//! validation still establish permission to move, rebuild and borrow fields.

use std::collections::BTreeMap;

use super::async_exec::{Action, AddressProjection, AddressRoot, Graph, LoadKind};
use super::async_lend::{Access, Plan};
use crate::linearcheck::LinearTypes;
use crate::typed_body::BindingId;
use crate::typed_ir::{Declarations, FieldId};
use crate::Type;

pub(crate) struct Field {
    pub path: Vec<FieldId>,
    pub name: String,
    pub ty: Type,
}

#[derive(Clone)]
pub(crate) struct Shape {
    pub constructor: String,
    pub ty: Type,
    pub fields: Vec<ShapeField>,
}

#[derive(Clone)]
pub(crate) struct ShapeField {
    pub id: FieldId,
    pub name: String,
    pub ty: Type,
    pub nested: Option<Box<Shape>>,
}

pub(crate) struct Layout {
    pub binding: BindingId,
    pub shape: Shape,
    pub fields: Vec<Field>,
}

pub(crate) fn layouts(
    graph: &Graph,
    declarations: &Declarations,
    lending: Option<&Plan>,
    types: &LinearTypes,
) -> Result<Vec<Layout>, String> {
    let mut selected = BTreeMap::<usize, Vec<Vec<FieldId>>>::new();
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
        if matches!(located.action, Action::Release { .. })
            && types.can_repeat(&descriptor.ty)
            && !types.contains_reference(&descriptor.ty)
        {
            // Releasing a plain Copy projection discards a copy. It neither
            // empties a field nor requires split owning storage.
            continue;
        }
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
            let path = descriptor
                .projections
                .iter()
                .map(|projection| match projection {
                    AddressProjection::Field(field) => Some(*field),
                    _ => None,
                })
                .collect::<Option<Vec<_>>>();
            selected
                .entry(binding.0)
                .or_default()
                .push(path.unwrap_or_else(|| match descriptor.projections[0] {
                    AddressProjection::Field(field) => vec![field],
                    _ => unreachable!(),
                }));
        }
    }
    selected
        .into_iter()
        .map(|(index, paths)| {
            let binding = BindingId(index);
            let shape = shape(&graph.bindings[index].ty, &[], &paths, declarations)?;
            let mut fields = Vec::new();
            flatten(&shape, &[], "", &mut fields);
            Ok(Layout {
                binding,
                shape,
                fields,
            })
        })
        .collect()
}

fn shape(
    ty: &Type,
    prefix: &[FieldId],
    paths: &[Vec<FieldId>],
    declarations: &Declarations,
) -> Result<Shape, String> {
    let Type::Named(constructor) = crate::typed_ir::resolve_type(ty, &declarations.aliases)? else {
        return Err("field storage requires a concrete struct owner".into());
    };
    let fields = declarations
        .structs
        .get(&constructor)
        .ok_or("field storage owner is not a concrete struct")?;
    let fields = fields
        .iter()
        .map(|field| {
            let id = declarations
                .field_id(&Type::Named(constructor.clone()), &field.name)
                .ok_or("field storage lost its checked field identity")?;
            let mut path = prefix.to_vec();
            path.push(id);
            let split = paths
                .iter()
                .any(|selected| selected.starts_with(&path) && selected.len() > path.len());
            Ok(ShapeField {
                id,
                name: field.name.clone(),
                ty: field.ty.clone(),
                nested: if split {
                    Some(Box::new(shape(&field.ty, &path, paths, declarations)?))
                } else {
                    None
                },
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    Ok(Shape {
        constructor,
        ty: ty.clone(),
        fields,
    })
}

fn flatten(shape: &Shape, prefix: &[FieldId], name: &str, output: &mut Vec<Field>) {
    for field in &shape.fields {
        let mut path = prefix.to_vec();
        path.push(field.id);
        let name = if name.is_empty() {
            field.name.clone()
        } else {
            format!("{name}.{}", field.name)
        };
        if let Some(nested) = &field.nested {
            flatten(nested, &path, &name, output);
        } else {
            output.push(Field {
                path,
                name,
                ty: field.ty.clone(),
            });
        }
    }
}

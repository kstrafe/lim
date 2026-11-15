//! Ordinary projection contracts for evaluated async reference handles.
//! Implementation detail of built-in code generation, not runtime semantics.
//!
//! A projection is checked against concrete declaration identities, not the
//! spelling of a field. Its ordinary generated function borrows from the
//! incoming referent; it never borrows a frame cell holding that handle.
//! This is representation validation, not a substitute for either the source
//! or the generated ordinary borrow proof. Selected addresses with checks and
//! frame-local referents still require their separate storage plans.
#![allow(dead_code)]

use crate::generator::async_exec::{
    AddressProjection, AddressRoot, Graph, PlaceDescriptor, ValueId,
};
use crate::typed_ir::{resolve_type, Declarations};
use crate::Type;

pub(crate) struct Reborrow {
    pub root: ValueId,
    pub input: Type,
    pub output: Type,
    fields: Vec<String>,
    mutable: bool,
    pinned: bool,
}

impl Reborrow {
    pub fn new(
        graph: &Graph,
        place: &PlaceDescriptor,
        declarations: &Declarations,
        mutable: bool,
        pinned: bool,
    ) -> Result<Self, String> {
        Self::project(graph, place, declarations, mutable, pinned)
    }

    fn project(
        graph: &Graph,
        place: &PlaceDescriptor,
        declarations: &Declarations,
        mutable: bool,
        pinned: bool,
    ) -> Result<Self, String> {
        let AddressRoot::Value(root) = place.root else {
            return Err(
                "local borrows require stable frame-owner storage, not a handle projection".into(),
            );
        };
        let input = graph
            .values
            .get(root.0)
            .ok_or("borrow projection has no evaluated handle")?
            .ty
            .clone();
        let (mut target, exclusive, input_pinned) =
            match resolve_type(&input, &declarations.aliases)? {
                Type::Reference { mutable, target } => (*target, mutable, false),
                Type::PinnedReference { mutable, target } => (*target, mutable, true),
                _ => return Err("borrow projection requires an evaluated reference handle".into()),
            };
        if mutable && !exclusive {
            return Err("exclusive projection cannot borrow through a shared handle".into());
        }
        let Some((AddressProjection::Dereference, projections)) = place.projections.split_first()
        else {
            return Err("borrow projection lost its checked dereference boundary".into());
        };
        if !place.checks().is_empty() {
            return Err("borrow projection requires a path without deferred address checks".into());
        }
        let (fields, leaf) = checked_path(target, projections, &place.ty, declarations)?;
        let pinned = pinned || (fields.is_empty() && input_pinned);
        target = leaf;
        let output = if pinned {
            Type::PinnedReference {
                mutable,
                target: Box::new(target),
            }
        } else {
            Type::Reference {
                mutable,
                target: Box::new(target),
            }
        };
        Ok(Self {
            root,
            input,
            output,
            fields,
            mutable,
            pinned,
        })
    }

    /// Keep the actual source reference as a named function parameter. This
    /// makes all nested projections ordinary variable-rooted places for both
    /// the borrow checker and native address emission, without moving owners.
    pub fn declaration(&self, name: &str, argument: &str) -> String {
        let place = self.place(argument);
        format!(
            "(#fn {name} (({argument} {})) {}\n\
            (#return (#{}borrow{} {place})))",
            crate::type_source(&self.input),
            crate::type_source(&self.output),
            if self.pinned { "pin-" } else { "" },
            if self.mutable { "-mut" } else { "" }
        )
    }

    fn place(&self, argument: &str) -> String {
        if self.fields.is_empty() {
            return format!("(#deref {argument})");
        }
        self.fields
            .iter()
            .fold(argument.to_owned(), |place, field| {
                format!("(#get {place} {field})")
            })
    }
}

/// Shared representation validation for external handles and stable owners.
/// The returned names render already checked declaration identities; they do
/// not perform field lookup during runtime evaluation.
pub(crate) fn checked_path(
    mut target: Type,
    projections: &[AddressProjection],
    leaf: &Type,
    declarations: &Declarations,
) -> Result<(Vec<String>, Type), String> {
    let mut fields = Vec::new();
    for projection in projections {
        target = resolve_type(&target, &declarations.aliases)?;
        match projection {
            AddressProjection::Field(field) => {
                let Type::Named(owner) = &target else {
                    return Err("borrow projection lost its checked struct type".into());
                };
                let declaration = declarations
                    .structs
                    .get(owner)
                    .and_then(|fields| fields.get(field.index))
                    .ok_or("borrow projection has no checked field")?;
                if declarations.field_id(&target, &declaration.name) != Some(*field) {
                    return Err("borrow projection lost its checked field identity".into());
                }
                fields.push(declaration.name.clone());
                target = declaration.ty.clone();
            }
            AddressProjection::Tuple(index) => {
                let Type::Tuple(elements) = target else {
                    return Err("borrow projection lost its checked tuple type".into());
                };
                target = elements
                    .get(*index)
                    .cloned()
                    .ok_or("borrow projection tuple index is out of bounds")?;
                fields.push(index.to_string());
            }
            _ => {
                return Err(
                    "borrow projection with selected addresses requires a checked snapshot".into(),
                )
            }
        }
    }
    target = resolve_type(&target, &declarations.aliases)?;
    if target != resolve_type(leaf, &declarations.aliases)? {
        return Err("borrow projection disagrees with its checked leaf type".into());
    }
    Ok((fields, target))
}

pub(crate) struct Write {
    pub projection: Reborrow,
    pub value: Type,
}

impl Write {
    pub fn new(
        graph: &Graph,
        place: &PlaceDescriptor,
        declarations: &Declarations,
        types: &crate::linearcheck::LinearTypes,
    ) -> Result<Self, String> {
        let AddressRoot::Value(root) = place.root else {
            return Err("reference write requires an evaluated handle".into());
        };
        let input = graph
            .values
            .get(root.0)
            .ok_or("reference write lost its input type")?;
        let pinned = matches!(
            resolve_type(&input.ty, &declarations.aliases)?,
            Type::PinnedReference { .. }
        );
        let projection = Reborrow::project(graph, place, declarations, true, pinned)?;
        let (Type::Reference { target, .. } | Type::PinnedReference { target, .. }) =
            &projection.output
        else {
            unreachable!()
        };
        let value = target.as_ref().clone();
        if !types.can_repeat(&value) || types.contains_reference(&value) {
            return Err("reference writes to owning or reference-bearing leaves require checked restoration storage".into());
        }
        Ok(Self { projection, value })
    }

    pub fn declaration(&self, name: &str, argument: &str, value: &str) -> String {
        let projection = &self.projection;
        let target = if projection.fields.is_empty() {
            argument.to_owned()
        } else {
            format!(
                "(#{}borrow-mut {})",
                if projection.pinned { "pin-" } else { "" },
                projection.place(argument)
            )
        };
        let write = if projection.pinned {
            format!("(#unsafe (#pin-write {target} {value}))")
        } else {
            format!("(#deref-set {target} {value})")
        };
        format!(
            "(#fn {name} (({argument} {}) ({value} {})) ()\n{write}\n(#return ()))",
            crate::type_source(&projection.input),
            crate::type_source(&self.value)
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::generator::async_exec::{Action, PlaceId};
    use crate::typed_body::BindingId;

    fn fixture(
        handle: &str,
    ) -> (
        Graph,
        PlaceDescriptor,
        Declarations,
        crate::linearcheck::LinearTypes,
    ) {
        fixture_with_scalar(handle, "#u64")
    }

    fn fixture_with_scalar(
        handle: &str,
        scalar: &str,
    ) -> (
        Graph,
        PlaceDescriptor,
        Declarations,
        crate::linearcheck::LinearTypes,
    ) {
        let source = format!(
            "#struct Owner (#linear) ((value #u64))
#type Scalar {scalar}
#struct Outer () ((pair (#tuple Scalar Scalar)))
#type View ({handle} Outer)
#fn project ((input View)) ({handle} Scalar)
              (#return (#{}borrow{} (#get (#get input pair) 1)))\n",
            if handle.starts_with("#pin") {
                "pin-"
            } else {
                ""
            },
            if handle.ends_with("mut") { "-mut" } else { "" }
        );
        let program = crate::parse_program(&source).unwrap();
        let declarations = crate::typecheck::resolve_program_for_analysis(&program, true).unwrap();
        let graph =
            crate::generator::async_exec::build(&declarations.bodies["project"], &[]).unwrap();
        let place = graph
            .blocks
            .iter()
            .flat_map(|block| &block.actions)
            .find_map(|action| {
                if let Action::Borrow { place, .. } = action.action {
                    Some(place)
                } else {
                    None
                }
            })
            .unwrap();
        let descriptor = graph.places[place.0].clone();
        let types = crate::linearcheck::LinearTypes::from_program(&program);
        (graph, descriptor, declarations, types)
    }

    #[test]
    fn aliases_and_nested_tuple_fields_generate_ordinary_checked_projections() {
        for handle in ["#ref", "#ref-mut", "#pin-ref", "#pin-ref-mut"] {
            let (mut graph, place, declarations, _) = fixture(handle);
            let AddressRoot::Value(root) = place.root else {
                unreachable!()
            };
            graph.values[root.0].ty = Type::Named("View".into());
            let mutable = handle.ends_with("mut");
            let pinned = handle.starts_with("#pin");
            let projection = Reborrow::new(&graph, &place, &declarations, mutable, pinned).unwrap();
            assert_eq!(projection.input, Type::Named("View".into()));
            assert!(projection
                .declaration("generated", "input")
                .contains("(#get (#get input pair) 1)"));
            let source = format!(
                "#type Scalar #u64
#struct Outer () ((pair (#tuple Scalar Scalar)))
#type View ({handle} Outer)
 {}",
                projection.declaration("generated", "input")
            );
            let program = crate::parse_program(&source).unwrap();
            crate::CheckedProgram::validate(&program)
                .unwrap_or_else(|error| panic!("{error}\n{source}"));
        }
    }

    #[test]
    fn direct_dereference_reborrows_generate_checked_whole_referent_helpers() {
        for handle in ["#ref", "#ref-mut", "#pin-ref", "#pin-ref-mut"] {
            let (graph, mut place, declarations, _) = fixture(handle);
            place.projections.truncate(1);
            place.ty = Type::Named("Outer".into());
            let result = Reborrow::new(
                &graph,
                &place,
                &declarations,
                handle.ends_with("mut"),
                false,
            )
            .unwrap();
            assert_eq!(result.pinned, handle.starts_with("#pin"));
            let generated = result.declaration("generated", "input");
            assert!(generated.contains("(#deref input)"));
            let source = format!(
                "#type Scalar #u64\n#struct Outer () ((pair (#tuple Scalar Scalar)))\n {generated}"
            );
            let program = crate::parse_program(&source).unwrap();
            crate::CheckedProgram::validate(&program)
                .unwrap_or_else(|error| panic!("{error}\n{source}"));
        }
    }

    #[test]
    fn field_identity_leaf_type_and_tuple_index_are_checked_without_panics() {
        let (graph, place, declarations, _) = fixture("#ref-mut");
        let mut bad = place.clone();
        if let AddressProjection::Field(field) = &mut bad.projections[1] {
            field.index = usize::MAX;
        }
        assert!(Reborrow::new(&graph, &bad, &declarations, true, false).is_err());
        let mut bad = place.clone();
        let wrong_owner = declarations
            .field_id(&Type::Named("Owner".into()), "value")
            .unwrap();
        bad.projections[1] = AddressProjection::Field(wrong_owner);
        assert!(Reborrow::new(&graph, &bad, &declarations, true, false).is_err());
        let mut bad = place.clone();
        bad.ty = Type::Bool;
        assert!(Reborrow::new(&graph, &bad, &declarations, true, false).is_err());
        let mut bad = place.clone();
        bad.projections[2] = AddressProjection::Tuple(usize::MAX);
        assert!(Reborrow::new(&graph, &bad, &declarations, true, false).is_err());
        let mut bad = place;
        bad.projections.remove(0);
        assert!(Reborrow::new(&graph, &bad, &declarations, true, false).is_err());
    }

    #[test]
    fn local_storage_and_selected_addresses_do_not_use_handle_projection() {
        let (graph, place, declarations, _) = fixture("#ref-mut");
        let mut bad = place.clone();
        bad.root = AddressRoot::Local(BindingId(0));
        assert!(Reborrow::new(&graph, &bad, &declarations, true, false).is_err());
        let mut bad = place;
        bad.projections.push(AddressProjection::Index(ValueId(0)));
        assert!(!bad.checks().is_empty());
        assert!(Reborrow::new(&graph, &bad, &declarations, true, false).is_err());
        // Already evaluated checks are not sufficient to invent a stable
        // selected-address representation either.
        bad.checked_prefix = bad.projections.len();
        bad.parent = Some(PlaceId(0));
        assert!(Reborrow::new(&graph, &bad, &declarations, true, false).is_err());
    }

    #[test]
    fn shared_handles_cannot_authorize_exclusive_projection_or_writes() {
        for handle in ["#ref", "#pin-ref"] {
            let (graph, place, declarations, types) = fixture(handle);
            assert!(Reborrow::new(&graph, &place, &declarations, true, false).is_err());
            assert!(Write::new(&graph, &place, &declarations, &types).is_err());
        }
    }

    #[test]
    fn plain_leaf_writes_generate_checked_ordinary_functions() {
        for handle in ["#ref-mut", "#pin-ref-mut"] {
            let (graph, place, declarations, types) = fixture(handle);
            let write = Write::new(&graph, &place, &declarations, &types).unwrap();
            assert_eq!(write.value, Type::U64);
            let source = format!(
                "#type Scalar #u64
#struct Outer () ((pair (#tuple Scalar Scalar)))
#type View ({handle} Outer)
 {}",
                write.declaration("generated", "input", "value")
            );
            let program = crate::parse_program(&source).unwrap();
            crate::CheckedProgram::validate(&program)
                .unwrap_or_else(|error| panic!("{error}\n{source}"));
        }
    }

    #[test]
    fn writes_do_not_invent_restoration_for_owners_or_reference_bearing_leaves() {
        for scalar in ["Owner", "(#ref #u64)", "(#ref-mut #u64)"] {
            let (graph, place, declarations, types) = fixture_with_scalar("#ref-mut", scalar);
            let error = Write::new(&graph, &place, &declarations, &types)
                .err()
                .unwrap();
            assert!(error.contains("restoration storage"), "{error}");
        }
    }
}

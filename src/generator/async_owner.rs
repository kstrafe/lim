//! Stable owner projections for the pinned executable async graph.
//! Implementation detail of built-in code generation, not runtime semantics.
//!
//! Local bindings are physically initialized only when their source Bind runs.
//! Borrowing uses their actual Full payload in the stationary frame; neither
//! factory-time hoisting nor copying an owner creates that address. This plan
//! checks representation only. Source and generated ordinary checking remain
//! mandatory, including ownership, self-aliasing and cancellation contracts.
#![allow(dead_code)]

use crate::generator::async_exec::{Action, AddressRoot, Graph, PlaceDescriptor};
use crate::typed_body::BindingId;
use crate::typed_ir::{resolve_type, Declarations};
use crate::Type;

pub(crate) struct Borrow {
    pub binding: BindingId,
    pub input: Type,
    pub output: Type,
    pub mutable: bool,
    fields: Vec<String>,
}

pub(crate) fn validate_mutability(
    graph: &Graph,
    binding: BindingId,
    mutable: bool,
) -> Result<(), String> {
    if mutable
        && !(binding.0 < graph.parameter_count && graph.mutable_parameters.contains(&binding))
        && !graph
            .blocks
            .iter()
            .flat_map(|block| &block.actions)
            .any(|action| match &action.action {
                Action::Bind {
                    binding: declared,
                    mutable,
                    ..
                } => *declared == binding && *mutable,
                Action::Commit(pattern) => {
                    (pattern.mutable || pattern.borrow_mode.is_some_and(|mode| mode.mutable))
                        && pattern.bindings.contains(&binding)
                }
                _ => false,
            })
    {
        return Err("stable owner borrow cannot make an immutable binding exclusive".into());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::generator::async_exec::{AddressProjection, ValueId};

    fn fixture(mutable: bool, whole: bool) -> (Graph, PlaceDescriptor, Declarations) {
        let path = if whole {
            "owner"
        } else {
            "(#get (#get owner pair) 1)"
        };
        let leaf = if whole { "Outer" } else { "#u64" };
        let source = format!("#struct Outer (#linear) ((pair (#tuple #u64 #u64)))
#type Owner Outer
#fn work {{ #params = ((seed #u64)); #returns = #u64; #body = (
              (#let-mut owner Owner (#struct-literal Outer ((pair (#tuple (#tuple #u64 #u64) 7u64 seed)))))
              (#let view (#pin-ref{} {leaf}) (#pin-borrow{} {path}))
              (#drop view) (#forget owner) (#return seed) ); }}\n",
            if mutable { "-mut" } else { "" }, if mutable { "-mut" } else { "" });
        let program = crate::parse_program(&source).unwrap();
        let declarations = crate::typecheck::resolve_program_for_analysis(&program, true).unwrap();
        let graph = crate::generator::async_exec::build(&declarations.bodies["work"], &[]).unwrap();
        let place = graph
            .blocks
            .iter()
            .flat_map(|block| &block.actions)
            .find_map(|action| match action.action {
                Action::Borrow { place, .. } => Some(place),
                _ => None,
            })
            .unwrap();
        let place = graph.places[place.0].clone();
        (graph, place, declarations)
    }

    #[test]
    fn stable_whole_and_nested_owner_projections_use_checked_ordinary_functions() {
        for mutable in [false, true] {
            for whole in [false, true] {
                let (graph, place, declarations) = fixture(mutable, whole);
                let plan = Borrow::new(&graph, &place, &declarations, mutable, true, true).unwrap();
                let declaration = crate::generator::format_generated_syntax(
                    &plan.declaration("project", "input"),
                )
                .unwrap();
                let source = format!(
                    "#struct Outer (#linear) ((pair (#tuple #u64 #u64)))\n{declaration}"
                );
                let program = crate::parse_program(&source).unwrap();
                crate::CheckedProgram::validate(&program)
                    .unwrap_or_else(|error| panic!("{error}\n{source}"));
                assert_eq!(
                    plan.binding,
                    BindingId(
                        graph
                            .bindings
                            .iter()
                            .position(|binding| binding.name == "owner")
                            .unwrap()
                    )
                );
                if whole {
                    assert!(source.contains("(#return input)"));
                } else {
                    assert!(source.contains("(#get (#get input pair) 1)"));
                }
            }
        }
    }

    #[test]
    fn ordinary_projection_preserves_nested_exclusive_reference_identity() {
        let target = Box::new(Type::Named("View".into()));
        let plan = Borrow {
            binding: BindingId(0),
            input: Type::PinnedReference {
                mutable: false,
                target: target.clone(),
            },
            output: Type::Reference {
                mutable: false,
                target,
            },
            mutable: false,
            fields: Vec::new(),
        };
        let declaration = plan.declaration("project", "input");
        assert!(declaration.contains("(#ptr-borrow projected (#ref-ptr projected))"));
        let declaration = crate::generator::format_generated_syntax(&declaration).unwrap();
        let source = format!(
            "#struct View (#linear) ((value (#ref-mut #u64)))
{declaration}
#fn read-view {{ #params = ((view (#ref View))); #returns = #u64; #body = ( (#return (#deref (#get view value))) ); }}
#fn main {{ #params = (); #returns = #u64; #effects = ((#effects-of project)); #body = (
              (#let-mut owner #u64 42u64)
              (#let view View (#struct-literal View ((value (#borrow-mut owner)))))
              (#let borrowed (#ref View) (#call project ((input (#pin-borrow view)))))
              (#let answer #u64 (#call read-view ((view borrowed))))
              (#forget borrowed) (#forget view) (#return answer) ); }}\n"
        );
        crate::CheckedProgram::validate(&crate::parse_program(&source).unwrap())
            .unwrap_or_else(|error| panic!("{error}\n{source}"));
        let invalid = source.replace("(#let answer #u64", "(#set owner 99u64)\n  (#let answer #u64");
        let error = crate::check_types(&crate::parse_program(&invalid).unwrap()).unwrap_err();
        assert!(error.contains("borrow"), "{error}");
    }

    #[test]
    fn parameter_owner_projections_require_explicit_mutability_metadata() {
        let source = "#struct Owner (#linear) ((value #u64))
#fn work { #params = ((#mut owner Owner)); #returns = #u64; #body = (
              (#let view (#pin-ref-mut #u64) (#pin-borrow-mut (#get owner value)))
              (#drop view) (#forget owner) (#return 42u64) ); }\n";
        let program = crate::parse_program(source).unwrap();
        let declarations = crate::typecheck::resolve_program_for_analysis(&program, true).unwrap();
        let mut graph =
            crate::generator::async_exec::build(&declarations.bodies["work"], &[]).unwrap();
        assert!(graph.mutable_parameters.contains(&BindingId(0)));
        assert!(validate_mutability(&graph, BindingId(0), true).is_ok());
        graph.mutable_parameters.clear();
        assert!(validate_mutability(&graph, BindingId(0), true).is_err());
        assert!(validate_mutability(&graph, BindingId(0), false).is_ok());
        graph
            .mutable_parameters
            .insert(BindingId(graph.parameter_count));
        assert!(graph.validate().is_err());
    }

    #[test]
    fn mutable_owner_projection_requires_the_actual_declared_mutable_binding() {
        let (mut graph, place, declarations) = fixture(true, false);
        let plan = Borrow::new(&graph, &place, &declarations, true, true, true).unwrap();
        for action in graph.blocks.iter_mut().flat_map(|block| &mut block.actions) {
            if let Action::Bind {
                binding, mutable, ..
            } = &mut action.action
            {
                if *binding == plan.binding {
                    *mutable = false;
                }
            }
        }
        assert!(Borrow::new(&graph, &place, &declarations, true, true, true).is_err());
        assert!(Borrow::new(&graph, &place, &declarations, false, true, true).is_ok());
    }

    #[test]
    fn checked_field_identity_tuple_bounds_and_leaf_type_are_preserved() {
        let (graph, place, declarations) = fixture(false, false);
        let mut bad = place.clone();
        if let AddressProjection::Field(field) = &mut bad.projections[0] {
            field.index = usize::MAX;
        }
        assert!(Borrow::new(&graph, &bad, &declarations, false, true, true).is_err());
        let mut bad = place.clone();
        bad.projections[1] = AddressProjection::Tuple(usize::MAX);
        assert!(Borrow::new(&graph, &bad, &declarations, false, true, true).is_err());
        let mut bad = place;
        bad.ty = Type::Bool;
        assert!(Borrow::new(&graph, &bad, &declarations, false, true, true).is_err());
    }

    #[test]
    fn unstabilized_owners_and_unchecked_selected_addresses_are_not_emitted() {
        let (graph, place, declarations) = fixture(false, false);
        assert!(Borrow::new(&graph, &place, &declarations, false, true, false).is_err());
        let ordinary = Borrow::new(&graph, &place, &declarations, false, false, true).unwrap();
        assert!(matches!(
            ordinary.output,
            Type::Reference { mutable: false, .. }
        ));
        let generated = ordinary.declaration("project", "input");
        assert!(generated.contains("#ref-ptr") && generated.contains("#ptr-borrow"));
        let mut bad = place.clone();
        bad.projections.push(AddressProjection::Index(ValueId(0)));
        assert!(Borrow::new(&graph, &bad, &declarations, false, true, true).is_err());
        bad.checked_prefix = bad.projections.len();
        assert!(Borrow::new(&graph, &bad, &declarations, false, true, true).is_err());
        let mut bad = place;
        bad.root = AddressRoot::Value(ValueId(0));
        assert!(Borrow::new(&graph, &bad, &declarations, false, true, true).is_err());
        bad.root = AddressRoot::Local(BindingId(usize::MAX));
        assert!(Borrow::new(&graph, &bad, &declarations, false, true, true).is_err());
    }
}

impl Borrow {
    pub fn new(
        graph: &Graph,
        place: &PlaceDescriptor,
        declarations: &Declarations,
        mutable: bool,
        pinned: bool,
        stationary: bool,
    ) -> Result<Self, String> {
        if !stationary {
            return Err(
                "local borrows require stable frame-owner storage, not a handle projection".into(),
            );
        }
        let AddressRoot::Local(binding) = place.root else {
            return Err("stable owner borrow requires a checked local binding".into());
        };
        let owner = graph
            .bindings
            .get(binding.0)
            .ok_or("stable owner borrow lost its binding")?;
        validate_mutability(graph, binding, mutable)?;
        if !place.checks().is_empty() {
            return Err("stable owner projection needs its selected address snapshot".into());
        }
        let owner = resolve_type(&owner.ty, &declarations.aliases)?;
        let (fields, target) = crate::generator::async_projection::checked_path(
            owner.clone(),
            &place.projections,
            &place.ty,
            declarations,
        )?;
        Ok(Self {
            binding,
            mutable,
            input: Type::PinnedReference {
                mutable,
                target: Box::new(owner),
            },
            output: if pinned {
                Type::PinnedReference {
                    mutable,
                    target: Box::new(target),
                }
            } else {
                Type::Reference {
                    mutable,
                    target: Box::new(target),
                }
            },
            fields,
        })
    }

    pub fn declaration(&self, name: &str, argument: &str) -> String {
        let value = if self.fields.is_empty() {
            argument.to_owned()
        } else {
            let place = self
                .fields
                .iter()
                .fold(argument.to_owned(), |place, field| {
                    format!("(#get {place} {field})")
                });
            format!(
                "(#pin-borrow{} {place})",
                if self.mutable { "-mut" } else { "" }
            )
        };
        let value = if matches!(self.output, Type::Reference { .. }) {
            let ty = match &self.output {
                Type::Reference { target, .. } => target,
                _ => unreachable!(),
            };
            // Keep the exact identity visible to ordinary loan analysis.
            // A stored raw pointer is otherwise only a lifetime-anchored view
            // and cannot carry the payload's nested reference provenance.
            format!("(#block (#let projected {} {value})\n(#unsafe (#ptr-borrow{} projected (#ref-ptr projected))))",
                crate::type_source(&Type::PinnedReference { mutable: self.mutable, target: ty.clone() }),
                if self.mutable { "-mut" } else { "" })
        } else {
            value
        };
        format!(
            "(#fn {name} (({argument} {})) {} {} (#return {value}))",
            crate::type_source(&self.input),
            crate::type_source(&self.output),
            if matches!(self.output, Type::Reference { .. }) { super::effects::RAW_BOUNDARY } else { "" },
        )
    }

    /// Operation-local borrows of a movable frame use its ordinary storage
    /// capability directly. No raw-pointer reconstruction or pin weakening is
    /// needed while the frame remains on the synchronous poll call's stack.
    pub fn declaration_from_unpinned_slot(
        &self,
        name: &str,
        argument: &str,
        slot: &str,
        full: &str,
    ) -> String {
        let Type::PinnedReference { target, .. } = &self.input else {
            unreachable!()
        };
        let borrow = if self.mutable {
            "#borrow-mut"
        } else {
            "#borrow"
        };
        let base = "projected";
        let place = self.fields.iter().fold(base.to_owned(), |place, field| {
            format!("(#get {place} {field})")
        });
        let value = if self.fields.is_empty() {
            base.to_owned()
        } else {
            format!("({borrow} {place})")
        };
        format!(
            "(#fn {name} (({argument} (#ref{} {slot}))) {}\n\
          (#let {base} (#ref{} {}) ({borrow} (#get-payload {argument} {full} 0)))\n\
          (#return {value}))",
            if self.mutable { "-mut" } else { "" },
            crate::type_source(&self.output),
            if self.mutable { "-mut" } else { "" },
            crate::type_source(target)
        )
    }
}

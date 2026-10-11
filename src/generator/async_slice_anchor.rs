//! Checked reconstruction of selected elements from lifetime-bearing slices.
//! Addresses remember selection; they never grant permissions or extend loans.

use crate::generator::async_exec::Graph;
use crate::typed_body::PlaceRoot;
use crate::typed_ir::Declarations;
use crate::typed_place::{Place, Segment};
use crate::Type;
use std::collections::HashMap;

struct Recipe {
    project: [Option<String>; 2],
    index: String,
    probe: String,
    coordinate: Option<u128>,
    owner: String,
    sample: String,
    address: String,
}

#[derive(Default)]
pub(crate) struct Recipes {
    entries: HashMap<Place, Recipe>,
    pub declarations: Vec<String>,
}

pub(crate) fn parameter(
    place: &Place,
    graph: &Graph,
    declarations: &Declarations,
) -> Option<crate::typed_body::BindingId> {
    let PlaceRoot::Parameter(binding) = place.root else {
        return None;
    };
    matches!(
        crate::typed_ir::resolve_type(&graph.bindings[binding.0].ty, &declarations.aliases),
        Ok(Type::Slice(_) | Type::MutableSlice(_))
    )
    .then_some(binding)
}

impl Recipes {
    pub fn new(
        places: impl IntoIterator<Item = Place>,
        graph: &Graph,
        declarations: &Declarations,
        fresh: impl Fn(&str) -> String,
    ) -> Result<Self, String> {
        let mut recipes = Self::default();
        for place in places {
            let Some(binding) = parameter(&place, graph, declarations) else {
                continue;
            };
            if recipes.entries.contains_key(&place) {
                continue;
            }
            let source = crate::typed_ir::resolve_type(
                &graph.bindings[binding.0].ty,
                &declarations.aliases,
            )?;
            let (exclusive, element) = match &source {
                Type::MutableSlice(element) => (true, element.as_ref().clone()),
                Type::Slice(element) => (false, element.as_ref().clone()),
                _ => unreachable!(),
            };
            let coordinate = match place.segments.first() {
                Some(Segment::Index(index)) => Some(*index),
                Some(Segment::DynamicIndex) => None,
                _ => return Err("selected slice anchors require a checked element index".into()),
            };
            let input = crate::type_source(&Type::PinnedReference {
                mutable: exclusive,
                target: Box::new(source),
            });
            let owner = fresh("slice-anchor-owner");
            let sample = fresh("slice-anchor-sample");
            let mut project: [Option<String>; 2] = [None, None];
            for mutable in [false, true] {
                if mutable && !exclusive {
                    continue;
                }
                let name = fresh("slice-anchor-project");
                let first = fresh("slice-anchor-element");
                let mut target = crate::typed_ir::resolve_type(&element, &declarations.aliases)?;
                let reference = |ty| {
                    crate::type_source(&Type::Reference {
                        mutable,
                        target: Box::new(ty),
                    })
                };
                let first_type = crate::type_source(&Type::Reference {
                    mutable: exclusive,
                    target: Box::new(target.clone()),
                });
                let mut steps = vec![format!(
                    "(#let {first} {first_type} (#slice{}-idx (#deref {owner}) {sample}))",
                    if exclusive { "-mut" } else { "" }
                )];
                let mut value = first;
                for segment in place.segments.iter().skip(1) {
                    let projected = match segment {
                        Segment::Field(field) => {
                            let field = declarations.field(*field);
                            target = field.ty.clone();
                            format!("(#get {value} {})", field.name)
                        }
                        Segment::Tuple(index) => {
                            let Type::Tuple(fields) = target else { return Err("slice anchor tuple lost its checked layout".into()) };
                            target = fields.get(*index).ok_or("slice anchor tuple index is invalid")?.clone();
                            format!("(#get {value} {index})")
                        }
                        Segment::Index(index) => {
                            let Type::Array(element, _) = target else { return Err("slice anchor array lost its checked layout".into()) };
                            target = *element;
                            format!("(#index {value} {index}usize)")
                        }
                        _ => return Err("nested runtime slice anchor coordinates require checked reconstruction".into()),
                    };
                    target = crate::typed_ir::resolve_type(&target, &declarations.aliases)?;
                    let next = fresh("slice-anchor-step");
                    steps.push(format!(
                        "(#let {next} {} (#borrow{} {projected}))",
                        reference(target.clone()),
                        if mutable { "-mut" } else { "" }
                    ));
                    value = next;
                }
                let output = if place.segments.len() == 1 && exclusive && !mutable {
                    format!("(#borrow (#deref {value}))")
                } else {
                    value
                };
                recipes.declarations.push(format!(
                    "(#fn {name} (: {owner} {input} : {sample} #usize) {} {} (#return {output}))",
                    reference(target),
                    steps.join("\n")
                ));
                project[usize::from(mutable)] = Some(name);
            }
            let prototype = fresh("slice-anchor-address");
            let length = fresh("slice-anchor-length");
            let address = fresh("slice-anchor-pointer");
            let base = fresh("slice-anchor-base");
            let next = fresh("slice-anchor-next");
            let descending = fresh("slice-anchor-descending");
            let stride = fresh("slice-anchor-stride");
            let delta = fresh("slice-anchor-delta");
            let index = fresh("slice-anchor-index");
            let probe = fresh("slice-anchor-probe");
            let len = format!(
                "(#slice{}-len (#deref {owner}))",
                if exclusive { "-mut" } else { "" }
            );
            let shared = project[0].as_ref().unwrap();
            recipes.declarations.push(format!("(#fn {prototype} (: {owner} {input} : {sample} #usize) #usize (#return (#ptr-address (#ref-ptr (#call {shared} (: {owner} {owner} : {sample} {sample}))))))"));
            // Explicit argument names are generated symbols, not positional metadata.
            let at = |coordinate: &str| {
                format!("(#call {prototype} (: {owner} {owner} : {sample} {coordinate}))")
            };
            let measurements = format!("(#let {base} #usize {})
              (#let {next} #usize {})
              (#let {descending} #bool (#usize.< {next} {base}))
              (#let {stride} #usize (#if {descending} (#usize.-.wrap {base} {next}) (#usize.-.wrap {next} {base})))
              (#let {delta} #usize (#if {descending} (#usize.-.wrap {base} {address}) (#usize.-.wrap {address} {base})))", at("0usize"), at("1usize"));
            let direction = format!(
                "(#if {descending} (#usize.<= {address} {base}) (#usize.>= {address} {base}))"
            );
            let valid = format!("(#if (#usize.== {stride} 0usize) (#usize.== {address} {base}) (#bool.&& {direction} (#bool.&& (#usize.== (#usize.%.wrap {delta} {stride}) 0usize) (#usize.< (#usize./.wrap {delta} {stride}) {length}))))");
            recipes.declarations.push(format!("(#fn {index} (: {owner} {input} : {address} #usize) #usize
              (#let {length} #usize {len}) (#assert (#usize.> {length} 0usize))
              (#if (#usize.== {length} 1usize) (#block (#assert (#usize.== {address} {})) (#return 0usize)) ())
              {measurements} (#assert {valid})
              (#return (#if (#usize.== {stride} 0usize) 0usize (#usize./.wrap {delta} {stride}))))", at("0usize")));
            let probe_body = if let Some(coordinate) = coordinate {
                format!(
                    "(#bool.&& (#usize.< {coordinate}usize {length}) (#usize.== {address} {}))",
                    at(&format!("{coordinate}usize"))
                )
            } else {
                format!("(#if (#usize.== {length} 0usize) false (#if (#usize.== {length} 1usize) (#usize.== {address} {}) (#block {measurements} {valid})))", at("0usize"))
            };
            recipes.declarations.push(format!("(#fn {probe} (: {owner} {input} : {address} #usize) #bool (#let {length} #usize {len}) (#return {probe_body}))"));
            recipes.entries.insert(
                place,
                Recipe {
                    project,
                    index,
                    probe,
                    coordinate,
                    owner,
                    sample,
                    address,
                },
            );
        }
        Ok(recipes)
    }

    pub fn materialize(&self, place: &Place, owner: &str, pointer: &str, mutable: bool) -> String {
        let recipe = &self.entries[place];
        let index = recipe
            .coordinate
            .map(|index| format!("{index}usize"))
            .unwrap_or_else(|| {
                format!(
                    "(#call {} (: {} {owner} : {} (#ptr-address {pointer})))",
                    recipe.index, recipe.owner, recipe.address
                )
            });
        format!(
            "(#call {} (: {} {owner} : {} {index}))",
            recipe.project[usize::from(mutable)].as_ref().unwrap(),
            recipe.owner,
            recipe.sample
        )
    }

    pub fn probe(&self, place: &Place, owner: &str, pointer: &str) -> String {
        let recipe = &self.entries[place];
        format!(
            "(#call {} (: {} {owner} : {} (#ptr-address {pointer})))",
            recipe.probe, recipe.owner, recipe.address
        )
    }
}

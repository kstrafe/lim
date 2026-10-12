//! Checked reconstruction of selected elements from lifetime-bearing slices.
//! Addresses remember selection; they never grant permissions or extend loans.

use crate::generator::async_exec::Graph;
use crate::typed_body::PlaceRoot;
use crate::typed_ir::Declarations;
use crate::typed_place::{Place, Segment};
use crate::Type;
use std::collections::HashMap;

#[derive(Clone)]
struct Recipe {
    project: [Option<String>; 2],
    index: String,
    probe: String,
    coordinate: Option<u128>,
    owner: String,
    sample: String,
    address: String,
    nested: Option<[Option<String>; 2]>,
}

// Reuse ordinary array geometry after selecting a slice element. The adapted
// graph is a layout descriptor only; it is never used for source loan checking.
#[derive(Clone)]
struct Nested {
    place: Place,
    arrays: super::async_array_anchor::Recipes,
}

impl Nested {
    fn project(
        &self,
        prefix: usize,
        mutable: bool,
        base: &str,
        indices: &HashMap<usize, String>,
    ) -> String {
        if prefix == 0 {
            return base.into();
        }
        if let Some(value) = self
            .arrays
            .project(&self.place, prefix, mutable, base, indices)
        {
            return value;
        }
        let mut value = base.to_owned();
        for (position, segment) in self.place.segments[..prefix].iter().enumerate() {
            value = match segment {
                Segment::Index(index) => format!("(#index {value} {index}usize)"),
                Segment::DynamicIndex => format!("(#index {value} {})", indices[&position]),
                _ => unreachable!("dynamic slice suffix projections have array recipes"),
            };
        }
        format!("(#borrow{} {value})", if mutable { "-mut" } else { "" })
    }

    fn materialize(
        &self,
        base: &str,
        address: &str,
        mutable: bool,
        fresh: &impl Fn(&str) -> String,
    ) -> String {
        let mut indices = HashMap::new();
        let mut steps = Vec::new();
        for (position, segment) in self.place.segments.iter().enumerate() {
            if *segment != Segment::DynamicIndex {
                continue;
            }
            let array = self.project(position, false, base, &indices);
            let index = fresh("slice-nested-index");
            steps.push(format!(
                "(#let {index} #usize {})",
                self.arrays
                    .get(&self.place, position)
                    .index_address(&array, address)
            ));
            indices.insert(position, index);
        }
        format!(
            "(#block {} {})",
            steps.join("\n"),
            self.project(self.place.segments.len(), mutable, base, &indices)
        )
    }

    fn probe(
        &self,
        base: &str,
        address: &str,
        start: usize,
        indices: &mut HashMap<usize, String>,
        fresh: &impl Fn(&str) -> String,
    ) -> String {
        if let Some(position) = (start..self.place.segments.len())
            .find(|position| self.place.segments[*position] == Segment::DynamicIndex)
        {
            let array = self.project(position, false, base, indices);
            let recipe = self.arrays.get(&self.place, position);
            let index = fresh("slice-nested-probe-index");
            indices.insert(position, index.clone());
            let rest = self.probe(base, address, position + 1, indices, fresh);
            format!(
                "(#bool.&& {} (#block (#let {index} #usize {}) {rest}))",
                recipe.probe_address(&array, address),
                recipe.index_address(&array, address)
            )
        } else {
            format!(
                "(#usize.== {address} (#ptr-address (#ref-ptr {})))",
                self.project(self.place.segments.len(), false, base, indices)
            )
        }
    }
}

#[derive(Clone, Default)]
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
        let mut layout_graph = None;
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
            let has_nested = place
                .segments
                .iter()
                .skip(1)
                .any(|segment| *segment == Segment::DynamicIndex);
            let mut nested = if has_nested {
                let adapted = layout_graph.get_or_insert_with(|| graph.clone());
                adapted.bindings[binding.0].ty = Type::Reference {
                    mutable: exclusive,
                    target: Box::new(element.clone()),
                };
                let suffix = Place {
                    root: place.root.clone(),
                    segments: place.segments[1..].to_vec(),
                };
                Some(Nested {
                    arrays: super::async_array_anchor::Recipes::new(
                        [suffix.clone()],
                        adapted,
                        declarations,
                        &fresh,
                    ),
                    place: suffix,
                })
            } else {
                None
            };
            if let Some(nested) = &mut nested {
                recipes.declarations.append(&mut nested.arrays.declarations);
            }
            let mut project: [Option<String>; 2] = [None, None];
            let mut leaf = Type::Unit;
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
                        Segment::DynamicIndex => {
                            let Type::Array(element, _) = target else { return Err("slice anchor dynamic suffix lost its checked array layout".into()) };
                            target = *element;
                            format!("(#index {value} 0usize)")
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
                leaf = target.clone();
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
            let alignment = if has_nested {
                "true".into()
            } else {
                format!("(#usize.== (#usize.%.wrap {delta} {stride}) 0usize)")
            };
            let valid = format!("(#if (#usize.== {stride} 0usize) (#usize.== {address} {base}) (#bool.&& {direction} (#bool.&& {alignment} (#usize.< (#usize./.wrap {delta} {stride}) {length}))))");
            let single_valid = if has_nested {
                "true".into()
            } else {
                format!("(#usize.== {address} {})", at("0usize"))
            };
            recipes.declarations.push(format!("(#fn {index} (: {owner} {input} : {address} #usize) #usize
              (#let {length} #usize {len}) (#assert (#usize.> {length} 0usize))
              (#if (#usize.== {length} 1usize) (#block (#assert {single_valid}) (#return 0usize)) ())
              {measurements} (#assert {valid})
              (#return (#if (#usize.== {stride} 0usize) 0usize (#usize./.wrap {delta} {stride}))))"));
            let mut probe_body = if let Some(coordinate) = coordinate {
                let match_address = if has_nested {
                    "true".into()
                } else {
                    format!(
                        "(#usize.== {address} {})",
                        at(&format!("{coordinate}usize"))
                    )
                };
                format!("(#bool.&& (#usize.< {coordinate}usize {length}) {match_address})")
            } else {
                format!("(#if (#usize.== {length} 0usize) false (#if (#usize.== {length} 1usize) {single_valid} (#block {measurements} {valid})))")
            };
            let mut nested_project = None;
            if let Some(nested) = nested {
                let selected = coordinate
                    .map(|coordinate| format!("{coordinate}usize"))
                    .unwrap_or_else(|| {
                        format!("(#call {index} (: {owner} {owner} : {address} {address}))")
                    });
                let base = fresh("slice-nested-base");
                let base_type = crate::type_source(&Type::Reference {
                    mutable: exclusive,
                    target: Box::new(element.clone()),
                });
                let base_binding = format!(
                    "(#let {base} {base_type} (#slice{}-idx (#deref {owner}) {selected}))",
                    if exclusive { "-mut" } else { "" }
                );
                let nested_probe = nested.probe(&base, &address, 0, &mut HashMap::new(), &fresh);
                probe_body =
                    format!("(#bool.&& {probe_body} (#block {base_binding} {nested_probe}))");
                let mut functions = [None, None];
                for mutable in [false, true] {
                    if mutable && !exclusive {
                        continue;
                    }
                    let name = fresh("slice-nested-project");
                    let body = nested.materialize(&base, &address, mutable, &fresh);
                    let output = crate::type_source(&Type::Reference {
                        mutable,
                        target: Box::new(leaf.clone()),
                    });
                    recipes.declarations.push(format!("(#fn {name} (: {owner} {input} : {address} #usize) {output} {base_binding} (#return {body}))"));
                    functions[usize::from(mutable)] = Some(name);
                }
                nested_project = Some(functions);
            }
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
                    nested: nested_project,
                },
            );
        }
        Ok(recipes)
    }

    pub fn materialize(&self, place: &Place, owner: &str, pointer: &str, mutable: bool) -> String {
        let recipe = &self.entries[place];
        if let Some(nested) = &recipe.nested {
            return format!(
                "(#call {} (: {} {owner} : {} (#ptr-address {pointer})))",
                nested[usize::from(mutable)].as_ref().unwrap(),
                recipe.owner,
                recipe.address
            );
        }
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

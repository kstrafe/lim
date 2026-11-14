//! Layout-aware recipes for runtime-selected elements in stationary arrays.
//! These pure helpers calculate offsets; they do not grant borrow permissions.
//! Original source and emitted ordinary code remain the ownership authority.

use std::collections::HashMap;

use crate::generator::async_exec::Graph;
use crate::typed_body::PlaceRoot;
use crate::typed_ir::Declarations;
use crate::typed_place::{Place, Segment};
use crate::Type;

#[derive(Clone)]
pub(crate) struct Recipe {
    index: String,
    probe: String,
    owner: String,
    address: String,
}

impl Recipe {
    pub fn index(&self, owner: &str, pointer: &str) -> String {
        self.call(&self.index, owner, pointer)
    }

    pub fn probe(&self, owner: &str, pointer: &str) -> String {
        self.call(&self.probe, owner, pointer)
    }

    fn call(&self, name: &str, owner: &str, pointer: &str) -> String {
        self.call_address(name, owner, &format!("(#ptr-address {pointer})"))
    }

    pub fn index_address(&self, owner: &str, address: &str) -> String {
        self.call_address(&self.index, owner, address)
    }

    pub fn probe_address(&self, owner: &str, address: &str) -> String {
        self.call_address(&self.probe, owner, address)
    }

    fn call_address(&self, name: &str, owner: &str, address: &str) -> String {
        format!(
            "(#call {name} (({} {owner}) ({} {address})))",
            self.owner, self.address
        )
    }
}

#[derive(Clone, Default)]
pub(crate) struct Recipes {
    entries: HashMap<(Place, usize), Recipe>,
    projections: HashMap<(Place, usize, bool), Projection>,
    pub declarations: Vec<String>,
}

#[derive(Clone)]
struct Projection {
    name: String,
    owner: String,
    coordinates: Vec<(usize, String)>,
}

pub(crate) fn target_type(
    place: &Place,
    prefix: usize,
    graph: &Graph,
    declarations: &Declarations,
) -> Type {
    let resolve = |ty: &Type| {
        crate::typed_ir::resolve_type(ty, &declarations.aliases)
            .expect("array anchor types were resolved before emission")
    };
    let (source_type, external) = match place.root {
        PlaceRoot::Local(binding) => (&graph.bindings[binding.0].ty, false),
        PlaceRoot::Parameter(binding) => (&graph.bindings[binding.0].ty, true),
        PlaceRoot::Global(global) => (declarations.global_type(global), false),
        _ => unreachable!("array anchors retain checked local/parameter roots"),
    };
    let mut ty = resolve(source_type);
    if external {
        let (Type::Reference { target, .. } | Type::PinnedReference { target, .. }) = ty else {
            unreachable!("external anchors are thin reference parameters");
        };
        ty = resolve(&target);
    }
    for segment in &place.segments[..prefix] {
        ty = match (segment, ty) {
            (Segment::Field(id), _) => resolve(&declarations.field(*id).ty),
            (Segment::Payload(variant, index), _) => {
                resolve(&declarations.variant(*variant).fields[*index])
            }
            (Segment::Tuple(index), Type::Tuple(fields)) => resolve(&fields[*index]),
            (Segment::Index(_) | Segment::DynamicIndex, Type::Array(element, _)) => {
                resolve(&element)
            }
            _ => unreachable!("array anchor projections were checked before emission"),
        };
    }
    ty
}

impl Recipes {
    pub fn new(
        places: impl IntoIterator<Item = Place>,
        graph: &Graph,
        declarations: &Declarations,
        fresh: impl Fn(&str) -> String,
    ) -> Self {
        let mut recipes = Self::default();
        for place in places {
            if (place.segments.len() > 1 && place.segments.contains(&Segment::DynamicIndex))
                || (matches!(place.root, PlaceRoot::Parameter(_)) && !place.segments.is_empty())
            {
                for prefix in 1..=place.segments.len() {
                    for mutable in [false, true] {
                        if recipes
                            .projections
                            .contains_key(&(place.clone(), prefix, mutable))
                        {
                            continue;
                        }
                        let pinned = matches!(
                            place.root,
                            PlaceRoot::Local(_) | PlaceRoot::Global(_)
                        ) || matches!(place.root, PlaceRoot::Parameter(binding)
                                if matches!(crate::typed_ir::resolve_type(&graph.bindings[binding.0].ty, &declarations.aliases),
                                    Ok(Type::PinnedReference { .. })));
                        let reference = |target| {
                            if pinned {
                                Type::PinnedReference {
                                    mutable,
                                    target: Box::new(target),
                                }
                            } else {
                                Type::Reference {
                                    mutable,
                                    target: Box::new(target),
                                }
                            }
                        };
                        let input = reference(target_type(&place, 0, graph, declarations));
                        if let PlaceRoot::Parameter(binding) = place.root {
                            let source = crate::typed_ir::resolve_type(
                                &graph.bindings[binding.0].ty,
                                &declarations.aliases,
                            )
                            .expect("external anchor reference was resolved");
                            // An immutable parameter cannot grant an exclusive projection.
                            if mutable
                                && matches!(
                                    source,
                                    Type::Reference { mutable: false, .. }
                                        | Type::PinnedReference { mutable: false, .. }
                                )
                            {
                                continue;
                            }
                        }
                        let owner = fresh("array-project-owner");
                        let name = fresh("array-project");
                        let mut signature = vec![format!("{owner} {}", crate::type_source(&input))];
                        let mut coordinates = Vec::new();
                        let mut steps = Vec::new();
                        let mut projected = owner.clone();
                        let suffix = if mutable { "-mut" } else { "" };
                        let borrow = if pinned { "#pin-borrow" } else { "#borrow" };
                        for (position, segment) in place.segments[..prefix].iter().enumerate() {
                            let expression = match segment {
                                Segment::Field(id) => {
                                    format!("(#get {projected} {})", declarations.field(*id).name)
                                }
                                Segment::Tuple(index) => format!("(#get {projected} {index})"),
                                Segment::Payload(variant, _) => format!(
                                    "(#deref (#unsafe (#pin-get-payload-unchecked{suffix} {projected} {})))",
                                    declarations.variant(*variant).name
                                ),
                                Segment::Index(index) => {
                                    format!("(#index {projected} {index}usize)")
                                }
                                Segment::DynamicIndex => {
                                    let index = fresh("array-project-index");
                                    signature.push(format!("{index} #usize"));
                                    coordinates.push((position, index.clone()));
                                    format!("(#index {projected} {index})")
                                }
                                _ => unreachable!("array projection has checked segments"),
                            };
                            let next = fresh("array-project-step");
                            steps.push(format!(
                                "(#let {next} {} ({borrow}{suffix} {expression}))",
                                crate::type_source(&reference(target_type(
                                    &place,
                                    position + 1,
                                    graph,
                                    declarations
                                )))
                            ));
                            projected = next;
                        }
                        recipes.declarations.push(format!(
                            "(#fn {name} ({}) {} {} (#return {projected}))",
                            signature
                                .iter()
                                .map(|parameter| format!("({parameter})"))
                                .collect::<Vec<_>>()
                                .join(" "),
                            crate::type_source(&reference(target_type(
                                &place,
                                prefix,
                                graph,
                                declarations
                            ))),
                            steps.join("\n")
                        ));
                        recipes.projections.insert(
                            (place.clone(), prefix, mutable),
                            Projection {
                                name,
                                owner,
                                coordinates,
                            },
                        );
                    }
                }
            }
            for (position, segment) in place.segments.iter().enumerate() {
                if *segment != Segment::DynamicIndex
                    || recipes.entries.contains_key(&(place.clone(), position))
                {
                    continue;
                }
                let array = target_type(&place, position, graph, declarations);
                let Type::Array(_, length) = &array else {
                    unreachable!("dynamic array projection requires an array");
                };
                let pinned = matches!(place.root, PlaceRoot::Local(_) | PlaceRoot::Global(_))
                    || matches!(place.root, PlaceRoot::Parameter(binding)
                        if matches!(crate::typed_ir::resolve_type(&graph.bindings[binding.0].ty, &declarations.aliases),
                            Ok(Type::PinnedReference { .. })));
                let input = if pinned {
                    Type::PinnedReference {
                        mutable: false,
                        target: Box::new(array.clone()),
                    }
                } else {
                    Type::Reference {
                        mutable: false,
                        target: Box::new(array.clone()),
                    }
                };
                let owner = fresh("array-anchor-owner");
                let address = fresh("array-anchor-address");
                let prototype = fresh("array-anchor-prototype");
                let base = fresh("array-anchor-base");
                let index = fresh("array-anchor-index");
                let probe = fresh("array-anchor-probe");
                let sample = fresh("array-anchor-sample");
                let mut projected = owner.clone();
                let mut prototype_steps = Vec::new();
                let mut projected_reference = true;
                for (offset, segment) in place.segments[position..].iter().enumerate() {
                    if let Segment::Payload(variant, _) = segment {
                        // A prototype measures geometry, not the contents of
                        // its sample element. Another element may have an
                        // inactive variant here. Form only its padded payload
                        // address; never load the value. Actual selections and
                        // candidate probes check the active variant separately.
                        let input = if projected_reference {
                            projected.clone()
                        } else {
                            format!("(#pin-borrow {projected})")
                        };
                        let next = fresh("array-anchor-payload");
                        let target =
                            target_type(&place, position + offset + 1, graph, declarations);
                        prototype_steps.push(format!("(#let {next} (#pin-ref {}) (#unsafe (#pin-get-payload-unchecked {input} {})))",
                            crate::type_source(&target), declarations.variant(*variant).name));
                        projected = next;
                        projected_reference = true;
                        continue;
                    }
                    projected = match segment {
                        Segment::Field(id) => {
                            format!("(#get {projected} {})", declarations.field(*id).name)
                        }
                        Segment::Tuple(index) => format!("(#get {projected} {index})"),
                        Segment::Index(index) => format!("(#index {projected} {index}usize)"),
                        Segment::DynamicIndex if offset == 0 => {
                            format!("(#index {projected} {sample})")
                        }
                        Segment::DynamicIndex => format!("(#index {projected} 0usize)"),
                        _ => unreachable!("array prototype has checked projections"),
                    };
                    projected_reference = false;
                }
                // Start at the canonical *leaf*, not the array's start. This
                // subtracts actual field/padding offsets, including zero-sized
                // tail fields whose address is at the end of an element.
                let borrow = if pinned { "#pin-borrow" } else { "#borrow" };
                let prototype_reference = if projected_reference {
                    projected
                } else {
                    format!("({borrow} {projected})")
                };
                let input = crate::type_source(&input);
                let (prefix, index_value, probe_value) = if *length <= 1 {
                    (
                        String::new(),
                        "0usize".to_owned(),
                        if *length == 0 { "false" } else { "true" }.to_owned(),
                    )
                } else {
                    let next = fresh("array-anchor-next");
                    let descending = fresh("array-anchor-descending");
                    let stride = fresh("array-anchor-stride");
                    let delta = fresh("array-anchor-delta");
                    let prefix = format!(
                        "(#let {base} #usize (#call {prototype} (({owner} {owner}) ({sample} 0usize))))
                         (#let {next} #usize (#call {prototype} (({owner} {owner}) ({sample} 1usize))))
                         (#let {descending} #bool (#usize::lt {next} {base}))
                         (#let {stride} #usize (#if {descending} (#usize::sub-wrap {base} {next}) (#usize::sub-wrap {next} {base})))
                         (#let {delta} #usize (#if {descending} (#usize::sub-wrap {base} {address}) (#usize::sub-wrap {address} {base})))");
                    let index_value = format!(
                        "(#if (#usize::eq {stride} 0usize) 0usize (#usize::div-wrap {delta} {stride}))"
                    );
                    let probe_value = format!("(#if (#usize::eq {stride} 0usize) (#usize::eq {address} {base})
                        (#bool::and (#if {descending} (#usize::le {address} {base}) (#usize::ge {address} {base}))
                          (#usize::lt {delta} (#usize::mul-wrap {stride} {length}usize))))");
                    (prefix, index_value, probe_value)
                };
                recipes.declarations.push(format!(
                    "(#fn {prototype} (({owner} {input}) ({sample} #usize)) #usize
                      {}\n(#return (#ptr-address (#ref-ptr {prototype_reference}))))
                    (#fn {index} (({owner} {input}) ({address} #usize)) #usize
                      {prefix}
                      (#return {index_value}))
                    (#fn {probe} (({owner} {input}) ({address} #usize)) #bool
                      {prefix}
                      (#return {probe_value}))",
                    prototype_steps.join("\n")
                ));
                recipes.entries.insert(
                    (place.clone(), position),
                    Recipe {
                        index,
                        probe,
                        owner,
                        address,
                    },
                );
            }
        }
        recipes
    }

    pub fn get(&self, place: &Place, position: usize) -> &Recipe {
        &self.entries[&(place.clone(), position)]
    }

    pub fn project(
        &self,
        place: &Place,
        prefix: usize,
        mutable: bool,
        owner: &str,
        indices: &HashMap<usize, String>,
    ) -> Option<String> {
        let projection = self.projections.get(&(place.clone(), prefix, mutable))?;
        let mut arguments = vec![format!("{} {owner}", projection.owner)];
        arguments.extend(
            projection
                .coordinates
                .iter()
                .map(|(position, name)| format!("{name} {}", indices[position])),
        );
        Some(format!(
            "(#call {} ({}))",
            projection.name,
            arguments
                .iter()
                .map(|argument| format!("({argument})"))
                .collect::<Vec<_>>()
                .join(" ")
        ))
    }
}

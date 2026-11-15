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

pub(crate) fn binding_numeric_shapes(
    body: &Body,
    declarations: &Declarations,
) -> Vec<Option<std::sync::Arc<Shape>>> {
    let mut shared = HashMap::new();
    body.bindings
        .iter()
        .map(|binding| {
            shared
                .entry(binding.ty.clone())
                .or_insert_with(|| {
                    let mut cells = Vec::new();
                    collect_numeric_arrays(
                        &binding.ty,
                        declarations,
                        &mut Vec::new(),
                        &mut std::collections::HashSet::new(),
                        &mut cells,
                    );
                    (!cells.is_empty())
                        .then(|| Shape::build(&binding.ty, declarations).ok())
                        .flatten()
                        .map(std::sync::Arc::new)
                })
                .clone()
        })
        .collect()
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
    /// Loans retained in an owning pointer's allocation, not additional words
    /// in the numeric backing buffer.
    pub retained: Vec<ParameterLoanSeed>,
}

#[derive(Clone, Debug)]
pub(crate) struct Layout {
    pub words: usize,
    pub slots: Vec<Slot>,
    pub shape: Option<std::sync::Arc<Shape>>,
}

/// Flat value-word geometry, not an initialization or reference-provenance
/// witness. Arrays share one element shape rather than expanding their indices.
#[derive(Clone, Debug)]
pub(crate) struct Shape {
    words: usize,
    numeric_word: bool,
    fields: Vec<(Segment, Shape)>,
    array: Option<(Box<Shape>, usize)>,
    variants: Vec<crate::typed_ir::VariantId>,
}

impl Shape {
    fn build(ty: &Type, declarations: &Declarations) -> Result<Self, String> {
        let ty = crate::typed_ir::resolve_type(ty, &declarations.aliases)?;
        let mut shape = Self {
            numeric_word: ty == Type::U64,
            words: crate::codegen::storage_word_count(
                &ty,
                &declarations.structs,
                &declarations.enums,
            )?,
            fields: Vec::new(),
            array: None,
            variants: Vec::new(),
        };
        match &ty {
            Type::Named(name) if declarations.structs.contains_key(name) => {
                for field in &declarations.structs[name] {
                    shape.fields.push((
                        Segment::Field(declarations.field_id(&ty, &field.name).unwrap()),
                        Self::build(&field.ty, declarations)?,
                    ));
                }
            }
            Type::Named(name) if declarations.enums.contains_key(name) => {
                for variant in &declarations.enums[name] {
                    shape
                        .variants
                        .push(declarations.variant_id(&ty, &variant.name).unwrap());
                    for (index, field) in variant.fields.iter().enumerate() {
                        shape.fields.push((
                            Segment::Payload(
                                declarations.variant_id(&ty, &variant.name).unwrap(),
                                index,
                            ),
                            Self::build(field, declarations)?,
                        ));
                    }
                }
            }
            Type::Tuple(fields) => {
                for (index, field) in fields.iter().enumerate() {
                    shape
                        .fields
                        .push((Segment::Tuple(index), Self::build(field, declarations)?));
                }
            }
            Type::Array(element, length) => {
                shape.array = Some((Box::new(Self::build(element, declarations)?), *length));
            }
            _ => {}
        }
        Ok(shape)
    }

    pub fn project(&self, path: &[Segment]) -> Option<(usize, usize)> {
        self.project_shape(path)
            .map(|(offset, shape)| (offset, shape.words))
    }

    fn project_shape(&self, path: &[Segment]) -> Option<(usize, &Shape)> {
        let Some((first, tail)) = path.split_first() else {
            return Some((0, self));
        };
        if let (Some((element, length)), Segment::Index(index)) = (&self.array, first) {
            let index = usize::try_from(*index).ok()?;
            if index >= *length {
                return None;
            }
            let (offset, shape) = element.project_shape(tail)?;
            return Some((
                index.checked_mul(element.words)?.checked_add(offset)?,
                shape,
            ));
        }
        let mut start = usize::from(matches!(first, Segment::Payload(_, _)));
        for (segment, child) in &self.fields {
            if segment == first {
                let (offset, shape) = child.project_shape(tail)?;
                return Some((start.checked_add(offset)?, shape));
            }
            if let (Segment::Payload(wanted, _), Segment::Payload(actual, _)) = (first, segment) {
                if wanted != actual {
                    continue;
                }
            }
            start = start.checked_add(child.words)?;
        }
        None
    }

    pub fn tag_offset(
        &self,
        path: &[Segment],
        variant: crate::typed_ir::VariantId,
    ) -> Option<usize> {
        let (offset, shape) = self.project_shape(path)?;
        shape.variants.contains(&variant).then_some(offset)
    }

    pub fn tag_path(
        &self,
        offset: usize,
        variant: crate::typed_ir::VariantId,
        at: &impl Fn(usize) -> Option<crate::typed_ir::VariantId>,
    ) -> Option<Vec<Segment>> {
        self.tag_path_at(offset, 0, variant, at)
    }

    fn tag_path_at(
        &self,
        offset: usize,
        base: usize,
        variant: crate::typed_ir::VariantId,
        at: &impl Fn(usize) -> Option<crate::typed_ir::VariantId>,
    ) -> Option<Vec<Segment>> {
        if offset == 0 && self.variants.contains(&variant) {
            return Some(Vec::new());
        }
        if let Some((element, length)) = &self.array {
            if element.words == 0 {
                return None;
            }
            let index = offset / element.words;
            if index >= *length {
                return None;
            }
            let start = index.checked_mul(element.words)?;
            let mut path =
                element.tag_path_at(offset - start, base.checked_add(start)?, variant, at)?;
            path.insert(0, Segment::Index(index as u128));
            return Some(path);
        }
        let active = if self.variants.is_empty() {
            None
        } else {
            let active = at(base)?;
            if !self.variants.contains(&active) {
                return None;
            }
            Some(active)
        };
        let mut start = usize::from(active.is_some());
        for (segment, child) in &self.fields {
            if matches!(segment, Segment::Payload(actual, _) if Some(*actual) != active) {
                continue;
            }
            let end = start.checked_add(child.words)?;
            if offset >= start && offset < end {
                let mut path =
                    child.tag_path_at(offset - start, base.checked_add(start)?, variant, at)?;
                path.insert(0, segment.clone());
                return Some(path);
            }
            start = end;
        }
        None
    }

    /// Only an in-bounds cell of an owned U64 array is numeric backing.
    /// Scalar words and paths crossing a reference are not storage witnesses.
    pub(crate) fn is_numeric_cell(&self, path: &[Segment]) -> bool {
        let Some((Segment::Index(index), parent)) = path.split_last() else {
            return false;
        };
        let Some((_, shape)) = self.project_shape(parent) else {
            return false;
        };
        shape
            .array
            .as_ref()
            .is_some_and(|(element, length)| element.numeric_word && *index < *length as u128)
    }
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
            let forgotten = (head == "word-forget" && children.len() == 3)
                .then(|| crate::parse_type(Some(&body.syntax(children[1], false))).ok())
                .flatten();
            let ty = match (head.as_str(), children.len()) {
                ("word-forget", 3) => forgotten.as_ref()?,
                ("word-write", 4) => body.nodes[children[3].0].ty.as_ref()?,
                ("word-read" | "word-take", 3) => node.ty.as_ref()?,
                ("word-view", 3) => match node.ty.as_ref()? {
                    Type::Reference { target, .. } | Type::PinnedReference { target, .. } => target,
                    _ => return None,
                },
                _ => return None,
            };
            let mut slots = Vec::new();
            // Deferred layouts stay unsupported rather than acquiring fabricated
            // slots from a signature whose physical representation is unknown.
            let words = if head == "word-forget" {
                // Retiring numeric storage never loads a typed reference and
                // must not introduce candidate entry loans for its layout.
                crate::codegen::storage_word_count(ty, &declarations.structs, &declarations.enums)
                    .ok()?
            } else {
                collect(ty, declarations, &mut Vec::new(), 0, &mut slots).ok()?
            };
            let shape = (head != "word-forget")
                .then(|| Shape::build(ty, declarations).map(std::sync::Arc::new))
                .transpose()
                .ok()?;
            Some((
                NodeId(index),
                Layout {
                    words,
                    slots,
                    shape,
                },
            ))
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
        | Type::PinOwned(_)
        | Type::PinShared(_) => {
            slots.push(Slot {
                path: path.clone(),
                offset,
                mutable: matches!(
                    &ty,
                    Type::Reference { mutable: true, .. }
                        | Type::PinnedReference { mutable: true, .. }
                        | Type::MutableSlice(_)
                        | Type::PinOwned(_)
                        | Type::PinShared(_)
                ),
                pinned: matches!(
                    &ty,
                    Type::PinnedReference { .. } | Type::PinOwned(_) | Type::PinShared(_)
                ),
                owned_allocation: matches!(&ty, Type::PinOwned(_) | Type::PinShared(_)),
                retained: if matches!(&ty, Type::PinOwned(_) | Type::PinShared(_)) {
                    declarations
                        .reference_storage_slots(&ty)
                        .into_iter()
                        .filter(|seed| seed.storage.first() == Some(&Segment::Dereference))
                        .collect()
                } else {
                    Vec::new()
                },
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
    fn restored_word_owner_retains_its_pointee_reference_requirements() {
        let program = crate::parse_program("#struct Holder () ((link (#ref #u64)))
#struct Words () ((words (#array #u64 1)))
#fn restore { #params = ((storage (#ref-mut Words))); #returns = (#pin-own Holder); #effects = (#io #global-access); #body = (
              (#return (#unsafe (#word-take (#pin-own Holder) (#borrow-slice-mut (#get storage words))))) ); }
#fn forward { #params = ((storage (#ref-mut Words))); #returns = (#pin-own Holder); #effects = ((#effects-of restore)); #body = (
              (#return (#call restore ((storage storage)))) ); }
#fn main { #params = (); #returns = #u64; #body = ( (#return 0u64) ); }\n").unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        for name in ["restore", "forward"] {
            let inputs = &checked.declarations().bodies[name].word_input_requirements;
            assert!(
                inputs.iter().any(|input| input.owned_allocation),
                "{name}: {inputs:?}"
            );
            assert!(
                inputs.iter().any(|input| !input.owned_allocation
                    && input
                        .input_storage
                        .iter()
                        .filter(|segment| **segment == Segment::Dereference)
                        .count()
                        == 2),
                "{name}: {inputs:?}"
            );
        }
    }

    #[test]
    fn forwarding_owned_word_requirements_retains_the_ownership_obligation() {
        let source = "#struct Words () ((words (#array #u64 1)))
#fn restore { #params = ((storage (#ref-mut Words))); #returns = (#pin-own #u64); #effects = (#io #global-access); #body = (
              (#return (#unsafe (#word-take (#pin-own #u64) (#borrow-slice-mut (#get storage words))))) ); }
#fn forward { #params = ((storage (#ref-mut Words))); #returns = (#pin-own #u64); #effects = ((#effects-of restore)); #body = (
              (#return (#call restore ((storage storage)))) ); }
#fn forward-again { #params = ((storage (#ref-mut Words))); #returns = (#pin-own #u64); #effects = ((#effects-of forward)); #body = (
              (#return (#call forward ((storage storage)))) ); }
#fn main { #params = (); #returns = #u64; #body = ( (#return 0u64) ); }\n";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let declarations = checked.declarations();
        for name in ["restore", "forward", "forward-again"] {
            let inputs = &declarations.bodies[name].word_input_requirements;
            assert_eq!(inputs.len(), 1, "{name}: {inputs:?}");
            assert!(inputs[0].owned_allocation, "{name}: {inputs:?}");
            assert!(inputs[0].mutable && inputs[0].pinned);
        }
        let invalid = source.replace("#fn main { #params = (); #returns = #u64; #body = ( (#return 0u64) ); }\n", "
#fn main { #params = (); #returns = #u64; #effects = (#io #global-access (#effects-of forward-again)); #body = (
              (#let amount #u64 42u64)
              (#let-mut storage Words (#struct-literal Words ((words (#array-repeat 0u64)))))
              (#unsafe (#word-write (#ref #u64) (#borrow-slice-mut (#get storage words)) (#borrow amount)))
              (#let owner (#pin-own #u64) (#call forward-again ((storage (#borrow-mut storage)))))
              (#forget owner) (#forget storage) (#return 0u64) ); }\n");
        let error = crate::CheckedProgram::validate(&crate::parse_program(&invalid).unwrap())
            .err()
            .unwrap();
        assert!(
            error.contains("missing required input loan")
                || error.contains("missing slot provenance"),
            "{error:?}"
        );
    }

    #[test]
    fn numeric_backing_geometry_rejects_scalar_reference_and_unknown_paths() {
        let program = crate::parse_program(
            "#struct Words () ((words (#array #u64 2)) (scalar #u64) (view (#ref (#array #u64 2))))
#fn main { #params = (); #returns = #u64; #body = ( (#return 0u64) ); }\n",
        )
        .unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let declarations = checked.declarations();
        let ty = Type::Named("Words".into());
        let shape = Shape::build(&ty, declarations).unwrap();
        let field = |name| Segment::Field(declarations.field_id(&ty, name).unwrap());
        assert!(shape.is_numeric_cell(&[field("words"), Segment::Index(1)]));
        for path in [
            vec![field("words"), Segment::Index(2)],
            vec![field("words"), Segment::DynamicIndex],
            vec![field("scalar")],
            vec![field("scalar"), Segment::Index(0)],
            vec![field("view"), Segment::Dereference, Segment::Index(0)],
            vec![field("words"), Segment::Index(0), Segment::Dereference],
        ] {
            assert!(!shape.is_numeric_cell(&path), "{path:?}");
        }
        let narrow = Shape::build(&Type::Array(Box::new(Type::U32), 2), declarations).unwrap();
        assert!(!narrow.is_numeric_cell(&[Segment::Index(0)]));
    }

    #[test]
    fn flat_shape_projects_owned_fields_and_keeps_large_arrays_compact() {
        let source = "#struct Pair () ((left #u64) (right (#tuple #u64 #u64)))
#struct Other () ((left #u64))
#enum Choice () ((Choice.First (#tuple #u64 #u64)) (Choice.Second #u64))
#fn main { #params = (); #returns = #u64; #body = ( (#return 0u64) ); }\n";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let declarations = checked.declarations();
        let pair = Type::Named("Pair".into());
        let shape = Shape::build(&pair, declarations).unwrap();
        let right = declarations.field_id(&pair, "right").unwrap();
        assert_eq!(
            shape.project(&[Segment::Field(right), Segment::Tuple(1)]),
            Some((2, 1))
        );
        let wrong = declarations
            .field_id(&Type::Named("Other".into()), "left")
            .unwrap();
        assert_eq!(shape.project(&[Segment::Field(wrong)]), None);
        assert_eq!(shape.project(&[Segment::Dereference]), None);
        let choice = Type::Named("Choice".into());
        let shape = Shape::build(&choice, declarations).unwrap();
        let first = declarations.variant_id(&choice, "Choice.First").unwrap();
        let second = declarations.variant_id(&choice, "Choice.Second").unwrap();
        assert_eq!(
            shape.project(&[Segment::Payload(first, 0), Segment::Tuple(1)]),
            Some((2, 1))
        );
        assert_eq!(shape.project(&[Segment::Payload(second, 0)]), Some((1, 1)));
        let array =
            Shape::build(&Type::Array(Box::new(pair), 1_000_000_000), declarations).unwrap();
        assert!(array.fields.is_empty());
        assert_eq!(array.array.as_ref().unwrap().0.fields.len(), 2);
        assert_eq!(
            array.project(&[
                Segment::Index(999_999_999),
                Segment::Field(right),
                Segment::Tuple(1)
            ]),
            Some((2_999_999_999, 1))
        );
        assert_eq!(array.project(&[Segment::Index(1_000_000_000)]), None);
        assert_eq!(array.project(&[Segment::DynamicIndex]), None);
    }

    #[test]
    fn large_numeric_input_uses_one_symbolic_candidate_and_one_exact_requirement() {
        let source = "#struct Holder () ((value (#ref #u64)))
#fn read { #params = ((words (#array #u64 1000000000))); #returns = #u64; #effects = (#io #global-access); #body = (
              (#let restored Holder (#unsafe (#word-read Holder (#borrow-slice words 7usize 8usize))))
              (#let answer #u64 (#deref (#get restored value)))
              (#forget restored) (#return answer) ); }\n";
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

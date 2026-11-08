//! Instantiate checked return-loan origins in caller storage. Returned reference
//! values never allocate unrelated referents. May-origins remain alternatives.
use super::*;
use crate::typed_body::ParameterLoanSummary;
use crate::typed_place::Segment as Path;
use symbolic::{Location, Segment};

type Bounds = crate::typed_flow::VariantBounds;

pub(super) struct ReferenceModel<'a> {
    pub(super) arguments: &'a [Value],
    pub(super) origins: Vec<ParameterLoanSummary>,
    pub(super) bounds: Bounds,
    pub(super) source: Option<&'a State>,
    pub(super) guards: Option<&'a guarded_returns::Guards>,
}

#[derive(Clone)]
struct Cursor {
    guard: Bit,
    value: Value,
    place: Option<Location>,
    view: Option<(usize, usize, bool)>,
    selection: Vec<usize>,
}

pub(super) struct ReferenceCandidate {
    pub state: State,
    pub reference: Value,
    pub selection: Vec<usize>,
}

impl Engine<'_, '_> {
    pub(super) fn verify_contract_return(
        &mut self,
        state: &State,
        function: &Function,
        arguments: &[Value],
        value: &Value,
    ) -> Result<()> {
        if !self.reference_type(&function.return_type, 0)? {
            return Ok(());
        }
        let declarations = self.checked.declarations();
        let id = declarations
            .function_id(&function.name)
            .ok_or_else(|| Error::checker("missing checked return identity"))?;
        let body = declarations
            .bodies
            .get(&function.name)
            .ok_or_else(|| Error::unsupported("contract has no checked return body"))?;
        let entry = self.old.clone();
        let returns = ReferenceModel {
            guards: None,
            source: entry.as_ref(),
            arguments,
            origins: body
                .call_return_origins
                .get(&id)
                .cloned()
                .unwrap_or_default(),
            bounds: body
                .call_return_variant_bounds
                .get(&id)
                .cloned()
                .unwrap_or_default(),
        };
        let covered = self.reference_coverage(state, value, &[], &returns, 0)?;
        let missing = self.circuit.and(state.guard, self.circuit.not(covered));
        if self.circuit.satisfy(missing)?.is_some() {
            return Err(Error::unsupported(
                "checked return-origin summary does not cover the symbolically executed reference",
            ));
        }
        Ok(())
    }

    pub(super) fn reference_coverage(
        &mut self,
        state: &State,
        value: &Value,
        path: &[Path],
        returns: &ReferenceModel<'_>,
        depth: usize,
    ) -> Result<Bit> {
        self.tick()?;
        if depth > 32 {
            return Err(Error::limit("return origin validation nesting exceeds 32"));
        }
        if self.circuit.satisfy(state.guard)?.is_none() {
            return Ok(TRUE);
        }
        match value {
            Value::Ref {
                place,
                target,
                mutable,
                pinned,
            } => {
                let mut covered = FALSE;
                for (candidate, reference) in
                    self.return_references(state.clone(), path, target, *mutable, *pinned, returns)?
                {
                    let Value::Ref { place: origin, .. } = reference else {
                        return Err(Error::checker(
                            "return origin validation produced a non-reference",
                        ));
                    };
                    let same = self.same_location(place, &origin);
                    let same = self.circuit.and(candidate.guard, same);
                    covered = self.circuit.or(covered, same);
                }
                Ok(covered)
            }
            Value::Record(name, fields) => {
                let mut covered = TRUE;
                for (field, value) in fields {
                    let id = self
                        .checked
                        .declarations()
                        .field_id(&Type::Named(name.clone()), field)
                        .ok_or_else(|| Error::checker("missing executed return field"))?;
                    let mut nested = path.to_vec();
                    nested.push(Path::Field(id));
                    let valid =
                        self.reference_coverage(state, value, &nested, returns, depth + 1)?;
                    covered = self.circuit.and(covered, valid);
                }
                Ok(covered)
            }
            Value::Tuple(values) | Value::Array(_, values) => {
                let mut covered = TRUE;
                let array = matches!(value, Value::Array(_, _));
                for (index, element) in values.iter().enumerate() {
                    let mut nested = path.to_vec();
                    nested.push(if array {
                        Path::Index(index as u128)
                    } else {
                        Path::Tuple(index)
                    });
                    let valid =
                        self.reference_coverage(state, element, &nested, returns, depth + 1)?;
                    covered = self.circuit.and(covered, valid);
                }
                Ok(covered)
            }
            Value::Enum(name, tag, values) => {
                let mut covered = TRUE;
                let known = returns
                    .bounds
                    .iter()
                    .filter(|(slot, _)| path_matches(slot, path))
                    .collect::<Vec<_>>();
                if !known.is_empty() {
                    covered = FALSE;
                    for (index, variant) in self.enums[name].clone().iter().enumerate() {
                        let id = self
                            .checked
                            .declarations()
                            .variant_id(&Type::Named(name.clone()), &variant.name)
                            .ok_or_else(|| {
                                Error::checker("missing executed return variant bound")
                            })?;
                        if known.iter().any(|(_, choices)| choices.contains(&id)) {
                            let allowed = self
                                .circuit
                                .eq_word(tag, &Circuit::constant(index as u128, 64, false));
                            covered = self.circuit.or(covered, allowed);
                        }
                    }
                }
                for (index, value) in values.iter().enumerate() {
                    let Some(value) = value else {
                        continue;
                    };
                    let variant = self.enums[name][index].name.clone();
                    let id = self
                        .checked
                        .declarations()
                        .variant_id(&Type::Named(name.clone()), &variant)
                        .ok_or_else(|| Error::checker("missing executed return variant"))?;
                    let active = self
                        .circuit
                        .eq_word(tag, &Circuit::constant(index as u128, 64, false));
                    let mut branch = state.clone();
                    branch.guard = self.circuit.and(branch.guard, active);
                    let mut nested = path.to_vec();
                    nested.push(Path::Payload(id, 0));
                    let valid =
                        self.reference_coverage(&branch, value, &nested, returns, depth + 1)?;
                    let valid = self.circuit.or(self.circuit.not(active), valid);
                    covered = self.circuit.and(covered, valid);
                }
                Ok(covered)
            }
            Value::Slice(_) => Err(Error::unsupported(
                "reusable slice results require a view-origin summary",
            )),
            _ => Ok(TRUE),
        }
    }

    pub(super) fn contract_return_values(
        &mut self,
        state: State,
        function: &Function,
        arguments: &[Value],
        guards: Option<&guarded_returns::Guards>,
    ) -> Result<Vec<(State, Value)>> {
        if !self.reference_type(&function.return_type, 0)? {
            let mut state = state;
            let value = self.fresh_value(&mut state, &function.return_type, 0)?;
            return Ok(vec![(state, value)]);
        }
        let declarations = self.checked.declarations();
        let id = declarations
            .function_id(&function.name)
            .ok_or_else(|| Error::checker("missing checked contract function identity"))?;
        let body = declarations
            .bodies
            .get(&function.name)
            .ok_or_else(|| Error::unsupported("reference contract has no checked body"))?;
        let entry = self.old.clone();
        let returns = ReferenceModel {
            guards,
            source: entry.as_ref(),
            arguments,
            origins: body
                .call_return_origins
                .get(&id)
                .cloned()
                .unwrap_or_default(),
            bounds: body
                .call_return_variant_bounds
                .get(&id)
                .cloned()
                .unwrap_or_default(),
        };
        let guard = state.guard;
        let values = self.reference_value(state, &function.return_type, &[], &returns, 0)?;
        // Reference origins and variant bounds were checked against every
        // executed provider result before its certificate became available.
        // POD result fields are nondeterministic; their fresh validity bits
        // are not universally quantified coverage conditions on the inputs.
        if values.is_empty() && self.circuit.satisfy(guard)?.is_some() {
            return Err(Error::unsupported(
                "checked return origins do not cover every feasible contract input",
            ));
        }
        Ok(values)
    }

    pub(super) fn reference_value(
        &mut self,
        mut state: State,
        ty: &Type,
        path: &[Path],
        returns: &ReferenceModel<'_>,
        depth: usize,
    ) -> Result<Vec<(State, Value)>> {
        self.tick()?;
        if depth > 32 {
            return Err(Error::limit("contract result nesting exceeds 32"));
        }
        let ty = self.resolve_type(ty)?;
        if !self.reference_type(&ty, depth)? {
            let value = self.fresh_value(&mut state, &ty, 0)?;
            return Ok(vec![(state, value)]);
        }
        match &ty {
            Type::Reference { target, mutable } | Type::PinnedReference { target, mutable } => {
                let pinned = matches!(ty, Type::PinnedReference { .. });
                self.return_references(state, path, target, *mutable, pinned, returns)
            }
            Type::Tuple(types) => {
                let components = types
                    .iter()
                    .enumerate()
                    .map(|(i, ty)| (Path::Tuple(i), ty.clone()))
                    .collect::<Vec<_>>();
                Ok(self
                    .return_components(state, &components, path, returns, depth)?
                    .into_iter()
                    .map(|(state, values)| (state, Value::Tuple(values)))
                    .collect())
            }
            Type::Array(element, len) => {
                if *len > 64 {
                    return Err(Error::limit("symbolic arrays are limited to 64 elements"));
                }
                let components = (0..*len)
                    .map(|i| (Path::Index(i as u128), (**element).clone()))
                    .collect::<Vec<_>>();
                Ok(self
                    .return_components(state, &components, path, returns, depth)?
                    .into_iter()
                    .map(|(state, values)| (state, Value::Array((**element).clone(), values)))
                    .collect())
            }
            Type::Named(name) if self.records.contains_key(name) => {
                let fields = self.records[name].clone();
                let components = fields
                    .iter()
                    .map(|field| {
                        let id = self
                            .checked
                            .declarations()
                            .field_id(&ty, &field.name)
                            .ok_or_else(|| Error::checker("missing return-field identity"))?;
                        Ok((Path::Field(id), field.ty.clone()))
                    })
                    .collect::<Result<Vec<_>>>()?;
                Ok(self
                    .return_components(state, &components, path, returns, depth)?
                    .into_iter()
                    .map(|(state, values)| {
                        (
                            state,
                            Value::Record(
                                name.clone(),
                                fields
                                    .iter()
                                    .map(|field| field.name.clone())
                                    .zip(values)
                                    .collect(),
                            ),
                        )
                    })
                    .collect())
            }
            Type::Named(name) if self.enums.contains_key(name) => {
                let variants = self.enums[name].clone();
                let mut output = Vec::new();
                for (index, variant) in variants.iter().enumerate() {
                    let mut state = state.clone();
                    if let Some(guards) = returns.guards {
                        let guard = guards
                            .get(&guarded_returns::Key::Variant(path.to_vec(), index))
                            .copied()
                            .unwrap_or(FALSE);
                        state.guard = self.circuit.and(state.guard, guard);
                        if self.circuit.satisfy(state.guard)?.is_none() {
                            continue;
                        }
                    }
                    let id = self
                        .checked
                        .declarations()
                        .variant_id(&ty, &variant.name)
                        .ok_or_else(|| Error::checker("missing return-variant identity"))?;
                    let known = returns
                        .bounds
                        .iter()
                        .filter(|(slot, _)| path_matches(slot, path))
                        .collect::<Vec<_>>();
                    if !known.is_empty() && !known.iter().any(|(_, choices)| choices.contains(&id))
                    {
                        continue;
                    }
                    if let Some(payload) = variant.fields.first() {
                        let mut nested = path.to_vec();
                        nested.push(Path::Payload(id, 0));
                        for (state, payload) in self.reference_value(
                            state.clone(),
                            payload,
                            &nested,
                            returns,
                            depth + 1,
                        )? {
                            let value = self.construct_enum(name, index, Some(payload))?;
                            output.push((state, value));
                        }
                    } else {
                        output.push((state.clone(), self.construct_enum(name, index, None)?));
                    }
                    self.return_limit(output.len())?;
                }
                Ok(output)
            }
            _ => {
                let value = self.fresh_value(&mut state, &ty, 0)?;
                Ok(vec![(state, value)])
            }
        }
    }

    fn return_components(
        &mut self,
        state: State,
        components: &[(Path, Type)],
        path: &[Path],
        returns: &ReferenceModel<'_>,
        depth: usize,
    ) -> Result<Vec<(State, Vec<Value>)>> {
        let mut runs = vec![(state, Vec::new())];
        for (component, ty) in components {
            let mut nested = path.to_vec();
            nested.push(component.clone());
            let mut output = Vec::new();
            for (state, values) in runs {
                for (state, value) in
                    self.reference_value(state, ty, &nested, returns, depth + 1)?
                {
                    let mut values = values.clone();
                    values.push(value);
                    output.push((state, values));
                    self.return_limit(output.len())?;
                }
            }
            runs = output;
        }
        Ok(runs)
    }

    pub(super) fn return_references(
        &mut self,
        state: State,
        path: &[Path],
        target: &Type,
        mutable: bool,
        pinned: bool,
        returns: &ReferenceModel<'_>,
    ) -> Result<Vec<(State, Value)>> {
        Ok(self
            .reference_candidates(state, path, target, mutable, pinned, returns)?
            .into_iter()
            .map(|candidate| (candidate.state, candidate.reference))
            .collect())
    }

    pub(super) fn reference_candidates(
        &mut self,
        state: State,
        path: &[Path],
        target: &Type,
        mutable: bool,
        pinned: bool,
        returns: &ReferenceModel<'_>,
    ) -> Result<Vec<ReferenceCandidate>> {
        let sources = returns
            .origins
            .iter()
            .enumerate()
            .filter(|(_, source)| !source.lifetime_only && path_matches(&source.storage, path))
            .collect::<Vec<_>>();
        if sources.is_empty() {
            return Err(Error::unsupported(
                "returned reference slot has no checked value-origin summary",
            ));
        }
        let mut output = Vec::new();
        for (index, source) in sources {
            self.tick()?;
            let mut state = state.clone();
            if let Some(guards) = returns.guards {
                // Reject a wholly inactive origin before projecting input
                // payloads. Exact physical choices are filtered below.
                let mut guard = FALSE;
                for (key, condition) in guards {
                    self.tick()?;
                    if let guarded_returns::Key::Origin(slot, source, _) = key {
                        if slot == path && *source == index {
                            guard = self.circuit.or(guard, *condition);
                        }
                    }
                }
                state.guard = self.circuit.and(state.guard, guard);
                if self.circuit.satisfy(state.guard)?.is_none() {
                    continue;
                }
            }
            if source.global.is_some()
                || source.fresh_allocation.is_some()
                || source.owned_allocation
                || source.word_stored
                || source.word_view_address
            {
                return Err(Error::unsupported("returned reference requires an unmodeled global, allocation or word-memory origin"));
            }
            let argument = returns.arguments.get(source.parameter).ok_or_else(|| {
                Error::checker("return origin parameter is outside the checked signature")
            })?;
            let mut input_path = source.input_storage.clone();
            for (position, selected) in path.iter().enumerate() {
                if let Some(Some(input)) = source.storage_inputs.get(position) {
                    if let Some(slot @ Path::DynamicIndex) = input_path.get_mut(*input) {
                        if matches!(selected, Path::Index(_)) {
                            *slot = selected.clone();
                        }
                    }
                }
            }
            let inputs = self.return_project(
                returns.source.unwrap_or(&state),
                vec![Cursor {
                    guard: state.guard,
                    value: argument.clone(),
                    place: None,
                    view: None,
                    selection: Vec::new(),
                }],
                &input_path,
            )?;
            for input in inputs {
                let Value::Ref { place, .. } = input.value else {
                    return Err(Error::unsupported(
                        "return origin did not select a modeled reference value",
                    ));
                };
                let value = self.read(&state, &place)?;
                let projected = self.return_project(
                    &state,
                    vec![Cursor {
                        guard: input.guard,
                        value,
                        place: Some(place),
                        view: None,
                        selection: input.selection,
                    }],
                    &source.referent_projection,
                )?;
                for projected in projected {
                    let place = projected.place.ok_or_else(|| {
                        Error::checker("projected return origin has no caller storage")
                    })?;
                    self.compatible(&projected.value, target)?;
                    let mut state = state.clone();
                    state.guard = projected.guard;
                    if let Some(guards) = returns.guards {
                        let key = guarded_returns::Key::Origin(
                            path.to_vec(),
                            index,
                            projected.selection.clone(),
                        );
                        let selected = guards.get(&key).copied().unwrap_or(FALSE);
                        state.guard = self.circuit.and(state.guard, selected);
                        if self.circuit.satisfy(state.guard)?.is_none() {
                            continue;
                        }
                    }
                    output.push(ReferenceCandidate {
                        state,
                        reference: Value::Ref {
                            place,
                            target: target.clone(),
                            mutable,
                            pinned,
                        },
                        selection: projected.selection,
                    });
                    self.return_limit(output.len())?;
                }
            }
        }
        Ok(output)
    }

    fn return_project(
        &mut self,
        state: &State,
        mut cursors: Vec<Cursor>,
        path: &[Path],
    ) -> Result<Vec<Cursor>> {
        for segment in path {
            let mut output = Vec::new();
            for mut cursor in cursors {
                self.tick()?;
                match segment {
                    Path::Dereference => {
                        let Value::Ref { place, .. } = cursor.value else {
                            return Err(Error::unsupported(
                                "return origin dereferences an unmodeled value",
                            ));
                        };
                        cursor.value = self.read(state, &place)?;
                        cursor.place = Some(place);
                        cursor.view = None;
                        output.push(cursor);
                    }
                    Path::Field(id) => {
                        let Value::Record(name, fields) = &cursor.value else {
                            return Err(Error::unsupported(
                                "return field origin is not a modeled record",
                            ));
                        };
                        if self
                            .checked
                            .declarations()
                            .aggregate_id(&Type::Named(name.clone()))
                            != Some(id.owner)
                        {
                            return Err(Error::checker("return field origin has the wrong owner"));
                        }
                        cursor.value = fields
                            .get(id.index)
                            .ok_or_else(|| Error::checker("return field index is invalid"))?
                            .1
                            .clone();
                        if let Some(place) = &mut cursor.place {
                            place.path.push(Segment::Field(id.index));
                        }
                        output.push(cursor);
                    }
                    Path::Tuple(index) => {
                        let Value::Tuple(values) = &cursor.value else {
                            return Err(Error::unsupported(
                                "return tuple origin is not a modeled tuple",
                            ));
                        };
                        cursor.value = values
                            .get(*index)
                            .ok_or_else(|| Error::checker("return tuple index is invalid"))?
                            .clone();
                        if let Some(place) = &mut cursor.place {
                            place.path.push(Segment::Field(*index));
                        }
                        output.push(cursor);
                    }
                    Path::Payload(id, 0) => {
                        let Value::Enum(name, tag, values) = &cursor.value else {
                            return Err(Error::unsupported(
                                "return payload origin is not a modeled enum",
                            ));
                        };
                        if self
                            .checked
                            .declarations()
                            .aggregate_id(&Type::Named(name.clone()))
                            != Some(id.owner)
                        {
                            return Err(Error::checker(
                                "return payload origin has the wrong owner",
                            ));
                        }
                        let selected = self
                            .circuit
                            .eq_word(tag, &Circuit::constant(id.index as u128, 64, false));
                        cursor.guard = self.circuit.and(cursor.guard, selected);
                        if cursor.guard == FALSE {
                            continue;
                        }
                        let Some(value) = values.get(id.index).and_then(Option::as_ref) else {
                            continue;
                        };
                        cursor.value = value.clone();
                        if let Some(place) = &mut cursor.place {
                            place.path.push(Segment::Payload(id.index));
                        }
                        output.push(cursor);
                    }
                    Path::Index(_)
                    | Path::DynamicIndex
                    | Path::SliceIndex(_)
                    | Path::SliceDynamicIndex => {
                        let Value::Array(_, values) = &cursor.value else {
                            return Err(Error::unsupported(
                                "return index origin has no bounded array backing",
                            ));
                        };
                        let (start, end, unknown) = cursor.view.unwrap_or((0, values.len(), false));
                        let requested = match segment {
                            Path::Index(i) | Path::SliceIndex(i) => usize::try_from(*i).ok(),
                            _ => None,
                        };
                        let indices = if let Some(index) = requested.filter(|_| !unknown) {
                            start
                                .checked_add(index)
                                .filter(|index| *index < end)
                                .into_iter()
                                .collect::<Vec<_>>()
                        } else {
                            (start..end).collect()
                        };
                        for index in indices {
                            let mut branch = cursor.clone();
                            // Indices are relative to the checked origin's
                            // projection sequence, never provider heap IDs or
                            // ordinals that change when a payload is inactive.
                            branch.selection.push(index);
                            branch.value = values[index].clone();
                            branch.view = None;
                            if let Some(place) = &mut branch.place {
                                place.path.push(Segment::Index(Circuit::constant(
                                    index as u128,
                                    64,
                                    false,
                                )));
                            }
                            output.push(branch);
                            self.return_limit(output.len())?;
                        }
                    }
                    Path::SliceRange { start, end } => {
                        let Value::Array(_, values) = &cursor.value else {
                            return Err(Error::unsupported(
                                "return range has no bounded array backing",
                            ));
                        };
                        let (base, limit, unknown) =
                            cursor.view.unwrap_or((0, values.len(), false));
                        if unknown {
                            // Composing with an unknown starting offset cannot
                            // narrow the physical range to a fixed prefix.
                            cursor.view = Some((base, limit, true));
                            output.push(cursor);
                            continue;
                        }
                        let start = usize::try_from(*start)
                            .ok()
                            .and_then(|start| base.checked_add(start));
                        let end = usize::try_from(*end)
                            .ok()
                            .and_then(|end| base.checked_add(end));
                        match (start, end) {
                            (Some(start), Some(end)) if start <= end && end <= limit => {
                                cursor.view = Some((start, end, unknown));
                                output.push(cursor);
                            }
                            _ => {
                                return Err(Error::unsupported(
                                    "return origin range exceeds its modeled backing",
                                ))
                            }
                        }
                    }
                    Path::SliceRangeUnknown | Path::SliceHalf(_) => {
                        let Value::Array(_, values) = &cursor.value else {
                            return Err(Error::unsupported(
                                "return range has no bounded array backing",
                            ));
                        };
                        let (start, end, _) = cursor.view.unwrap_or((0, values.len(), false));
                        cursor.view = Some((start, end, true));
                        output.push(cursor);
                    }
                    _ => {
                        return Err(Error::unsupported(
                            "return origin uses an unmodeled storage projection",
                        ))
                    }
                }
                self.return_limit(output.len())?;
            }
            cursors = output;
        }
        Ok(cursors)
    }

    fn return_limit(&self, count: usize) -> Result<()> {
        if count > 256 {
            Err(Error::limit("contract return alternatives exceed 256"))
        } else {
            Ok(())
        }
    }

    pub(super) fn reference_type(&mut self, ty: &Type, depth: usize) -> Result<bool> {
        self.tick()?;
        if depth > 32 {
            return Err(Error::limit("contract result type nesting exceeds 32"));
        }
        Ok(match self.resolve_type(ty)? {
            Type::Reference { .. } | Type::PinnedReference { .. } => true,
            Type::Array(element, len) => len != 0 && self.reference_type(&element, depth + 1)?,
            Type::Tuple(types) => {
                let mut found = false;
                for ty in types {
                    found |= self.reference_type(&ty, depth + 1)?;
                }
                found
            }
            Type::Named(name) if self.records.contains_key(&name) => {
                let mut found = false;
                for field in self.records[&name].clone() {
                    found |= self.reference_type(&field.ty, depth + 1)?;
                }
                found
            }
            Type::Named(name) if self.enums.contains_key(&name) => {
                let mut found = false;
                for variant in self.enums[&name].clone() {
                    for ty in variant.fields {
                        found |= self.reference_type(&ty, depth + 1)?;
                    }
                }
                found
            }
            _ => false,
        })
    }
}

pub(super) fn path_matches(schema: &[Path], selected: &[Path]) -> bool {
    schema.len() == selected.len()
        && schema.iter().zip(selected).all(|(a, b)| {
            a == b
                || matches!(
                    (a, b),
                    (Path::DynamicIndex, Path::Index(_))
                        | (Path::SliceDynamicIndex, Path::SliceIndex(_))
                )
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_wrong_field_origin_cannot_cover_the_executed_reference() {
        let program = crate::parse_program(
            r#"
          (#struct Pair () (: first #u8 : second #u8))
          (#fn pick (: source (#ref-mut Pair)) (#ref-mut #u8)
            (#return (#borrow-mut (#get (#deref source) first))))"#,
        )
        .unwrap();
        let checked = CheckedProgram::validate(&program).unwrap();
        let graph = Graph::new(checked.program(), checked.declarations());
        let mut engine = Engine::new(&checked, &graph, Span::new(0, 0, 1, 1));
        let mut state = State::new();
        let function = engine.function("pick").unwrap();
        let argument = engine
            .fresh_value(&mut state, &function.parameters[0].ty, 0)
            .unwrap();
        let arguments = vec![argument];
        let (state, value) = engine
            .call(state, function, arguments.clone(), false)
            .unwrap()
            .pop()
            .unwrap();
        engine
            .verify_contract_return(&state, function, &arguments, &value)
            .unwrap();
        let id = checked.declarations().function_id("pick").unwrap();
        let body = &checked.declarations().bodies["pick"];
        let mut origins = body.call_return_origins[&id].clone();
        let wrong = checked
            .declarations()
            .field_id(&Type::Named("Pair".into()), "second")
            .unwrap();
        for origin in &mut origins {
            origin.referent_projection = vec![Path::Field(wrong)];
        }
        let returns = ReferenceModel {
            guards: None,
            source: None,
            arguments: &arguments,
            origins,
            bounds: Bounds::new(),
        };
        let covered = engine
            .reference_coverage(&state, &value, &[], &returns, 0)
            .unwrap();
        let missing = engine.circuit.and(state.guard, engine.circuit.not(covered));
        assert!(engine.circuit.satisfy(missing).unwrap().is_some());
        let missing = ReferenceModel {
            guards: None,
            source: None,
            arguments: &arguments,
            origins: Vec::new(),
            bounds: Bounds::new(),
        };
        let error = engine
            .reference_coverage(&state, &value, &[], &missing, 0)
            .unwrap_err();
        assert_eq!(
            error.diagnostic_code(),
            crate::DiagnosticCode::ProofUnsupported
        );
    }

    #[test]
    fn incorrect_variant_bounds_do_not_hide_a_fieldless_executed_return() {
        let program = crate::parse_program(
            r#"
          (#enum Maybe () (: Maybe.None : Maybe.Some (#ref #u8)))
          (#fn none () Maybe (#return (#enum-literal Maybe.None)))"#,
        )
        .unwrap();
        let checked = CheckedProgram::validate(&program).unwrap();
        let graph = Graph::new(checked.program(), checked.declarations());
        let mut engine = Engine::new(&checked, &graph, Span::new(0, 0, 1, 1));
        let function = engine.function("none").unwrap();
        let (state, value) = engine
            .call(State::new(), function, Vec::new(), false)
            .unwrap()
            .pop()
            .unwrap();
        engine
            .verify_contract_return(&state, function, &[], &value)
            .unwrap();
        let wrong = checked
            .declarations()
            .variant_id(&Type::Named("Maybe".into()), "Maybe.Some")
            .unwrap();
        let returns = ReferenceModel {
            guards: None,
            source: None,
            arguments: &[],
            origins: Vec::new(),
            bounds: Bounds::from([(Vec::new(), std::collections::HashSet::from([wrong]))]),
        };
        let covered = engine
            .reference_coverage(&state, &value, &[], &returns, 0)
            .unwrap();
        let missing = engine.circuit.and(state.guard, engine.circuit.not(covered));
        assert!(engine.circuit.satisfy(missing).unwrap().is_some());
    }

    #[test]
    fn absent_or_invalid_projection_keys_do_not_fall_back_to_other_candidates() {
        let program = crate::parse_program(
            r#"
          (#fn at (: values (#ref (#array #u8 2)) : index #usize) (#ref #u8)
            (#return (#borrow (#index (#deref values) index))))
        "#,
        )
        .unwrap();
        let checked = CheckedProgram::validate(&program).unwrap();
        let graph = Graph::new(checked.program(), checked.declarations());
        let mut engine = Engine::new(&checked, &graph, Span::new(0, 0, 1, 1));
        let function = engine.function("at").unwrap();
        let mut state = State::new();
        let arguments = function
            .parameters
            .iter()
            .map(|parameter| engine.fresh_value(&mut state, &parameter.ty, 0))
            .collect::<Result<Vec<_>>>()
            .unwrap();
        for guards in [
            guarded_returns::Guards::new(),
            guarded_returns::Guards::from([(
                guarded_returns::Key::Origin(Vec::new(), 0, vec![99]),
                TRUE,
            )]),
        ] {
            let error = engine
                .contract_return_values(state.clone(), function, &arguments, Some(&guards))
                .err()
                .unwrap();
            assert_eq!(
                error.diagnostic_code().proof_outcome(),
                Some(crate::ProofOutcome::Unsupported)
            );
        }
    }

    #[test]
    fn inactive_payloads_and_aliased_inputs_keep_stable_projection_choices() {
        let program = crate::parse_program(
            r#"
          (#enum Maybe () (: Maybe.None : Maybe.Some (#ref #u8)))
          (#fn unused () () (#return ()))
        "#,
        )
        .unwrap();
        let checked = CheckedProgram::validate(&program).unwrap();
        let graph = Graph::new(checked.program(), checked.declarations());
        let mut engine = Engine::new(&checked, &graph, Span::new(0, 0, 1, 1));
        let mut state = State::new();
        let reference = engine
            .fresh_value(
                &mut state,
                &Type::Reference {
                    mutable: false,
                    target: Box::new(Type::U8),
                },
                0,
            )
            .unwrap();
        let absent = engine.construct_enum("Maybe", 0, None).unwrap();
        let present = engine.construct_enum("Maybe", 1, Some(reference)).unwrap();
        let value = Value::Array(
            Type::Named("Maybe".into()),
            vec![absent, present.clone(), present],
        );
        let variant = checked
            .declarations()
            .variant_id(&Type::Named("Maybe".into()), "Maybe.Some")
            .unwrap();
        let projected = engine
            .return_project(
                &state,
                vec![Cursor {
                    guard: state.guard,
                    value,
                    place: None,
                    view: None,
                    selection: Vec::new(),
                }],
                &[Path::DynamicIndex, Path::Payload(variant, 0)],
            )
            .unwrap();
        assert_eq!(projected.len(), 2);
        assert_eq!(projected[0].selection, vec![1]);
        assert_eq!(projected[1].selection, vec![2]);
        let (Value::Ref { place: a, .. }, Value::Ref { place: b, .. }) =
            (&projected[0].value, &projected[1].value)
        else {
            panic!("references expected")
        };
        assert_eq!(engine.same_location(a, b), TRUE);
    }

    #[test]
    fn a_fixed_subrange_after_an_unknown_offset_keeps_all_possible_origins() {
        let program = crate::parse_program("(#fn unused () () (#return ()))").unwrap();
        let checked = CheckedProgram::validate(&program).unwrap();
        let graph = Graph::new(checked.program(), checked.declarations());
        let mut engine = Engine::new(&checked, &graph, Span::new(0, 0, 1, 1));
        let mut state = State::new();
        let reference = engine
            .fresh_value(
                &mut state,
                &Type::Reference {
                    mutable: false,
                    target: Box::new(Type::Array(Box::new(Type::U8), 4)),
                },
                0,
            )
            .unwrap();
        let Value::Ref { place, .. } = reference else {
            panic!("reference expected")
        };
        let value = engine.read(&state, &place).unwrap();
        let cursors = engine
            .return_project(
                &state,
                vec![Cursor {
                    guard: state.guard,
                    value,
                    place: Some(place),
                    view: None,
                    selection: Vec::new(),
                }],
                &[
                    Path::SliceRangeUnknown,
                    Path::SliceRange { start: 1, end: 2 },
                    Path::SliceIndex(0),
                ],
            )
            .unwrap();
        assert_eq!(cursors.len(), 4);
        for (index, cursor) in cursors.iter().enumerate() {
            assert_eq!(cursor.selection, vec![index]);
        }
    }
}

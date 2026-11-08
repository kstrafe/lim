//! Reference-bearing write frames use checked final store origins. Sources are
//! read at call entry; preparing all replacements precedes any actual heap write.
use super::contract_memory::Target;
use super::contract_return::{path_matches, ReferenceModel};
use super::*;
use crate::typed_body::{ParameterLoanSummary, ParameterStoreSummary};
use crate::typed_place::Segment as Path;

impl Engine<'_, '_> {
    pub(super) fn contract_stored_values(
        &mut self,
        mut state: State,
        entry: &State,
        function: &Function,
        arguments: &[Value],
        target: &Target,
    ) -> Result<Vec<(State, Value)>> {
        if !self.reference_type(&target.ty, 0)? {
            let value = self.fresh_value(&mut state, &target.ty, 0)?;
            return Ok(vec![(state, value)]);
        }
        let model = self.store_model(entry, function, arguments, target)?;
        let guard = state.guard;
        let values = self.reference_value(state, &target.ty, &[], &model, 0)?;
        if values.is_empty() && self.circuit.satisfy(guard)?.is_some() {
            return Err(Error::unsupported(
                "checked store origins do not cover a feasible mutable target",
            ));
        }
        Ok(values)
    }

    pub(super) fn verify_contract_stores(
        &mut self,
        entry: &State,
        post: &State,
        function: &Function,
        arguments: &[Value],
    ) -> Result<()> {
        if self
            .graph
            .forbidden_effect(&function.name, "mutation")?
            .is_none()
        {
            return Ok(());
        }
        let mut needed = false;
        for parameter in &function.parameters {
            needed |= self.stores_references(&parameter.ty, 0)?;
        }
        if !needed {
            return Ok(());
        }
        for (branch, targets) in self.contract_targets(entry.clone(), arguments)? {
            for target in targets.iter().filter(|target| target.mutable) {
                if !self.reference_type(&target.ty, 0)? {
                    continue;
                }
                let model = self.store_model(entry, function, arguments, target)?;
                let mut state = post.clone();
                state.guard = self.circuit.and(state.guard, branch.guard);
                if self.circuit.satisfy(state.guard)?.is_none() {
                    continue;
                }
                let value = self.read(&state, &target.place)?;
                let covered = self.reference_coverage(&state, &value, &[], &model, 0)?;
                let missing = self.circuit.and(state.guard, self.circuit.not(covered));
                if self.circuit.satisfy(missing)?.is_some() {
                    return Err(Error::unsupported("checked store-origin summary does not cover the symbolically executed reference assignment"));
                }
            }
        }
        Ok(())
    }

    fn stores_references(&mut self, ty: &Type, depth: usize) -> Result<bool> {
        self.tick()?;
        if depth > 32 {
            return Err(Error::limit("stored-reference target nesting exceeds 32"));
        }
        Ok(match self.resolve_type(ty)? {
            Type::Reference { mutable, target } | Type::PinnedReference { mutable, target } => {
                (mutable && self.reference_type(&target, 0)?)
                    || self.stores_references(&target, depth + 1)?
            }
            Type::Array(element, _) => self.stores_references(&element, depth + 1)?,
            Type::Tuple(types) => {
                let mut found = false;
                for ty in types {
                    found |= self.stores_references(&ty, depth + 1)?;
                }
                found
            }
            Type::Named(name) if self.records.contains_key(&name) => {
                let mut found = false;
                for field in self.records[&name].clone() {
                    found |= self.stores_references(&field.ty, depth + 1)?;
                }
                found
            }
            Type::Named(name) if self.enums.contains_key(&name) => {
                let mut found = false;
                for variant in self.enums[&name].clone() {
                    for ty in variant.fields {
                        found |= self.stores_references(&ty, depth + 1)?;
                    }
                }
                found
            }
            _ => false,
        })
    }

    fn store_model<'a>(
        &mut self,
        entry: &'a State,
        function: &Function,
        arguments: &'a [Value],
        target: &Target,
    ) -> Result<ReferenceModel<'a>> {
        let declarations = self.checked.declarations();
        let id = declarations
            .function_id(&function.name)
            .ok_or_else(|| Error::checker("missing checked store function"))?;
        let body = declarations
            .bodies
            .get(&function.name)
            .ok_or_else(|| Error::unsupported("store contract has no checked body"))?;
        let stores = body
            .call_store_origins
            .get(&id)
            .cloned()
            .unwrap_or_default();
        self.store_model_from(entry, arguments, target, &stores)
    }

    fn store_model_from<'a>(
        &mut self,
        entry: &'a State,
        arguments: &'a [Value],
        target: &Target,
        stores: &[ParameterStoreSummary],
    ) -> Result<ReferenceModel<'a>> {
        let stores = stores
            .iter()
            .filter(|store| {
                store.destination.parameter == target.parameter
                    && path_matches(&store.destination.input_storage, &target.storage)
            })
            .collect::<Vec<_>>();
        let mut originals = Vec::new();
        self.original_store_origins(&target.ty, target, &[], &mut originals, 0)?;
        if stores.iter().any(|store| store.destination.lifetime_only) {
            return Err(Error::unsupported(
                "reference store destination has only a lifetime anchor",
            ));
        }
        originals.retain(|original| {
            !stores.iter().any(|store| {
                store.definitely_written
                    && !store.preserves_bytes
                    && exact(&store.destination.input_storage)
                    && exact(&store.destination.referent_projection)
                    && prefix(&store.destination.referent_projection, &original.storage)
            })
        });
        let mut bounds = crate::typed_flow::VariantBounds::new();
        for store in stores {
            let destination = &store.destination;
            if destination.global.is_some()
                || destination.fresh_allocation.is_some()
                || destination.word_stored
                || destination.word_view_address
                || destination.owned_allocation
            {
                return Err(Error::unsupported("reference store uses an unmodeled global, allocation or word-memory destination"));
            }
            for source in &store.sources {
                let mut source = source.clone();
                let mut path = destination.referent_projection.clone();
                path.extend(source.storage);
                source.storage = path;
                if !source.storage_inputs.is_empty() {
                    let mut inputs = vec![None; destination.referent_projection.len()];
                    inputs.extend(source.storage_inputs);
                    source.storage_inputs = inputs;
                }
                originals.push(source);
            }
            if store.variants_definitely_written
                && exact(&destination.input_storage)
                && exact(&destination.referent_projection)
            {
                for (path, variant) in &store.variants {
                    let mut nested = destination.referent_projection.clone();
                    nested.extend(path.iter().cloned());
                    bounds.entry(nested).or_default().insert(*variant);
                }
            }
        }
        Ok(ReferenceModel {
            guards: None,
            arguments,
            origins: originals,
            bounds,
            source: Some(entry),
        })
    }

    fn original_store_origins(
        &mut self,
        ty: &Type,
        target: &Target,
        path: &[Path],
        output: &mut Vec<ParameterLoanSummary>,
        depth: usize,
    ) -> Result<()> {
        self.tick()?;
        if depth > 32 {
            return Err(Error::limit("stored reference schema nesting exceeds 32"));
        }
        let ty = self.resolve_type(ty)?;
        match ty {
            Type::Reference { mutable, .. } | Type::PinnedReference { mutable, .. } => {
                if output.len() >= 256 {
                    return Err(Error::limit("stored reference slots exceed 256"));
                }
                let mut input_storage = target.storage.clone();
                input_storage.push(Path::Dereference);
                input_storage.extend(path.iter().cloned());
                output.push(ParameterLoanSummary {
                    fresh_allocation: None,
                    owned_allocation: false,
                    global: None,
                    parameter: target.parameter,
                    mutable,
                    pinned: matches!(self.resolve_type(&ty)?, Type::PinnedReference { .. }),
                    lifetime_only: false,
                    maybe_absent: false,
                    word_stored: false,
                    word_view_address: false,
                    reborrow: false,
                    referent_projection: Vec::new(),
                    input_storage,
                    storage: path.to_vec(),
                    storage_inputs: Vec::new(),
                });
            }
            Type::Tuple(types) => {
                for (index, ty) in types.iter().enumerate() {
                    let mut nested = path.to_vec();
                    nested.push(Path::Tuple(index));
                    self.original_store_origins(ty, target, &nested, output, depth + 1)?;
                }
            }
            Type::Array(element, len) => {
                if len > 64 {
                    return Err(Error::limit("symbolic arrays are limited to 64 elements"));
                }
                for index in 0..len {
                    let mut nested = path.to_vec();
                    nested.push(Path::Index(index as u128));
                    self.original_store_origins(&element, target, &nested, output, depth + 1)?;
                }
            }
            Type::Named(name) if self.records.contains_key(&name) => {
                for field in self.records[&name].clone() {
                    let id = self
                        .checked
                        .declarations()
                        .field_id(&Type::Named(name.clone()), &field.name)
                        .ok_or_else(|| Error::checker("missing stored-reference field"))?;
                    let mut nested = path.to_vec();
                    nested.push(Path::Field(id));
                    self.original_store_origins(&field.ty, target, &nested, output, depth + 1)?;
                }
            }
            Type::Named(name) if self.enums.contains_key(&name) => {
                for variant in self.enums[&name].clone() {
                    let id = self
                        .checked
                        .declarations()
                        .variant_id(&Type::Named(name.clone()), &variant.name)
                        .ok_or_else(|| Error::checker("missing stored-reference variant"))?;
                    if let Some(ty) = variant.fields.first() {
                        let mut nested = path.to_vec();
                        nested.push(Path::Payload(id, 0));
                        self.original_store_origins(ty, target, &nested, output, depth + 1)?;
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }
}

fn prefix(parent: &[Path], child: &[Path]) -> bool {
    parent.len() <= child.len() && path_matches(parent, &child[..parent.len()])
}
fn exact(path: &[Path]) -> bool {
    !path.iter().any(|path| {
        matches!(
            path,
            Path::DynamicIndex
                | Path::SliceDynamicIndex
                | Path::SliceRangeUnknown
                | Path::SliceHalf(_)
        )
    })
}

#[cfg(test)]
mod tests {
    #[test]
    fn definite_reference_replacement_has_a_checked_source() {
        let program = crate::parse_program(
            r#"
          (#struct Slot () (: reference (#ref #u8)))
          (#fn replace (: slot (#ref-mut Slot) : replacement (#ref #u8)) ()
            (#deref-set slot (#struct-literal Slot (: reference replacement)))
            (#return ()))"#,
        )
        .unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let declarations = checked.declarations();
        let id = declarations.function_id("replace").unwrap();
        let stores = &declarations.bodies["replace"].call_store_origins[&id];
        assert_eq!(stores.len(), 1);
        assert!(stores[0].definitely_written && !stores[0].preserves_bytes);
        assert_eq!(stores[0].sources.len(), 1);
        assert_eq!(stores[0].sources[0].parameter, 1);
    }

    #[test]
    fn wrong_or_missing_store_origins_cannot_cover_the_executed_assignment() {
        use super::*;
        let program = crate::parse_program(
            r#"
          (#struct Slot () (: reference (#ref #u8)))
          (#fn replace (: slot (#ref-mut Slot) : replacement (#ref #u8)) ()
            (#deref-set slot (#struct-literal Slot (: reference replacement))) (#return ()))"#,
        )
        .unwrap();
        let checked = CheckedProgram::validate(&program).unwrap();
        let graph = Graph::new(checked.program(), checked.declarations());
        let mut engine = Engine::new(&checked, &graph, Span::new(0, 0, 1, 1));
        let function = engine.function("replace").unwrap();
        let mut entry = State::new();
        let arguments = function
            .parameters
            .iter()
            .map(|parameter| engine.fresh_value(&mut entry, &parameter.ty, 0))
            .collect::<Result<Vec<_>>>()
            .unwrap();
        let (mut post, _) = engine
            .call(entry.clone(), function, arguments.clone(), false)
            .unwrap()
            .pop()
            .unwrap();
        engine
            .verify_contract_stores(&entry, &post, function, &arguments)
            .unwrap();
        let targets = engine
            .contract_targets(entry.clone(), &arguments)
            .unwrap()
            .pop()
            .unwrap()
            .1;
        let target = targets
            .iter()
            .find(|target| engine.reference_type(&target.ty, 0).unwrap())
            .unwrap();
        let mut model = engine
            .store_model(&entry, function, &arguments, target)
            .unwrap();
        let field = checked
            .declarations()
            .field_id(&Type::Named("Slot".into()), "reference")
            .unwrap();
        let source = &mut model.origins[0];
        source.parameter = 0;
        source.input_storage = vec![Path::Dereference, Path::Field(field)];
        let old = engine.read(&entry, &target.place).unwrap();
        let Value::Record(_, old) = old else {
            panic!("record expected")
        };
        let Value::Ref {
            place: old_place, ..
        } = &old[0].1
        else {
            panic!("reference expected")
        };
        let Value::Ref {
            place: new_place, ..
        } = &arguments[1]
        else {
            panic!("reference expected")
        };
        let old_byte = engine.read(&entry, old_place).unwrap();
        let new_byte = engine.read(&entry, new_place).unwrap();
        let equal_contents = engine.equal(&old_byte, &new_byte).unwrap();
        post.guard = engine.circuit.and(post.guard, equal_contents);
        let actual = engine.read(&post, &target.place).unwrap();
        let covered = engine
            .reference_coverage(&post, &actual, &[], &model, 0)
            .unwrap();
        let missing = engine.circuit.and(post.guard, engine.circuit.not(covered));
        assert!(engine.circuit.satisfy(missing).unwrap().is_some());
        model.origins.clear();
        assert_eq!(
            engine
                .reference_coverage(&post, &actual, &[], &model, 0)
                .unwrap_err()
                .diagnostic_code(),
            crate::DiagnosticCode::ProofUnsupported
        );
    }
}

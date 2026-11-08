//! Fresh input origins include possible internal references in pinned parents.
//! Typed in-place projections stop at reference handles; pointed-to storage is
//! a separate object. These relations are may-alias guards, never authorization.
use super::*;

const PAIR_LIMIT: usize = 4096;

impl Engine<'_, '_> {
    fn input_storage_contains(
        &mut self,
        value: &Value,
        target: &Type,
        depth: usize,
    ) -> Result<bool> {
        self.tick()?;
        if depth > 32 {
            return Err(Error::limit("input storage projection nesting exceeds 32"));
        }
        if self.resolve_type(&value.ty())? == *target {
            return Ok(true);
        }
        match value {
            Value::Record(_, fields) => {
                for (_, field) in fields {
                    if self.input_storage_contains(field, target, depth + 1)? {
                        return Ok(true);
                    }
                }
            }
            Value::Array(_, values) | Value::Tuple(values) => {
                for field in values {
                    if self.input_storage_contains(field, target, depth + 1)? {
                        return Ok(true);
                    }
                }
            }
            Value::Enum(_, _, values) => {
                for value in values {
                    self.tick()?;
                    if let Some(field) = value {
                        if self.input_storage_contains(field, target, depth + 1)? {
                            return Ok(true);
                        }
                    }
                }
            }
            _ => {}
        }
        Ok(false)
    }

    pub(super) fn register_input_storage(
        &mut self,
        state: &mut State,
        root: usize,
        pinned_mutable: bool,
    ) -> Result<()> {
        let value = state
            .heap
            .get(root)
            .ok_or_else(|| Error::checker("fresh input referent is missing"))?;
        let target = self.resolve_type(&value.ty())?;
        let parent = value.contains_ref() || pinned_mutable;
        let mut pairs = BTreeSet::new();
        for &other in &state.input_parents {
            if self.input_storage_contains(&state.heap[other], &target, 0)? {
                pairs.insert((root.min(other), root.max(other)));
            }
        }
        if parent {
            for &other in &state.input_referents {
                let target = self.resolve_type(&state.heap[other].ty())?;
                if self.input_storage_contains(value, &target, 0)? {
                    pairs.insert((root.min(other), root.max(other)));
                }
            }
        }
        for pair in pairs {
            if state.input_parent_aliases.len() >= PAIR_LIMIT
                && !state.input_parent_aliases.contains(&pair)
            {
                return Err(Error::limit("input parent aliases exceed 4096 pairs"));
            }
            state.input_parent_aliases.insert(pair);
        }
        state.input_referents.insert(root);
        if parent {
            state.input_parents.insert(root);
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn with_engine(test: impl FnOnce(&mut Engine<'_, '_>)) {
        let program = crate::parse_program(
            r#"
          (#struct Frame () (: value #u8 : retained (#pin-ref #u8)))
          (#struct Holder () (: retained (#ref #u8)))
          (#fn validate (: user (#ref #u8) : accepted #bool) #bool (#return accepted))
          (#fn perform (: user (#ref #u8)) () (#return ()))
        "#,
        )
        .unwrap();
        let checked = CheckedProgram::validate(&program).unwrap();
        let graph = Graph::new(checked.program(), checked.declarations());
        let mut engine = Engine::new(&checked, &graph, Span::new(0, 0, 1, 1));
        engine.trace = Some(Trace::Validated(ValidationRule {
            validator: "validate".into(),
            validator_parameter: 0,
            action: "perform".into(),
            action_parameter: 0,
        }));
        test(&mut engine);
    }

    fn root(value: &Value) -> usize {
        let Value::Ref { place, .. } = value else {
            panic!("reference")
        };
        place.root
    }

    #[test]
    fn pinned_parent_relations_cover_earlier_and_later_input_referents() {
        with_engine(|engine| {
            let mut state = State::new();
            let shared = Type::Reference {
                mutable: false,
                target: Box::new(Type::U8),
            };
            let earlier = engine.fresh_value(&mut state, &shared, 0).unwrap();
            let parent = engine
                .fresh_value(
                    &mut state,
                    &Type::PinnedReference {
                        mutable: true,
                        target: Box::new(Type::Named("Frame".into())),
                    },
                    0,
                )
                .unwrap();
            let later = engine.fresh_value(&mut state, &shared, 0).unwrap();
            for value in [&earlier, &later] {
                assert!(state
                    .possibly_aliasing_roots(root(&parent))
                    .contains(&root(value)));
                assert!(state
                    .possibly_aliasing_roots(root(value))
                    .contains(&root(&parent)));
            }
            assert!(engine
                .scalar_alias_cases(&state, &[earlier, parent, later], 0)
                .unwrap()
                .is_none());
        });
    }

    #[test]
    fn reference_handles_do_not_embed_their_referents_in_parent_storage() {
        with_engine(|engine| {
            let mut state = State::new();
            let parent = engine
                .fresh_value(
                    &mut state,
                    &Type::Reference {
                        mutable: true,
                        target: Box::new(Type::Named("Holder".into())),
                    },
                    0,
                )
                .unwrap();
            assert!(state.input_parents.contains(&root(&parent)));
            assert!(state.input_parent_aliases.is_empty());
        });
    }
}

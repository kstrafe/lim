//! Pure loop specifications and scoped validation-evidence assumptions.
use super::*;

pub(super) fn pure(
    expr: &Expr,
    locals: &BTreeMap<String, (Location, Type)>,
    depth: usize,
    variants: &BTreeSet<String>,
    positive: bool,
) -> Result<()> {
    if depth > 64 {
        return Err(Error::limit("induction expression nesting exceeds 64"));
    }
    match expr {
        Expr::Symbol(name)
            if matches!(name.as_str(), "true" | "false") || locals.contains_key(name) => Ok(()),
        Expr::Integer(_) | Expr::UnsignedInteger(_) | Expr::Char(_) => Ok(()),
        Expr::List(items) if matches!(items.first(), Some(Expr::Function(_))) =>
            Err(Error::unsupported("induction specifications cannot call user functions")),
        Expr::List(items) if items.is_empty() => Ok(()),
        Expr::List(_) => {
            let (head, args) = form(expr).ok_or_else(||
                Error::unsupported("induction specifications cannot call user functions"))?;
            if numeric(head).is_some() || matches!(head,
                "proof-not" | "proof-eq" | "index" | "deref" | "borrow"
                | "slice-len" | "slice-mut-len" | "slice-idx" | "slice-mut-idx") {
                for arg in args { pure(arg, locals, depth + 1, variants, false)?; }
                return Ok(());
            }
            match head {
                "proof-validated" => {
                    if !positive {
                        return Err(Error::unsupported("#proof-validated must occur positively in a loop invariant; it cannot be negated, compared, or used as a condition or rank"));
                    }
                    arity(head, args, 2)?;
                    // The descriptor is checked by validation_query. It names
                    // a validator parameter, not an executable expression.
                    pure(&args[1], locals, depth + 1, variants, false)
                }
                "proof-and" | "proof-or" => {
                    for arg in args { pure(arg, locals, depth + 1, variants, positive)?; }
                    Ok(())
                }
                "proof-implies" => {
                    arity(head, args, 2)?;
                    pure(&args[0], locals, depth + 1, variants, false)?;
                    pure(&args[1], locals, depth + 1, variants, positive)
                }
                "if" => {
                    if !(2..=3).contains(&args.len()) { return Err(Error::invalid("induction #if requires a condition and branches")); }
                    pure(&args[0], locals, depth + 1, variants, false)?;
                    for arg in &args[1..] { pure(arg, locals, depth + 1, variants, positive)?; }
                    Ok(())
                }
                "match" => {
                    if args.len() < 2 { return Err(Error::invalid("induction match requires a value and cases")); }
                    if args.len() > 257 { return Err(Error::limit("induction matches are limited to 256 cases")); }
                    pure(&args[0], locals, depth + 1, variants, false)?;
                    for arm in &args[1..] {
                        let Some(("case", parts)) = form(arm) else {
                            return Err(Error::unsupported("induction matches require explicit #case arms"));
                        };
                        if parts.len() != 2 { return Err(Error::unsupported("induction cases require a pattern and one pure value")); }
                        let mut scoped = locals.clone();
                        match &parts[0] {
                            Expr::Symbol(name) if name == "_" || variants.contains(name) => {},
                            Expr::List(items) if items.len() == 2 && symbol(&items[0]).is_ok_and(|name| variants.contains(name)) => {
                                let name = symbol(&items[1])?;
                                if name != "_" {
                                    crate::names::require(name, "value").map_err(Error::invalid)?;
                                    if scoped.contains_key(name) { return Err(Error::invalid("induction pattern bindings cannot shadow locals")); }
                                    scoped.insert(name.into(), (Location { root: 0, path: Vec::new() }, Type::Unit));
                                }
                            }
                            _ => return Err(Error::unsupported("induction matches require simple enum patterns")),
                        }
                        pure(&parts[1], &scoped, depth + 1, variants, positive)?;
                    }
                    Ok(())
                }
                "literal" => {
                    arity(head, args, 2)?;
                    if !matches!(args[1], Expr::Integer(_) | Expr::UnsignedInteger(_)) {
                        return Err(Error::invalid("nonliteral induction literal"));
                    }
                    Ok(())
                }
                "as" | "get" | "variant-is" => {
                    arity(head, args, 2)?;
                    pure(&args[0], locals, depth + 1, variants, false)
                }
                "proof-no-overflow" => {
                    arity(head, args, 3)?;
                    numeric(symbol(&args[0])?).ok_or_else(|| Error::invalid("invalid induction overflow operation"))?;
                    pure(&args[1], locals, depth + 1, variants, false)?;
                    pure(&args[2], locals, depth + 1, variants, false)
                }
                _ => Err(Error::unsupported(format!("#{head} is not a supported pure induction expression"))),
            }
        }
        _ => Err(Error::unsupported("induction expressions require pure local values; blocks, calls, bindings and global initializers are unsupported")),
    }
}

impl Engine<'_, '_> {
    pub(super) fn loop_predicate(
        &mut self,
        mut state: State,
        predicate: &Expr,
        assume: bool,
    ) -> Result<Vec<(State, Value)>> {
        if assume {
            let mut pending = vec![predicate];
            while let Some(expr) = pending.pop() {
                self.tick()?;
                if matches!(form(expr), Some(("proof-validated", _))) {
                    // Explicit evidence invariants replace implicit prefix
                    // facts at an abstract head. Only queried requirements are
                    // retained. Their positive polarity makes omission safe.
                    state.validations.clear();
                    break;
                }
                if let Expr::List(items) = expr {
                    pending.extend(items.iter());
                }
            }
        }
        let previous = self.validation_mode;
        self.validation_mode = if assume {
            ValidationMode::Assume
        } else {
            ValidationMode::Check
        };
        let result = self.proposition(state, predicate);
        self.validation_mode = previous;
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn input_alias_provenance_preserves_exclusivity_and_shared_ancestry() {
        let program = crate::parse_program(
            "(#struct Holder () (: loan (#ref-mut #u8))) (#fn entry () () (#return ()))",
        )
        .unwrap();
        let checked = CheckedProgram::validate(&program).unwrap();
        let graph = Graph::new(checked.program(), checked.declarations());
        let mut engine = Engine::new(&checked, &graph, Span::new(0, 0, 1, 1));
        let mut state = State::new();
        let reference = |target, mutable| Type::Reference {
            mutable,
            target: Box::new(target),
        };
        let shared = engine
            .fresh_value(&mut state, &reference(Type::U8, false), 0)
            .unwrap();
        let unique = engine
            .fresh_value(&mut state, &reference(Type::U8, true), 0)
            .unwrap();
        let holder = engine
            .fresh_value(
                &mut state,
                &reference(Type::Named("Holder".into()), false),
                0,
            )
            .unwrap();
        let Value::Ref { place: shared, .. } = shared else {
            panic!("shared")
        };
        let Value::Ref { place: unique, .. } = unique else {
            panic!("unique")
        };
        let Value::Ref { place: holder, .. } = holder else {
            panic!("holder")
        };
        let Value::Record(_, fields) = engine.read(&state, &holder).unwrap() else {
            panic!("record")
        };
        let Value::Ref { place: nested, .. } = &fields[0].1 else {
            panic!("nested")
        };
        let aliases = state.possibly_aliasing_roots(shared.root);
        assert!(aliases.contains(&holder.root));
        assert!(aliases.contains(&nested.root));
        assert!(!aliases.contains(&unique.root));
        let local = engine
            .allocate(
                &mut state,
                Value::Bits(Circuit::constant(0, 8, false), Type::U8),
            )
            .unwrap();
        assert!(!state
            .possibly_aliasing_roots(shared.root)
            .contains(&local.root));
        state.globals.insert("global".into(), local.clone());
        assert!(state
            .possibly_aliasing_roots(shared.root)
            .contains(&local.root));
        assert!(state
            .possibly_aliasing_roots(local.root)
            .contains(&shared.root));
        assert!(!engine.fresh_under_shared);
        let bad = reference(Type::Named("Missing".into()), false);
        assert!(engine.fresh_value(&mut state, &bad, 0).is_err());
        assert!(!engine.fresh_under_shared);
    }

    #[test]
    fn assumed_evidence_queries_are_consistent_under_symbolic_aliases() {
        let program = crate::parse_program(
            "(#fn validate (: item (#ref #u8)) #bool (#return true))\n\
             (#fn perform (: item (#ref #u8)) () (#return ()))",
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
        engine.validation_mode = ValidationMode::Assume;
        let mut state = State::new();
        state.frames.push(Frame {
            function: "perform".into(),
            locals: BTreeMap::new(),
        });
        let backing = engine
            .allocate(
                &mut state,
                Value::Array(
                    Type::U8,
                    vec![Value::Bits(Circuit::constant(0, 8, false), Type::U8); 2],
                ),
            )
            .unwrap();
        let mut indices = Vec::new();
        for name in ["first", "second"] {
            let mut index = Circuit::constant(0, 64, false);
            index.bits[0] = engine.circuit.fresh();
            indices.push(index.clone());
            let mut place = backing.clone();
            place.path.push(Segment::Index(index));
            engine
                .bind(
                    &mut state,
                    name.into(),
                    Type::Reference {
                        mutable: false,
                        target: Box::new(Type::U8),
                    },
                    Value::Ref {
                        place,
                        target: Type::U8,
                        mutable: false,
                        pinned: false,
                    },
                )
                .unwrap();
        }
        let descriptor = Expr::List(
            vec![
                Expr::Symbol("#parameter-of".into()),
                Expr::Symbol("validate".into()),
                Expr::Symbol("item".into()),
            ]
            .into(),
        );
        let first = [descriptor.clone(), Expr::Symbol("first".into())];
        let second = [descriptor, Expr::Symbol("second".into())];
        let (state, a) = engine
            .validation_query(state, &first)
            .unwrap()
            .pop()
            .unwrap();
        let (state, b) = engine
            .validation_query(state, &second)
            .unwrap()
            .pop()
            .unwrap();
        let (_, again) = engine
            .validation_query(state, &first)
            .unwrap()
            .pop()
            .unwrap();
        let changed = engine
            .circuit
            .xor(a.boolean().unwrap(), again.boolean().unwrap());
        assert!(engine.circuit.satisfy(changed).unwrap().is_none());
        let same = engine.circuit.eq_word(&indices[0], &indices[1]);
        let difference = engine
            .circuit
            .xor(a.boolean().unwrap(), b.boolean().unwrap());
        let inconsistent_alias = engine.circuit.and(same, difference);
        assert!(engine
            .circuit
            .satisfy(inconsistent_alias)
            .unwrap()
            .is_none());
        let independent = engine.circuit.and(same ^ 1, difference);
        assert!(engine.circuit.satisfy(independent).unwrap().is_some());
    }

    #[test]
    fn failed_loop_predicate_restores_validation_query_scope() {
        let program = crate::parse_program("(#fn entry () () (#return ()))").unwrap();
        let checked = CheckedProgram::validate(&program).unwrap();
        let graph = Graph::new(checked.program(), checked.declarations());
        let mut engine = Engine::new(&checked, &graph, Span::new(0, 0, 1, 1));
        let expr = Expr::List(vec![Expr::Symbol("#proof-validated".into())].into());
        assert!(engine.loop_predicate(State::new(), &expr, true).is_err());
        assert!(matches!(engine.validation_mode, ValidationMode::None));
    }
}

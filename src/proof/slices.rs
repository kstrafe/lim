//! Slice views retain their array location, rather than copying its contents.
//! Every derived view proves 0 <= start <= end <= length under its path guard.
use super::*;

impl Engine<'_, '_> {
    fn array_view(&mut self, state: &State, place: Location, mutable: bool) -> Result<Slice> {
        let Value::Array(element, values) = self.read(state, &place)? else {
            return Err("a symbolic slice requires an array reference or array place".into());
        };
        if values.len() > 64 {
            return Err(Error::limit(
                "symbolic slice backing arrays are limited to 64 elements",
            ));
        }
        Ok(Slice {
            place,
            element,
            start: Circuit::constant(0, 64, false),
            len: Circuit::constant(values.len() as u128, 64, false),
            mutable,
        })
    }

    fn slice_value(value: Value, mutable: bool) -> Result<Slice> {
        match value {
            Value::Slice(view) if view.mutable == mutable => Ok(view),
            _ => Err("a slice operation requires a matching immutable or mutable slice".into()),
        }
    }

    fn slice_range(
        &mut self,
        state: State,
        view: &Slice,
        start: &Expr,
        end: &Expr,
        spec: bool,
    ) -> Result<Vec<(State, Value)>> {
        let mut output = Vec::new();
        for (state, start) in self.expr_as(state, start, spec, &Type::Usize)? {
            let start = self.word_of(&start, &Type::Usize)?;
            for (state, end) in self.expr_as(state, end, spec, &Type::Usize)? {
                let end = self.word_of(&end, &Type::Usize)?;
                let reversed = self.circuit.lt_word(&end, &start);
                let beyond = self.circuit.lt_word(&view.len, &end);
                let invalid = self.circuit.or(reversed, beyond);
                let bad = self.circuit.and(state.guard, invalid);
                self.require_unsat(bad, "a slice range can be out of bounds or reversed")?;
                let len = self.circuit.binary("sub", Some("wrap"), &end, &start)?.0;
                let start = self
                    .circuit
                    .binary("add", Some("wrap"), &view.start, &start)?
                    .0;
                output.push((
                    state,
                    Value::Slice(Slice {
                        start,
                        len,
                        ..view.clone()
                    }),
                ));
            }
        }
        self.limit_paths(output.len())?;
        Ok(output)
    }

    pub(super) fn slice_expr(
        &mut self,
        state: State,
        head: &str,
        args: &[Expr],
        spec: bool,
    ) -> Result<Vec<(State, Value)>> {
        let mutable = matches!(
            head,
            "borrow-slice-mut"
                | "slice-mut-of"
                | "slice-mut-range"
                | "slice-mut-len"
                | "slice-mut-idx"
                | "slice-mut-split"
        );
        match head {
            "borrow-slice" | "borrow-slice-mut" => {
                if !matches!(args.len(), 1 | 3) {
                    return Err(format!(
                        "#{head} requires an array place and optional start/end bounds"
                    )
                    .into());
                }
                if spec && mutable {
                    return Err("mutable borrowing is not a specification operation".into());
                }
                let mut output = Vec::new();
                for (state, place) in self.place(state, &args[0], spec)? {
                    let view = self.array_view(&state, place, mutable)?;
                    if args.len() == 3 {
                        output.extend(self.slice_range(state, &view, &args[1], &args[2], spec)?);
                    } else {
                        output.push((state, Value::Slice(view)));
                    }
                }
                self.limit_paths(output.len())?;
                Ok(output)
            }
            "slice-of" | "slice-mut-of" => {
                arity(head, args, 1)?;
                let mut output = Vec::new();
                for (state, reference) in self.expr(state, &args[0], spec)? {
                    let Value::Ref {
                        place,
                        mutable: actual,
                        pinned: false,
                        ..
                    } = reference
                    else {
                        return Err(
                            "slice construction requires an ordinary array reference".into()
                        );
                    };
                    if actual != mutable {
                        return Err(
                            "slice construction requires matching reference mutability".into()
                        );
                    }
                    let view = self.array_view(&state, place, mutable)?;
                    output.push((state, Value::Slice(view)));
                }
                Ok(output)
            }
            "slice-len" | "slice-mut-len" => {
                arity(head, args, 1)?;
                self.expr(state, &args[0], spec)?
                    .into_iter()
                    .map(|(state, value)| {
                        let view = Self::slice_value(value, mutable)?;
                        Ok((state, Value::Bits(view.len, Type::Usize)))
                    })
                    .collect()
            }
            "slice-range" | "slice-mut-range" => {
                arity(head, args, 3)?;
                let mut output = Vec::new();
                for (state, value) in self.expr(state, &args[0], spec)? {
                    let view = Self::slice_value(value, mutable)?;
                    output.extend(self.slice_range(state, &view, &args[1], &args[2], spec)?);
                }
                self.limit_paths(output.len())?;
                Ok(output)
            }
            "slice-idx" | "slice-mut-idx" => {
                arity(head, args, 2)?;
                let mut output = Vec::new();
                for (state, value) in self.expr(state, &args[0], spec)? {
                    let view = Self::slice_value(value, mutable)?;
                    for (state, index) in self.expr_as(state, &args[1], spec, &Type::Usize)? {
                        let index = self.word_of(&index, &Type::Usize)?;
                        let valid = self.circuit.lt_word(&index, &view.len);
                        let bad = self.circuit.and(state.guard, self.circuit.not(valid));
                        self.require_unsat(bad, "a slice index can be out of bounds")?;
                        if self.inductive_witness || self.handle_type(&view.element, 0)? {
                            // Different stored references cannot be represented
                            // as numeric muxes. Keep each feasible element's
                            // actual location in a separate guarded execution.
                            // Induction also benefits from concrete addresses
                            // when relating earlier writes to processed cells.
                            let Value::Array(_, values) = self.read(&state, &view.place)? else {
                                return Err(Error::checker("slice lost its array backing"));
                            };
                            if values.len() > 64 {
                                return Err(Error::limit(
                                    "symbolic slice backing arrays are limited to 64 elements",
                                ));
                            }
                            self.bounds(&state, &view.start, values.len() + 1)?;
                            let mut addresses = vec![FALSE; values.len()];
                            for start in 0..=values.len() {
                                let mut pinned = state.clone();
                                let constant = Circuit::constant(start as u128, 64, false);
                                let selected_start = self.circuit.eq_word(&view.start, &constant);
                                pinned.guard = self.circuit.and(pinned.guard, selected_start);
                                pinned.guard = self.circuit.and(pinned.guard, valid);
                                if self.circuit.satisfy(pinned.guard)?.is_none() {
                                    continue;
                                }
                                let fixed = Slice {
                                    start: constant,
                                    ..view.clone()
                                };
                                self.slice_backing_values(&pinned, &fixed, TRUE)?;
                                let capacity =
                                    Circuit::constant((values.len() - start) as u128, 64, false);
                                let too_long = self.circuit.lt_word(&capacity, &view.len);
                                // Retain the geometry fact just checked above.
                                pinned.guard =
                                    self.circuit.and(pinned.guard, self.circuit.not(too_long));
                                self.bounds(&pinned, &index, values.len() - start)?;
                                for (offset, guard) in addresses.iter_mut().enumerate().skip(start)
                                {
                                    let relative =
                                        Circuit::constant((offset - start) as u128, 64, false);
                                    let selected = self.circuit.eq_word(&index, &relative);
                                    let guard_here = self.circuit.and(pinned.guard, selected);
                                    *guard = self.circuit.or(*guard, guard_here);
                                }
                            }
                            for (offset, guard) in addresses.into_iter().enumerate() {
                                let mut branch = state.clone();
                                branch.guard = guard;
                                if self.circuit.satisfy(branch.guard)?.is_none() {
                                    continue;
                                }
                                let mut place = view.place.clone();
                                place.path.push(Segment::Index(Circuit::constant(
                                    offset as u128,
                                    64,
                                    false,
                                )));
                                output.push((
                                    branch,
                                    Value::Ref {
                                        place,
                                        target: view.element.clone(),
                                        mutable,
                                        pinned: false,
                                    },
                                ));
                            }
                            self.limit_paths(output.len())?;
                            continue;
                        }
                        let index = self
                            .circuit
                            .binary("add", Some("wrap"), &view.start, &index)?
                            .0;
                        let mut place = view.place.clone();
                        place.path.push(Segment::Index(index));
                        output.push((
                            state,
                            Value::Ref {
                                place,
                                target: view.element.clone(),
                                mutable,
                                pinned: false,
                            },
                        ));
                    }
                }
                self.limit_paths(output.len())?;
                Ok(output)
            }
            "slice-mut-split" => {
                arity(head, args, 2)?;
                let mut output = Vec::new();
                for (state, value) in self.expr(state, &args[0], spec)? {
                    let view = Self::slice_value(value, true)?;
                    for (state, at) in self.expr_as(state, &args[1], spec, &Type::Usize)? {
                        let at = self.word_of(&at, &Type::Usize)?;
                        let beyond = self.circuit.lt_word(&view.len, &at);
                        let bad = self.circuit.and(state.guard, beyond);
                        self.require_unsat(bad, "a slice split can be out of bounds")?;
                        let right_start = self
                            .circuit
                            .binary("add", Some("wrap"), &view.start, &at)?
                            .0;
                        let right_len = self.circuit.binary("sub", Some("wrap"), &view.len, &at)?.0;
                        output.push((
                            state,
                            Value::Tuple(vec![
                                Value::Slice(Slice {
                                    len: at,
                                    ..view.clone()
                                }),
                                Value::Slice(Slice {
                                    start: right_start,
                                    len: right_len,
                                    ..view.clone()
                                }),
                            ]),
                        ));
                    }
                }
                self.limit_paths(output.len())?;
                Ok(output)
            }
            _ => Err(Error::unsupported(format!(
                "unsupported slice operation #{head}"
            ))),
        }
    }
}

//! Recover explicit source expressions for normalized, guarded universe levels.
use super::*;

impl Level {
    pub(in crate::proof::kernel) fn source(
        &self,
        names: &HashMap<String, String>,
    ) -> Result<String> {
        let variable = |name: &String| {
            names.get(name).cloned().ok_or_else(|| {
                "source translation encountered an unbound universe parameter".to_owned()
            })
        };
        let mut expressions = Vec::new();
        let mut meaning = Self::number(0)?;
        let mut bytes = 0usize;
        let mut comparisons = 0usize;
        for (monomial, offset) in &self.terms {
            let (mut expression, mut part) = if let Some(base) = &monomial.base {
                if *offset > 64 || monomial.nonzero.len() + *offset as usize > 80 {
                    return Err("universe source expression depth limit exceeded".into());
                }
                let mut expression = variable(base)?;
                for _ in 0..*offset {
                    expression = format!("(#pt-level-succ {expression})");
                }
                (expression, Self::variable(base.clone()).offset(*offset)?)
            } else {
                (offset.to_string(), Self::number(*offset)?)
            };
            // Choose outer guards first. Every extra right-hand contribution
            // from imax must be dominated by the complete level under the
            // guards already chosen outside it. Arbitrary lexical guard order
            // can change the level's meaning when an outer guard is zero.
            let mut pending = monomial.nonzero.clone();
            let mut outside: Vec<String> = Vec::new();
            while !pending.is_empty() {
                let mut selected = None;
                for condition in &pending {
                    comparisons += 1;
                    if comparisons > 4096 {
                        return Err("universe source reconstruction work limit exceeded".into());
                    }
                    let mut contribution = Self::variable(condition.clone());
                    for outer in &outside {
                        contribution = contribution.gated(&Self::variable(outer.clone()))?;
                    }
                    if contribution.at_most(self)? {
                        selected = Some(condition.clone());
                        break;
                    }
                }
                let selected =
                    selected.ok_or("normalized universe has no verified source reconstruction")?;
                pending.remove(&selected);
                outside.push(selected);
            }
            for condition in outside.iter().rev() {
                expression = format!("(#pt-level-imax {expression} {})", variable(condition)?);
                part = part.imax(&Self::variable(condition.clone()))?;
            }
            bytes = bytes.saturating_add(expression.len());
            if bytes > 64 * 1024 {
                return Err("universe source expression byte limit exceeded".into());
            }
            expressions.push(expression);
            meaning = meaning.maximum(&part)?;
        }
        // imax also contributes its right-hand level. Verify that these extra
        // contributions are already implied by the complete normalized level;
        // a failed reconstruction must never silently change a declaration.
        if !self.equivalent(&meaning)? {
            return Err("normalized universe has no verified source reconstruction".into());
        }
        Ok(match expressions.len() {
            0 => "0".into(),
            1 => expressions.pop().unwrap(),
            _ => format!("(#pt-level-max {})", expressions.join(" ")),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn normalized_guarded_levels_round_trip_through_native_syntax() {
        let u = Level::variable("original-u".into());
        let v = Level::variable("original-v".into());
        let names = HashMap::from([
            ("original-u".into(), "u".into()),
            ("original-v".into(), "v".into()),
        ]);
        for (level, original) in [
            (Level::number(0).unwrap(), "0"),
            (Level::number(47).unwrap(), "47"),
            (u.clone(), "u"),
            (u.successor().unwrap(), "(#pt-level-succ u)"),
            (u.imax(&v).unwrap(), "(#pt-level-imax u v)"),
            (
                Level::number(3)
                    .unwrap()
                    .imax(&u.imax(&v).unwrap())
                    .unwrap(),
                "(#pt-level-imax 3 (#pt-level-imax u v))",
            ),
            (
                u.successor().unwrap().imax(&v).unwrap().imax(&u).unwrap(),
                "(#pt-level-imax (#pt-level-imax (#pt-level-succ u) v) u)",
            ),
            (
                u.imax(&v).unwrap().maximum(&v.imax(&u).unwrap()).unwrap(),
                "(#pt-level-max (#pt-level-imax u v) (#pt-level-imax v u))",
            ),
        ] {
            let rendered = level
                .source(&names)
                .unwrap_or_else(|why| panic!("{original}: {why}"));
            let source = format!("(#math-definition level-round-trip (u v) (#pt-sort (#pt-level-succ {original})) (#pt-sort {rendered}))");
            let program = crate::parse_program(&source).unwrap();
            crate::check_types(&program).unwrap_or_else(|why| panic!("{why}\n{source}"));
        }
    }

    #[test]
    fn reconstructed_levels_must_have_exact_meaning_and_bounded_source() {
        let names = HashMap::from([("u".into(), "u".into())]);
        let guarded_constant = Level {
            terms: BTreeMap::from([(
                Monomial {
                    base: None,
                    nonzero: BTreeSet::from(["u".into()]),
                },
                2,
            )]),
        };
        assert!(guarded_constant
            .source(&names)
            .unwrap_err()
            .contains("verified source reconstruction"));
        assert!(Level::variable("u".into())
            .offset(65)
            .unwrap()
            .source(&names)
            .unwrap_err()
            .contains("depth limit"));
        assert!(Level::variable("missing".into())
            .source(&names)
            .unwrap_err()
            .contains("unbound universe"));
    }
}

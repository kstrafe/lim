//! Verify parsed translations against the already checked export environment.
//! This is independent of the text writer and does not trust source comments.
use super::*;
use crate::proof::kernel::{parse_declaration, Body};

/// Internal constant templates use the same bounded relocation as checked
/// source correspondence. The source text and alias inventory are compiler-owned.
pub(in crate::proof::kernel::core::export) fn relocate_template(
    value: &T,
    names: &HashMap<String, String>,
    levels: &HashMap<String, Level>,
) -> Result<T> {
    let mut remaining = SOURCE_NODES;
    let mut remaining_bytes = 64 * 1024 * 1024;
    Relocate {
        names,
        levels,
        remaining: &mut remaining,
        remaining_bytes: &mut remaining_bytes,
        memo: HashMap::new(),
    }
    .term(value, 0)
}

pub(super) fn check(
    replay: &mut Replay,
    report: &LeanExportReport,
    names: &HashMap<String, String>,
    program: &crate::Program,
) -> Result<()> {
    let reverse = names
        .iter()
        .map(|(old, new)| (new.clone(), old.clone()))
        .collect::<HashMap<_, _>>();
    let records = report
        .declarations
        .iter()
        .map(|record| (record.identity.as_str(), record))
        .collect::<HashMap<_, _>>();
    let mut remaining = SOURCE_NODES;
    let mut remaining_bytes = 64 * 1024 * 1024usize;
    let mut seen = HashSet::new();
    if program.items.len() != report.declarations.len() {
        return Err("native declaration inventory differs from the checked export".into());
    }
    for item in &program.items {
        let crate::Item::Proof { name, proposition } = item else {
            return Err("nonmathematical declaration in a proof-source translation".into());
        };
        let original = reverse
            .get(name)
            .ok_or("unknown native declaration in translation")?;
        if !seen.insert(original.clone()) {
            return Err("duplicate native declaration in translation".into());
        }
        let record = records
            .get(original.as_str())
            .ok_or("missing original declaration inventory")?;
        let declaration = replay
            .kernel
            .declarations
            .get(original)
            .ok_or("missing original checked declaration")?
            .clone();
        let parsed = parse_declaration(name, proposition, &HashSet::new())?;
        if parsed.universes.len() != declaration.universes.len() {
            return Err("translated universe parameter count differs from its source".into());
        }
        let levels = parsed
            .universes
            .iter()
            .cloned()
            .zip(declaration.universes.iter().cloned().map(Level::variable))
            .collect::<HashMap<_, _>>();
        let mut relocate = Relocate {
            names: &reverse,
            levels: &levels,
            remaining: &mut remaining,
            remaining_bytes: &mut remaining_bytes,
            memo: HashMap::new(),
        };
        replay.kernel.reset_budget();
        let checked = (|| -> Result<()> {
            match (declaration.family.as_ref(), parsed.body) {
                (
                    None,
                    Body::Definition {
                        ty,
                        value,
                        theorem,
                        opaque,
                    },
                ) => {
                    if theorem != (record.kind == "theorem") || opaque != (record.kind == "opaque")
                    {
                        return Err(
                            "translated declaration kind or opacity differs from its source".into(),
                        );
                    }
                    let ty = relocate.term(&ty, 0)?;
                    equivalent(&mut replay.kernel, &[], &ty, &declaration.ty, true)?;
                    replay.kernel.reset_budget();
                    let value = relocate.term(&value, 0)?;
                    replay.kernel.check(&[], &value, &declaration.ty, 0)?;
                    let expected = declaration
                        .value
                        .as_ref()
                        .or_else(|| replay.bodies.get(original))
                        .ok_or("missing original checked initializer")?;
                    replay.kernel.reset_budget();
                    // Both values have already been checked at this exact type.
                    // Preserve identical syntax without recomputing its contents.
                    if !replay.kernel.same_syntax(&value, expected)?
                        && !replay.kernel.convertible(&[], &value, expected, 0)?
                    {
                        return Err("translated initializer differs from its checked source".into());
                    }
                }
                (
                    Some(family),
                    Body::Inductive {
                        members,
                        parameters,
                        indices,
                        sort,
                        constructors,
                        indexed_constructors,
                    },
                ) => {
                    if record.kind != "inductive" {
                        return Err("translated datatype kind differs".into());
                    }
                    let roots = family
                        .group
                        .iter()
                        .filter(|name| !replay.kernel.nested.contains_key(*name))
                        .cloned()
                        .collect::<Vec<_>>();
                    if members
                        .iter()
                        .map(|name| relocate.name(name))
                        .collect::<Result<Vec<_>>>()?
                        != roots
                    {
                        return Err("translated mutual membership differs from its source".into());
                    }
                    if !sort.substitute(&levels)?.equivalent(&family.sort)? {
                        return Err("translated inductive sort differs from its source".into());
                    }
                    let mut ctx = Vec::new();
                    telescope(
                        &mut replay.kernel,
                        &mut relocate,
                        &mut ctx,
                        &parameters,
                        &family.parameters,
                    )?;
                    let parameters_ctx = ctx.clone();
                    telescope(
                        &mut replay.kernel,
                        &mut relocate,
                        &mut ctx,
                        &indices,
                        &family.indices,
                    )?;
                    let constructors = if indices.is_empty() {
                        constructors
                            .into_iter()
                            .map(|(name, fields)| (name, fields, vec![]))
                            .collect::<Vec<_>>()
                    } else {
                        indexed_constructors
                    };
                    if constructors.len() != family.constructors.len() {
                        return Err("translated constructor count differs from its source".into());
                    }
                    for ((name, fields, indices), expected) in
                        constructors.iter().zip(&family.constructors)
                    {
                        if relocate.name(name)? != expected.name {
                            return Err("translated constructor identity differs".into());
                        }
                        let mut ctx = parameters_ctx.clone();
                        telescope(
                            &mut replay.kernel,
                            &mut relocate,
                            &mut ctx,
                            fields,
                            &expected.fields,
                        )?;
                        if indices.len() != expected.result_indices.len() {
                            return Err("translated constructor index count differs".into());
                        }
                        for (actual, expected) in indices.iter().zip(&expected.result_indices) {
                            equivalent(
                                &mut replay.kernel,
                                &ctx,
                                &relocate.term(actual, 0)?,
                                expected,
                                false,
                            )?;
                        }
                    }
                }
                _ => return Err("translated declaration shape differs from its source".into()),
            }
            Ok(())
        })();
        checked.map_err(|why| {
            format!(
                "declaration '{}' ({} checking steps): {why}",
                record.name, replay.kernel.work
            )
        })?;
    }
    Ok(())
}

fn telescope(
    kernel: &mut Kernel,
    relocate: &mut Relocate<'_>,
    ctx: &mut Vec<T>,
    actual: &[T],
    expected: &[T],
) -> Result<()> {
    if actual.len() != expected.len() {
        return Err("translated telescope count differs from its source".into());
    }
    for (actual, expected) in actual.iter().zip(expected) {
        equivalent(kernel, ctx, &relocate.term(actual, 0)?, expected, true)?;
        ctx.push(expected.clone());
    }
    Ok(())
}

fn equivalent(
    kernel: &mut Kernel,
    ctx: &[T],
    actual: &T,
    expected: &T,
    is_type: bool,
) -> Result<()> {
    if is_type {
        kernel.sort(ctx, actual, 0)?;
    } else {
        let ty = kernel.infer(ctx, expected, 0)?;
        kernel.check(ctx, actual, &ty, 0)?;
    }
    if kernel.same_syntax(actual, expected)? || kernel.convertible(ctx, actual, expected, 0)? {
        Ok(())
    } else {
        Err("translated term is not definitionally equal to its checked source".into())
    }
}

struct Relocate<'a> {
    names: &'a HashMap<String, String>,
    levels: &'a HashMap<String, Level>,
    remaining: &'a mut usize,
    remaining_bytes: &'a mut usize,
    memo: HashMap<usize, T>,
}
impl Relocate<'_> {
    fn name(&self, name: &str) -> Result<String> {
        if matches!(name, "#pt-nat" | "#pt-false") {
            return Ok(name.into());
        }
        self.names
            .get(name)
            .cloned()
            .ok_or("unmapped native constant during correspondence checking".into())
    }
    fn term(&mut self, value: &T, depth: usize) -> Result<T> {
        if depth > 256 {
            return Err("source correspondence depth limit exceeded".into());
        }
        let key = Arc::as_ptr(value) as usize;
        if let Some(value) = self.memo.get(&key) {
            return Ok(value.clone());
        }
        *self.remaining = self
            .remaining
            .checked_sub(1)
            .ok_or("source correspondence node limit exceeded")?;
        macro_rules! walk {
            ($value:expr) => {
                self.term($value, depth + 1)?
            };
        }
        macro_rules! many {
            ($values:expr) => {
                $values
                    .iter()
                    .map(|value| self.term(value, depth + 1))
                    .collect::<Result<Vec<_>>>()?
            };
        }
        macro_rules! levels {
            ($values:expr) => {
                $values
                    .iter()
                    .map(|value| value.substitute(self.levels))
                    .collect::<Result<Vec<_>>>()?
            };
        }
        let result = term(match value.as_ref() {
            Term::QuotType(l, a, r) => {
                Term::QuotType(l.substitute(self.levels)?, walk!(a), walk!(r))
            }
            Term::QuotMake(l, a, r, x) => {
                Term::QuotMake(l.substitute(self.levels)?, walk!(a), walk!(r), walk!(x))
            }
            Term::QuotLift {
                source_level,
                target_level,
                ty,
                relation,
                target,
                function,
                respect,
                subject,
            } => Term::QuotLift {
                source_level: source_level.substitute(self.levels)?,
                target_level: target_level.substitute(self.levels)?,
                ty: walk!(ty),
                relation: walk!(relation),
                target: walk!(target),
                function: walk!(function),
                respect: walk!(respect),
                subject: walk!(subject),
            },
            Term::QuotInduct {
                level,
                ty,
                relation,
                motive,
                branch,
                subject,
            } => Term::QuotInduct {
                level: level.substitute(self.levels)?,
                ty: walk!(ty),
                relation: walk!(relation),
                motive: walk!(motive),
                branch: walk!(branch),
                subject: walk!(subject),
            },
            Term::Sort(level) => Term::Sort(level.substitute(self.levels)?),
            Term::Var(index) => Term::Var(*index),
            Term::Global(name, levels) => Term::Global(self.name(name)?, levels!(levels)),
            Term::Pi(a, b) => Term::Pi(walk!(a), walk!(b)),
            Term::Lam(a, b) => Term::Lam(walk!(a), walk!(b)),
            Term::Sigma(a, b) => Term::Sigma(walk!(a), walk!(b)),
            Term::App(a, b) => Term::App(walk!(a), walk!(b)),
            Term::Let(a, b, c) => Term::Let(walk!(a), walk!(b), walk!(c)),
            Term::Pair(a, b, c) => Term::Pair(walk!(a), walk!(b), walk!(c)),
            Term::Eq(a, b, c) => Term::Eq(walk!(a), walk!(b), walk!(c)),
            Term::Refl(a, b) => Term::Refl(walk!(a), walk!(b)),
            Term::First(a) => Term::First(walk!(a)),
            Term::Second(a) => Term::Second(walk!(a)),
            Term::Project {
                family,
                index,
                subject,
            } => Term::Project {
                family: self.name(family)?,
                index: *index,
                subject: walk!(subject),
            },
            Term::EqElim {
                ty,
                left,
                motive,
                base,
                right,
                proof,
            } => Term::EqElim {
                ty: walk!(ty),
                left: walk!(left),
                motive: walk!(motive),
                base: walk!(base),
                right: walk!(right),
                proof: walk!(proof),
            },
            Term::Ctor {
                family,
                levels,
                parameters,
                constructor,
                fields,
            } => Term::Ctor {
                family: self.name(family)?,
                levels: levels!(levels),
                parameters: many!(parameters),
                constructor: if matches!(family.as_str(), "#pt-nat" | "#pt-false") {
                    constructor.clone()
                } else {
                    self.name(constructor)?
                },
                fields: many!(fields),
            },
            Term::Induct {
                family,
                levels,
                parameters,
                indices,
                motive,
                branches,
                subject,
            } => Term::Induct {
                family: self.name(family)?,
                levels: levels!(levels),
                parameters: many!(parameters),
                indices: many!(indices),
                motive: walk!(motive),
                branches: many!(branches),
                subject: walk!(subject),
            },
            Term::MutualInduct {
                family,
                levels,
                parameters,
                indices,
                cases,
                subject,
            } => Term::MutualInduct {
                family: self.name(family)?,
                levels: levels!(levels),
                parameters: many!(parameters),
                indices: many!(indices),
                cases: cases
                    .iter()
                    .map(|case| {
                        Ok(RecursionCase {
                            family: self.name(&case.family)?,
                            motive: self.term(&case.motive, depth + 1)?,
                            branches: case
                                .branches
                                .iter()
                                .map(|value| self.term(value, depth + 1))
                                .collect::<Result<Vec<_>>>()?,
                        })
                    })
                    .collect::<Result<Vec<_>>>()?,
                subject: walk!(subject),
            },
            Term::NestedInduct {
                family,
                levels,
                parameters,
                selected,
                indices,
                cases,
                subject,
            } => Term::NestedInduct {
                family: self.name(family)?,
                levels: levels!(levels),
                parameters: many!(parameters),
                selected: *selected,
                indices: many!(indices),
                cases: cases
                    .iter()
                    .map(|case| {
                        Ok(NestedCase {
                            selector: self.term(&case.selector, depth + 1)?,
                            motive: self.term(&case.motive, depth + 1)?,
                            branches: case
                                .branches
                                .iter()
                                .map(|value| self.term(value, depth + 1))
                                .collect::<Result<Vec<_>>>()?,
                        })
                    })
                    .collect::<Result<Vec<_>>>()?,
                subject: walk!(subject),
            },
            Term::SelfType | Term::SelfAt(_) | Term::Recur(..) => {
                return Err("unexpected recursive marker in translated source".into())
            }
        });
        let level_bytes = match result.as_ref() {
            Term::Sort(level) => level.memory_weight(),
            Term::QuotType(level, ..)
            | Term::QuotMake(level, ..)
            | Term::QuotInduct { level, .. } => level.memory_weight(),
            Term::QuotLift {
                source_level,
                target_level,
                ..
            } => source_level
                .memory_weight()
                .saturating_add(target_level.memory_weight()),
            Term::Global(_, levels)
            | Term::Ctor { levels, .. }
            | Term::Induct { levels, .. }
            | Term::MutualInduct { levels, .. }
            | Term::NestedInduct { levels, .. } => levels.iter().fold(0usize, |total, level| {
                total.saturating_add(level.memory_weight())
            }),
            _ => 0,
        };
        let name_bytes = match result.as_ref() {
            Term::Global(name, _) => name.len(),
            Term::Ctor {
                family,
                constructor,
                ..
            } => family.len().saturating_add(constructor.len()),
            Term::MutualInduct { family, cases, .. } => {
                cases.iter().fold(family.len(), |total, case| {
                    total.saturating_add(case.family.len())
                })
            }
            Term::Induct { family, .. }
            | Term::NestedInduct { family, .. }
            | Term::Project { family, .. } => family.len(),
            _ => 0,
        };
        *self.remaining_bytes = self
            .remaining_bytes
            .checked_sub(
                128usize
                    .saturating_add(level_bytes)
                    .saturating_add(name_bytes),
            )
            .ok_or("source correspondence allocation limit exceeded")?;
        self.memo.insert(key, result.clone());
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn report(name: &str, kind: &str) -> LeanExportReport {
        LeanExportReport {
            target: name.into(),
            input_sha256: String::new(),
            bytes: 0,
            records: 0,
            foundations: vec![],
            declarations: vec![LeanDeclarationReport {
                name: name.into(),
                identity: name.into(),
                kind: kind.into(),
                line: 0,
                sha256: String::new(),
                dependencies: vec![],
            }],
        }
    }
    fn nat() -> T {
        term(Term::Global("#pt-nat".into(), vec![]))
    }
    fn zero() -> T {
        term(Term::Ctor {
            family: "#pt-nat".into(),
            levels: vec![],
            parameters: vec![],
            constructor: "zero".into(),
            fields: vec![],
        })
    }
    fn verify(replay: &mut Replay, kind: &str, source: &str) -> Result<()> {
        let program = crate::parse_program(source).unwrap();
        crate::check_types(&program).unwrap();
        check(
            replay,
            &report("original", kind),
            &HashMap::from([("original".into(), "native".into())]),
            &program,
        )
    }
    #[test]
    fn a_well_typed_different_data_initializer_is_not_the_original_definition() {
        let mut replay = Replay::new();
        replay
            .kernel
            .definition("original", vec![], nat(), zero(), false)
            .unwrap();
        verify(
            &mut replay,
            "definition",
            "(#math-definition native () #pt-nat #pt-zero)",
        )
        .unwrap();
        let error = verify(
            &mut replay,
            "definition",
            "(#math-definition native () #pt-nat (#pt-succ #pt-zero))",
        )
        .unwrap_err();
        assert!(error.contains("initializer differs"), "{error}");
    }
    #[test]
    fn a_proved_different_statement_is_not_the_original_theorem() {
        let mut replay = Replay::new();
        let proposition = term(Term::Sort(Level::number(0).unwrap()));
        let ty = term(Term::Pi(
            proposition.clone(),
            term(Term::Pi(term(Term::Var(0)), term(Term::Var(1)))),
        ));
        let proof = term(Term::Lam(
            proposition,
            term(Term::Lam(term(Term::Var(0)), term(Term::Var(0)))),
        ));
        replay
            .kernel
            .definition("original", vec![], ty, proof.clone(), true)
            .unwrap();
        replay.bodies.insert("original".into(), proof);
        let error=verify(&mut replay,"theorem","(#theorem native (#universes) (#parameters) (#statement (#pt-eq #pt-nat #pt-zero #pt-zero)) (#proof (#pt-refl #pt-nat #pt-zero)))").unwrap_err();
        assert!(error.contains("not definitionally equal"), "{error}");
    }
    #[test]
    fn opacity_is_part_of_source_correspondence() {
        let mut replay = Replay::new();
        replay
            .kernel
            .opaque_definition("original", vec![], nat(), zero())
            .unwrap();
        replay.bodies.insert("original".into(), zero());
        verify(
            &mut replay,
            "opaque",
            "(#math-opaque native () #pt-nat #pt-zero)",
        )
        .unwrap();
        let error = verify(
            &mut replay,
            "opaque",
            "(#math-definition native () #pt-nat #pt-zero)",
        )
        .unwrap_err();
        assert!(error.contains("kind or opacity"), "{error}");
    }
    #[test]
    fn a_well_typed_changed_constructor_field_is_not_the_original_datatype() {
        let mut replay = Replay::new();
        replay
            .kernel
            .inductive(
                "original",
                vec![],
                vec![],
                Level::number(1).unwrap(),
                vec![("constructor".into(), vec![nat()])],
            )
            .unwrap();
        let names = HashMap::from([
            ("original".into(), "native".into()),
            ("constructor".into(), "make".into()),
        ]);
        for (source, accepted) in [
            (
                "(#math-inductive native () () (#pt-type 0) ((make ((field #pt-nat)))))",
                true,
            ),
            (
                "(#math-inductive native () () (#pt-type 0) ((make ((field #pt-prop)))))",
                false,
            ),
        ] {
            let program = crate::parse_program(source).unwrap();
            crate::check_types(&program).unwrap();
            let result = check(
                &mut replay,
                &report("original", "inductive"),
                &names,
                &program,
            );
            if accepted {
                result.unwrap();
            } else {
                assert!(result.unwrap_err().contains("not definitionally equal"));
            }
        }
    }
    #[test]
    fn relocation_limits_include_owned_identifier_payloads() {
        let original = "x".repeat(4096);
        let names = HashMap::from([("native".into(), original.clone())]);
        let levels = HashMap::new();
        let input = term(Term::Global("native".into(), vec![]));
        let mut nodes = 2;
        let mut bytes = 128;
        let error = Relocate {
            names: &names,
            levels: &levels,
            remaining: &mut nodes,
            remaining_bytes: &mut bytes,
            memo: HashMap::new(),
        }
        .term(&input, 0)
        .unwrap_err();
        assert!(error.contains("allocation limit"), "{error}");
        let mut nodes = 2;
        let mut bytes = 128 + original.len();
        let output = Relocate {
            names: &names,
            levels: &levels,
            remaining: &mut nodes,
            remaining_bytes: &mut bytes,
            memo: HashMap::new(),
        }
        .term(&input, 0)
        .unwrap();
        assert!(matches!(output.as_ref(),Term::Global(name,_) if name==&original));
        assert_eq!(bytes, 0);
        let mut nodes = 0;
        let mut bytes = 8192;
        assert!(Relocate {
            names: &names,
            levels: &levels,
            remaining: &mut nodes,
            remaining_bytes: &mut bytes,
            memo: HashMap::new()
        }
        .term(&input, 0)
        .unwrap_err()
        .contains("node limit"));
    }
}

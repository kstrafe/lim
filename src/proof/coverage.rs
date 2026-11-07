//! Vacuity is a coverage observation, not a change to universal logic. Collect
//! it across all evaluations of a source clause, then report only after every
//! theorem has passed. Inconclusive SAT queries still fail closed.
use super::*;

#[derive(Default)]
pub(super) struct Coverage {
    spans: HashMap<usize, Span>,
    samples: Vec<Sample>,
}

struct Sample {
    span: Span,
    function: String,
    entered: Bit,
    admitted: Bit,
}

/// Shared across all theorem engines: source-backed diagnostics otherwise
/// duplicate each source snapshot once per warning.
pub(super) struct ReportBudget {
    bytes: usize,
    reports: usize,
}

impl Default for ReportBudget {
    fn default() -> Self {
        Self {
            bytes: 16 * 1024 * 1024,
            reports: 1024,
        }
    }
}

impl ReportBudget {
    fn charge(&mut self, program: &crate::Program, span: Span, names: usize) -> Result<()> {
        let mut bytes = names.saturating_add(1024);
        let mut charge_source = |span: Span| {
            if let Some(file) = program.source_files.get(span.source_id as usize) {
                bytes = bytes
                    .saturating_add(file.source.len())
                    .saturating_add(file.path.as_os_str().len())
                    .saturating_add(256);
            }
        };
        charge_source(span);
        // Include every snapshot attached by analysis_diagnostic, even when
        // the same source is attached several times by distinct provenance.
        for (usage, definitions) in &program.syntax_bundle_uses {
            if usage.source_id == span.source_id
                && usage.start <= span.start
                && span.end <= usage.end
            {
                for definition in definitions {
                    charge_source(*definition);
                }
            }
        }
        let mut origin = span;
        let mut seen = BTreeSet::new();
        while let Some(invocation) = program.generated_source_invocations.get(&origin.source_id) {
            if !seen.insert(invocation.source_id) {
                break;
            }
            charge_source(*invocation);
            origin = *invocation;
        }
        if bytes > self.bytes || self.reports == 0 {
            return Err(Error::limit(
                "proof coverage reports exceed 1024 warnings or 16 MiB of diagnostic storage",
            ));
        }
        self.bytes -= bytes;
        self.reports -= 1;
        Ok(())
    }
}

impl Coverage {
    /// Pair checked syntax with preserved source children. Only equal-arity
    /// list nodes with the same builtin head are aligned; a changed shape
    /// falls back to the theorem span rather than guessing a source range.
    pub(super) fn locate(
        &mut self,
        proposition: &Expr,
        source: Option<&crate::SpannedExpr>,
    ) -> Result<()> {
        let Some(source) = source else {
            return Ok(());
        };
        let mut pending = vec![(proposition, source)];
        let mut visited = 0;
        while let Some((expr, source)) = pending.pop() {
            visited += 1;
            if visited > 100_000 {
                return Err(Error::limit(
                    "proof coverage source mapping exceeds 100000 nodes",
                ));
            }
            let (Some((head, args)), Some((source_head, source_args))) =
                (form(expr), form(&source.expr))
            else {
                continue;
            };
            if head != source_head
                || args.len() != source_args.len()
                || source.children.len() != args.len() + 1
            {
                continue;
            }
            if head == "proof-contract" && args.len() == 3 {
                self.spans
                    .insert(&args[1] as *const Expr as usize, source.children[2].span);
            }
            pending.extend(args.iter().zip(source.children.iter().skip(1)));
        }
        Ok(())
    }

    pub(super) fn record(
        &mut self,
        circuit: &mut Circuit,
        precondition: &Expr,
        function: &str,
        fallback: Span,
        entered: Bit,
        admitted: Bit,
    ) -> Result<()> {
        let span = self
            .spans
            .get(&(precondition as *const Expr as usize))
            .copied();
        if let Some(sample) = span.and_then(|span| {
            self.samples
                .iter_mut()
                .find(|sample| sample.span == span && sample.function == function)
        }) {
            sample.entered = circuit.or(sample.entered, entered);
            sample.admitted = circuit.or(sample.admitted, admitted);
            return Ok(());
        }
        if self.samples.len() >= 1024 {
            return Err(Error::limit("proof contract coverage exceeds 1024 clauses"));
        }
        self.samples.push(Sample {
            span: span.unwrap_or(fallback),
            function: function.into(),
            entered,
            admitted,
        });
        Ok(())
    }

    pub(super) fn diagnostics(
        self,
        circuit: &mut Circuit,
        program: &crate::Program,
        theorem: &str,
        budget: &mut ReportBudget,
    ) -> Result<Vec<crate::Diagnostic>> {
        let mut output = Vec::new();
        for sample in self.samples {
            if circuit
                .satisfy(sample.admitted)
                .map_err(|error| error.context("while checking contract input coverage"))?
                .is_some()
            {
                continue;
            }
            let reachable = circuit
                .satisfy(sample.entered)
                .map_err(|error| error.context("while checking contract reachability"))?
                .is_some();
            let reason = if reachable {
                "its precondition is unsatisfiable"
            } else {
                "its enclosing proof path is infeasible"
            };
            budget.charge(
                program,
                sample.span,
                theorem.len().saturating_add(sample.function.len()),
            )?;
            let mut diagnostic = crate::analysis_diagnostic(
                format!(
                    "theorem '{}': contract for '{}' covers no inputs: {reason}",
                    crate::file_access::local_name(theorem),
                    crate::file_access::local_name(&sample.function)
                ),
                crate::DiagnosticCode::ProofVacuous,
                Some(sample.span),
                Vec::new(),
                program,
            );
            diagnostic.severity = crate::DiagnosticSeverity::Warning;
            diagnostic.notes.push("The contract is logically true over this empty input set; it establishes no execution behavior.".into());
            output.push(diagnostic);
        }
        Ok(output)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn repeated_clause_evaluations_accumulate_feasible_inputs() {
        let program = crate::parse_program("(#fn run () () (#return ()))").unwrap();
        let span = Span::new(0, 0, 1, 1);
        let precondition = Expr::Symbol("true".into());
        let mut coverage = Coverage::default();
        coverage
            .spans
            .insert(&precondition as *const Expr as usize, span);
        let mut circuit = Circuit::new();
        coverage
            .record(&mut circuit, &precondition, "run", span, TRUE, FALSE)
            .unwrap();
        coverage
            .record(&mut circuit, &precondition, "run", span, TRUE, TRUE)
            .unwrap();
        assert_eq!(coverage.samples.len(), 1);
        assert!(coverage
            .diagnostics(
                &mut circuit,
                &program,
                "claim",
                &mut ReportBudget::default()
            )
            .unwrap()
            .is_empty());
    }

    #[test]
    fn a_poisoned_solver_cannot_issue_a_vacuity_warning() {
        let program = crate::parse_program("(#fn run () () (#return ()))").unwrap();
        let span = Span::new(0, 0, 1, 1);
        let precondition = Expr::Symbol("false".into());
        let mut coverage = Coverage::default();
        let mut circuit = Circuit::new();
        coverage
            .record(&mut circuit, &precondition, "run", span, TRUE, FALSE)
            .unwrap();
        circuit.word(0, false);
        let error = coverage
            .diagnostics(
                &mut circuit,
                &program,
                "claim",
                &mut ReportBudget::default(),
            )
            .unwrap_err();
        assert_eq!(
            error.diagnostic_code().proof_outcome(),
            Some(ProofOutcome::CheckerError)
        );
    }

    #[test]
    fn attached_sources_are_charged_before_constructing_diagnostics() {
        let mut program = crate::parse_program("(#fn run () () (#return ()))").unwrap();
        let file = crate::SourceFile {
            path: std::path::PathBuf::from("source.lim"),
            source: " ".repeat(32 * 1024),
            file_scope: None,
        };
        program.source_files = vec![file.clone(), file];
        let origin = Span::new(0, 1, 1, 1);
        let generated = Span {
            source_id: 1,
            ..origin
        };
        for from_generator in [false, true] {
            if from_generator {
                program.syntax_bundle_uses.clear();
                program.generated_source_invocations.insert(1, origin);
            } else {
                program
                    .syntax_bundle_uses
                    .insert(generated, vec![origin, origin]);
            }
            let mut budget = ReportBudget {
                bytes: 48 * 1024,
                reports: 10,
            };
            let error = budget.charge(&program, generated, 0).unwrap_err();
            assert_eq!(
                error.diagnostic_code().proof_outcome(),
                Some(ProofOutcome::ResourceLimit)
            );
            assert_eq!(budget.bytes, 48 * 1024);
            assert_eq!(budget.reports, 10);
        }
    }
}

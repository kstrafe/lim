//! Readable native source for checked export declarations. No trusted replay
//! directives or unchecked holes are emitted; the complete output is rechecked.
use super::*;
#[path = "export_correspondence.rs"]
pub(super) mod correspondence;
#[path = "export_native_names.rs"]
mod native_names;
use crate::proof::kernel::native_file::{Builder, Snapshot};
use native_names::Names as NativeNames;

const SOURCE_BYTES: usize = crate::proof::kernel::native_source::SOURCE_BYTES;
const SOURCE_NODES: usize = 1_000_000;

#[derive(Clone, Debug)]
pub struct LeanExportTranslation {
    pub report: LeanExportReport,
    pub target: String,
    pub source: String,
}

/// Checked native source with paged declaration-report metadata.
/// Source text remains owned; ready declarations are parsed individually.
pub struct LeanExportReceiptTranslation {
    pub receipt: LeanExportReceipt,
    pub target: String,
    pub source: String,
}
impl std::fmt::Debug for LeanExportReceiptTranslation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LeanExportReceiptTranslation")
            .field("declarations", &self.receipt.declaration_count())
            .field("target", &self.target)
            .field("source_bytes", &self.source.len())
            .finish_non_exhaustive()
    }
}

/// Fully checked native proof bytes in invocation-local protected storage.
/// Publication can stream these bytes without materializing the whole source.
pub struct LeanExportArtifactTranslation {
    pub receipt: LeanExportReceipt,
    pub target: String,
    source: Snapshot,
}
impl LeanExportArtifactTranslation {
    /// Number of verified UTF-8 source bytes available to stream.
    pub fn source_len(&self) -> usize {
        self.source.len()
    }
    /// Write the verified source. The caller controls flushing and publication.
    pub fn write_source(&self, output: impl std::io::Write) -> std::io::Result<()> {
        self.source.write_to(output)
    }
}
impl std::fmt::Debug for LeanExportArtifactTranslation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LeanExportArtifactTranslation")
            .field("declarations", &self.receipt.declaration_count())
            .field("target", &self.target)
            .field("source_bytes", &self.source_len())
            .finish_non_exhaustive()
    }
}

enum Rendered {
    Memory(String),
    Paged(Snapshot),
}
struct CheckedSource {
    receipt: LeanExportReceipt,
    target: String,
    source: Rendered,
}

/// The memory route remains available to callers that need an owned string.
/// The paged route retains only one unformatted/formatted declaration at once.
struct Output {
    current: String,
    formatted: String,
    raw_bytes: usize,
    declaration_bytes: usize,
    max_bytes: usize,
    paged: Option<Builder>,
}
impl Output {
    fn new(paged: bool) -> Result<Self> {
        Self::with_limits(paged, crate::NativeProofLimits::default())
    }
    fn with_limits(paged: bool, limits: crate::NativeProofLimits) -> Result<Self> {
        Ok(Self {
            current: String::new(),
            formatted: String::new(),
            raw_bytes: 0,
            declaration_bytes: 0,
            max_bytes: limits.max_bytes,
            paged: if paged {
                Some(if limits == crate::NativeProofLimits::default() {
                    Builder::new(SOURCE_BYTES)?
                } else {
                    Builder::with_limit(limits.max_bytes)?
                })
            } else {
                None
            },
        })
    }
    fn push(&mut self, text: &str) -> Result<()> {
        let bytes = self
            .raw_bytes
            .checked_add(text.len())
            .filter(|n| *n <= self.max_bytes)
            .ok_or("proof-source byte limit exceeded")?;
        let declaration_bytes = self
            .declaration_bytes
            .checked_add(text.len())
            .filter(|n| *n <= SOURCE_BYTES)
            .ok_or("proof-source declaration byte limit exceeded")?;
        self.current.push_str(text);
        self.raw_bytes = bytes;
        self.declaration_bytes = declaration_bytes;
        Ok(())
    }
    fn end_declaration(&mut self) -> Result<()> {
        let formatted = crate::format_source(&self.current)
            .map_err(|why| format!("translated source formatting failed: {why}"))?;
        if let Some(builder) = &mut self.paged {
            // These are exclusively mathematical declarations. The formatter
            // adds no blank-line boundary for them, so concatenate chunks as-is.
            builder.append(formatted.as_bytes())?;
        } else {
            self.formatted
                .len()
                .checked_add(formatted.len())
                .filter(|bytes| *bytes <= self.max_bytes)
                .ok_or("formatted proof-source byte limit exceeded")?;
            self.formatted.push_str(&formatted);
        }
        self.current.clear();
        self.declaration_bytes = 0;
        Ok(())
    }
    fn finish(mut self) -> Result<Rendered> {
        if self.paged.is_none() && !self.current.is_empty() {
            self.end_declaration()?;
        }
        match self.paged {
            Some(builder) => {
                if !self.current.is_empty() {
                    return Err("unflushed translated declaration".into());
                }
                Ok(Rendered::Paged(builder.finish()))
            }
            None => Ok(Rendered::Memory(self.formatted)),
        }
    }
}

#[cfg(test)]
mod output_tests {
    use super::*;
    const FORMS: &[&str] = &[
        "(#math-definition value () #pt-nat #pt-zero)",
        "(#math-opaque opaque-value () #pt-nat #pt-zero)",
        "(#theorem reflexive (#universes) (#parameters) (#statement (#pt-eq #pt-nat #pt-zero #pt-zero)) (#proof (#pt-refl #pt-nat #pt-zero)))",
        "(#math-inductive Shape () () (#pt-type 0) ((point ())))",
    ];

    #[test]
    fn streamed_math_boundaries_match_whole_file_formatting_exactly() {
        for left in FORMS {
            for right in FORMS {
                for comments in ["", "; Lean declaration: next\n; Prefix SHA-256: 1234\n"] {
                    let chunks = [
                        format!("; Translation header\n; provenance\n\n{left}\n\n"),
                        format!("{comments}{right}\n\n"),
                    ];
                    let expected = crate::format_source(&chunks.concat()).unwrap();
                    for paged in [false, true] {
                        let mut output = Output::new(paged).unwrap();
                        for chunk in &chunks {
                            output.push(chunk).unwrap();
                            output.end_declaration().unwrap();
                            assert!(output.current.is_empty());
                        }
                        let actual = match output.finish().unwrap() {
                            Rendered::Memory(text) => text,
                            Rendered::Paged(snapshot) => snapshot.text().unwrap(),
                        };
                        assert_eq!(actual, expected);
                    }
                }
            }
        }
    }

    #[test]
    fn cumulative_raw_limit_survives_releasing_each_chunk() {
        let mut output = Output::new(true).unwrap();
        let form = FORMS[0];
        output.raw_bytes = SOURCE_BYTES - form.len();
        output.push(form).unwrap();
        output.end_declaration().unwrap();
        assert!(output.current.is_empty());
        assert_eq!(output.raw_bytes, SOURCE_BYTES);
        assert!(output.push(" ").unwrap_err().contains("byte limit"));
    }

    #[test]
    fn formatted_limit_and_unflushed_forms_cannot_return_an_artifact() {
        let mut output = Output::new(true).unwrap();
        output.paged = Some(Builder::new(2).unwrap());
        output.push("()").unwrap();
        assert!(output
            .end_declaration()
            .unwrap_err()
            .contains("formatted proof-source byte limit"));
        let mut output = Output::new(true).unwrap();
        output.push(FORMS[0]).unwrap();
        assert!(output.finish().err().unwrap().contains("unflushed"));
    }
}

pub(super) fn render(
    replay: &mut Replay,
    receipt: LeanExportReceipt,
    target_identity: &str,
) -> Result<LeanExportReceiptTranslation> {
    let checked = render_inner(replay, receipt, target_identity, false)?;
    let Rendered::Memory(source) = checked.source else {
        return Err("materialized translation returned paged source".into());
    };
    Ok(LeanExportReceiptTranslation {
        receipt: checked.receipt,
        target: checked.target,
        source,
    })
}

pub(super) fn render_artifact(
    replay: &mut Replay,
    receipt: LeanExportReceipt,
    target_identity: &str,
) -> Result<LeanExportArtifactTranslation> {
    let checked = render_inner(replay, receipt, target_identity, true)?;
    let Rendered::Paged(source) = checked.source else {
        return Err("artifact translation returned resident source".into());
    };
    Ok(LeanExportArtifactTranslation {
        receipt: checked.receipt,
        target: checked.target,
        source,
    })
}

fn render_inner(
    replay: &mut Replay,
    receipt: LeanExportReceipt,
    target_identity: &str,
    paged: bool,
) -> Result<CheckedSource> {
    let report = &receipt.summary;
    let limits = report.native_limits.unwrap_or_default();
    if receipt.declaration_count() > limits.max_declarations {
        return Err("native proof declaration limit exceeded".into());
    }
    let names = NativeNames::new(&receipt.declarations, &replay.checked);
    let target = names.forward(target_identity)?;
    let mut writer = Writer {
        kernel: &mut replay.kernel,
        names: &names,
        universes: HashMap::new(),
        output: if limits == crate::NativeProofLimits::default() {
            Output::new(paged)?
        } else {
            Output::with_limits(paged, limits)?
        },
        nodes: 0,
        max_nodes: limits.max_render_nodes,
    };
    writer.push("; Checked native translation of a Lean export, not an admission.\n")?;
    writer.push(&format!("; Lean: {LEAN_EXPORT_VERSION} ({LEAN_EXPORT_GITHASH})\n; Exporter: {EXPORTER_REVISION}\n; Input SHA-256: {}\n; Native theorem: {target}\n", report.input_sha256))?;
    if report.budget != crate::ProofBudget::default() {
        writer.push(&format!(
            "; Proof budget: work={} phase-bytes={} total-bytes={}\n",
            report.budget.work(),
            report.budget.phase_bytes(),
            report.budget.total_bytes()
        ))?;
    }
    if limits != crate::NativeProofLimits::default() {
        writer.push(&format!("; Native proof limits: {limits}\n"))?;
    }
    writer.push("; Keep the upstream source/license provenance with this translation.\n\n")?;
    if !report.axioms.is_empty() {
        writer.push(&format!(
            "; Declared logical axioms: {}\n; Target logical foundations: {}\n\n",
            Json::Array(report.axioms.iter().map(|name| text_json(name)).collect()).render(),
            Json::Array(
                report
                    .target_axioms
                    .iter()
                    .map(|name| text_json(name))
                    .collect()
            )
            .render()
        ))?;
    }
    if !report.foundations.is_empty() {
        writer.push(&format!(
            "; Checked primitive foundations: {}\n\n",
            Json::Array(
                report
                    .foundations
                    .iter()
                    .map(|name| text_json(name))
                    .collect()
            )
            .render()
        ))?;
    }
    for index in 0..receipt.declaration_count() {
        let declaration = receipt.declarations.get(index)?;
        let checked = writer
            .kernel
            .declarations
            .get(&declaration.identity)?
            .ok_or("checked source declaration is missing")?;
        writer.kernel.reset_budget();
        writer.universes = checked
            .universes
            .iter()
            .enumerate()
            .map(|(index, original)| (original.clone(), format!("u{index}")))
            .collect();
        writer.push(&format!(
            "; Lean declaration: {}\n; Identity: {}\n; Export line: {}\n; Prefix SHA-256: {}\n",
            text_json(&declaration.name).render(),
            text_json(&declaration.identity).render(),
            declaration.line,
            declaration.sha256
        ))?;
        if let Some(family) = &checked.family {
            writer.inductive(&declaration.identity, &checked.universes, family)?;
        } else {
            let retained = if checked.value.is_none() {
                replay.initializers.get(
                    index,
                    &replay.expressions,
                    &replay.names,
                    &replay.levels,
                )?
            } else {
                None
            };
            let value = checked
                .value
                .as_ref()
                .or(retained.as_ref())
                .ok_or("checked opaque/theorem initializer was not retained for translation")?;
            writer.definition(
                &declaration.identity,
                &checked.universes,
                &checked.ty,
                value,
                &declaration.kind,
            )?;
        }
        writer.push("\n\n")?;
        writer.output.end_declaration()?;
        drop(checked);
        replay.expressions.end_record();
    }
    // Formatting and the common declaration parser/kernel still check the
    // complete output. The source directory grants no declaration authority.
    let Writer { output, .. } = writer;
    let source = output.finish()?;
    let program = match &source {
        Rendered::Memory(text) => {
            if limits == crate::NativeProofLimits::default() {
                crate::proof::kernel::native_source::Source::new(text)
            } else {
                crate::proof::kernel::native_source::Source::with_limits(text, limits)
            }
        }
        Rendered::Paged(snapshot) => {
            if limits == crate::NativeProofLimits::default() {
                crate::proof::kernel::native_source::Source::snapshot(snapshot.clone())
            } else {
                crate::proof::kernel::native_source::Source::snapshot_with_limits(
                    snapshot.clone(),
                    limits,
                )
            }
        }
    }
    .map_err(|why| format!("translated source parsing failed: {why}"))?;
    program
        .check(report.budget)
        .map_err(|(name, why)| format!("translated source recheck failed: {name}: {why}"))?;
    if !program.is_theorem(&target) {
        return Err("translation did not preserve the selected theorem declaration".into());
    }
    correspondence::check_source_with_limits(
        correspondence::Context {
            kernel: &mut replay.kernel,
            initializers: &replay.initializers,
            expressions: &mut replay.expressions,
            names: &replay.names,
            levels: &replay.levels,
        },
        &names,
        &program,
        limits,
    )
    .map_err(|why| format!("translated source correspondence failed: {why}"))?;
    if program.foundation_dependencies(&target)? != report.target_axioms {
        return Err(
            "translated theorem's logical foundations differ from the checked export".into(),
        );
    }
    drop(program);
    drop(names);
    Ok(CheckedSource {
        receipt,
        target,
        source,
    })
}

#[cfg(test)]
fn check_target_foundations(
    program: &crate::Program,
    target: &str,
    expected: &[String],
) -> Result<()> {
    let actual = crate::proof::kernel::foundation_dependencies(program, target)?;
    if actual != expected {
        return Err(
            "translated theorem's logical foundations differ from the checked export".into(),
        );
    }
    Ok(())
}

#[cfg(test)]
mod foundation_audit_tests {
    use super::*;
    #[test]
    fn a_well_typed_proof_of_the_same_goal_cannot_silently_add_an_assumption() {
        let prefix = include_str!("../../../examples/proof_foundations.lim");
        for (body,expected) in [
            ("(#pt-refl #pt-nat #pt-zero)",true),
            ("(#pt-let (#parameter unused #pt-nat) (#pt-use selected-natural ()) (#pt-refl #pt-nat #pt-zero))",false),
        ] {
            let source=format!("{prefix}\n(#theorem audit-goal (#universes) (#parameters)
              (#statement (#pt-eq #pt-nat #pt-zero #pt-zero)) (#proof {body}))");
            let program=crate::parse_program(&source).unwrap();
            crate::check_types(&program).unwrap();
            let result=check_target_foundations(&program,"audit-goal",&[]);
            if expected {result.unwrap();} else {assert!(result.unwrap_err().contains("logical foundations differ"));}
        }
    }
}

struct Writer<'a, 'b> {
    kernel: &'a mut Kernel,
    names: &'a NativeNames<'b>,
    universes: HashMap<String, String>,
    output: Output,
    nodes: usize,
    max_nodes: usize,
}

impl Writer<'_, '_> {
    fn node(&mut self, depth: usize) -> Result<()> {
        self.nodes = self
            .nodes
            .checked_add(1)
            .ok_or("proof-source node count overflow")?;
        if self.nodes > self.max_nodes || depth > 96 {
            Err("proof-source node or depth limit exceeded".into())
        } else {
            Ok(())
        }
    }
    fn term(&mut self, value: &T, binders: usize, depth: usize) -> Result<()> {
        self.node(depth)?;
        match value.as_ref() {
            Term::NatLiteral { family, value } => self.push(&format!(
                "(#pt-nat-literal {} {})",
                self.name(family)?,
                text_json(value.decimal()).render()
            )),
            Term::Sort(level) => {
                self.push("(#pt-sort ")?;
                self.level(level)?;
                self.push(")")
            }
            Term::QuotType(l, a, r) | Term::QuotMake(l, a, r, _) => {
                self.push(if matches!(value.as_ref(), Term::QuotType(..)) {
                    "(#pt-quot "
                } else {
                    "(#pt-quot-make "
                })?;
                self.level(l)?;
                self.push(" ")?;
                self.term(a, binders, depth + 1)?;
                self.push(" ")?;
                self.term(r, binders, depth + 1)?;
                if let Term::QuotMake(_, _, _, x) = value.as_ref() {
                    self.push(" ")?;
                    self.term(x, binders, depth + 1)?;
                }
                self.push(")")
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
            } => {
                self.push("(#pt-quot-lift ")?;
                self.levels(&[source_level.clone(), target_level.clone()])?;
                for value in [ty, relation, target, function, respect, subject] {
                    self.push(" ")?;
                    self.term(value, binders, depth + 1)?;
                }
                self.push(")")
            }
            Term::QuotInduct {
                level,
                ty,
                relation,
                motive,
                branch,
                subject,
            } => {
                self.push("(#pt-quot-induct ")?;
                self.level(level)?;
                for value in [ty, relation, motive, branch, subject] {
                    self.push(" ")?;
                    self.term(value, binders, depth + 1)?;
                }
                self.push(")")
            }
            Term::Var(index) => {
                let number = index
                    .checked_add(1)
                    .and_then(|offset| binders.checked_sub(offset))
                    .ok_or("free variable in source translation")?;
                self.push(&format!("v{number}"))
            }
            Term::Global(name, levels) => {
                if matches!(name.as_str(), "#pt-nat" | "#pt-false") && levels.is_empty() {
                    return self.push(name);
                }
                self.push(&format!("(#pt-use {} ", self.name(name)?))?;
                self.levels(levels)?;
                self.push(")")
            }
            Term::Pi(..) | Term::Lam(..) => {
                let lambda = matches!(value.as_ref(), Term::Lam(..));
                self.push(if lambda { "(#pt-lambda (" } else { "(#pt-pi (" })?;
                let mut body = value.clone();
                let mut count = 0;
                while count < 64 {
                    let (domain, next) = match body.as_ref() {
                        Term::Lam(a, b) if lambda => (a.clone(), b.clone()),
                        Term::Pi(a, b) if !lambda => (a.clone(), b.clone()),
                        _ => break,
                    };
                    if count != 0 {
                        self.node(depth)?;
                        self.push(" ")?;
                    }
                    self.push(&format!("(v{} ", binders + count))?;
                    self.term(&domain, binders + count, depth + 1)?;
                    self.push(")")?;
                    body = next;
                    count += 1;
                }
                self.push(") ")?;
                self.term(&body, binders + count, depth + 1)?;
                self.push(")")
            }
            Term::Sigma(domain, body) => {
                self.push(&format!("(#pt-sigma ((v{binders} "))?;
                self.term(domain, binders, depth + 1)?;
                self.push(")) ")?;
                self.term(body, binders + 1, depth + 1)?;
                self.push(")")
            }
            Term::Let(ty, initializer, body) => {
                self.push(&format!("(#pt-let (#parameter v{binders} "))?;
                self.term(ty, binders, depth + 1)?;
                self.push(") ")?;
                self.term(initializer, binders, depth + 1)?;
                self.push(" ")?;
                self.term(body, binders + 1, depth + 1)?;
                self.push(")")
            }
            Term::App(..) => {
                let mut function = value.clone();
                let mut arguments = vec![];
                while arguments.len() < 64 {
                    let Term::App(f, a) = function.as_ref() else {
                        break;
                    };
                    arguments.push(a.clone());
                    function = f.clone();
                    if arguments.len() > 1 {
                        self.node(depth)?;
                    }
                }
                self.push("(#pt-app ")?;
                self.term(&function, binders, depth + 1)?;
                for argument in arguments.iter().rev() {
                    self.push(" ")?;
                    self.term(argument, binders, depth + 1)?;
                }
                self.push(")")
            }
            Term::Pair(a, b, c) => self.form("#pt-pair", &[a, b, c], binders, depth),
            Term::Eq(a, b, c) => self.form("#pt-eq", &[a, b, c], binders, depth),
            Term::Refl(a, b) => self.form("#pt-refl", &[a, b], binders, depth),
            Term::First(a) => self.form("#pt-first", &[a], binders, depth),
            Term::Second(a) => self.form("#pt-second", &[a], binders, depth),
            Term::EqElim {
                ty,
                left,
                motive,
                base,
                right,
                proof,
            } => self.form(
                "#pt-eq-elim",
                &[ty, left, motive, base, right, proof],
                binders,
                depth,
            ),
            Term::Project {
                family,
                index,
                subject,
            } => {
                self.push(&format!("(#pt-project {} {index} ", self.name(family)?))?;
                self.term(subject, binders, depth + 1)?;
                self.push(")")
            }
            Term::Ctor {
                family,
                levels,
                parameters,
                constructor,
                fields,
            } => {
                self.push(&format!("(#pt-construct {} ", self.name(family)?))?;
                self.levels(levels)?;
                self.push(" ")?;
                self.terms(parameters, binders, depth + 1)?;
                self.push(&format!(
                    " {} ",
                    if family == "#pt-nat" || family == "#pt-false" {
                        constructor.clone()
                    } else {
                        self.name(constructor)?
                    }
                ))?;
                self.terms(fields, binders, depth + 1)?;
                self.push(")")
            }
            Term::Induct {
                family,
                levels,
                parameters,
                indices,
                motive,
                branches,
                subject,
            } => {
                self.push(&format!("(#pt-induct {} ", self.name(family)?))?;
                self.levels(levels)?;
                self.push(" ")?;
                self.terms(parameters, binders, depth + 1)?;
                self.push(" ")?;
                if !indices.is_empty() {
                    self.indices(indices, binders, depth + 1)?;
                    self.push(" ")?;
                }
                self.term(motive, binders, depth + 1)?;
                self.push(" ")?;
                self.terms(branches, binders, depth + 1)?;
                self.push(" ")?;
                self.term(subject, binders, depth + 1)?;
                self.push(")")
            }
            Term::MutualInduct {
                family,
                levels,
                parameters,
                indices,
                cases,
                subject,
            } => self.group(
                family, levels, parameters, indices, cases, subject, binders, depth,
            ),
            Term::NestedInduct { .. } => {
                Err("unexpected source-only eliminator in an elaborated export".into())
            }
            Term::SelfType | Term::SelfAt(_) | Term::Recur(..) => {
                Err("unexpanded recursive marker in translated evidence".into())
            }
        }
    }
    fn form(&mut self, head: &str, terms: &[&T], binders: usize, depth: usize) -> Result<()> {
        self.push(&format!("({head}"))?;
        for term in terms {
            self.push(" ")?;
            self.term(term, binders, depth + 1)?;
        }
        self.push(")")
    }
    fn indices(&mut self, values: &[T], binders: usize, depth: usize) -> Result<()> {
        self.push("(#indices")?;
        for value in values {
            self.push(" ")?;
            self.term(value, binders, depth + 1)?;
        }
        self.push(")")
    }
    #[expect(clippy::too_many_arguments)]
    fn group(
        &mut self,
        family: &str,
        levels: &[Level],
        parameters: &[T],
        indices: &[T],
        cases: &[RecursionCase],
        subject: &T,
        binders: usize,
        depth: usize,
    ) -> Result<()> {
        let (description, _) = self.kernel.family(family, levels, 0)?;
        let nested = self.kernel.nested.any(&description.group)?;
        if nested {
            let roots = self.kernel.nested.roots(&description.group)?;
            let owner = roots.first().ok_or("nested group lacks a public owner")?;
            let selected = description
                .group
                .iter()
                .position(|name| name == family)
                .ok_or("nested group lacks its selected case")?;
            self.push(&format!("(#pt-nested-induct {} ", self.name(owner)?))?;
            self.levels(levels)?;
            self.push(" ")?;
            self.terms(parameters, binders, depth + 1)?;
            self.push(&format!(" {selected} "))?;
        } else {
            self.push(&format!("(#pt-mutual-induct {} ", self.name(family)?))?;
            self.levels(levels)?;
            self.push(" ")?;
            self.terms(parameters, binders, depth + 1)?;
            self.push(" ")?;
        }
        self.indices(indices, binders, depth + 1)?;
        self.push(" (")?;
        for (index, case) in cases.iter().enumerate() {
            if index != 0 {
                self.push(" ")?;
            }
            if nested {
                self.push("(#pt-case ")?;
                let selector =
                    self.kernel
                        .family_application(&case.family, levels, parameters, &[], 0)?;
                self.term(&selector, binders, depth + 1)?;
            } else {
                self.push(&format!("({}", self.name(&case.family)?))?;
            }
            self.push(" ")?;
            self.term(&case.motive, binders, depth + 1)?;
            self.push(" ")?;
            self.terms(&case.branches, binders, depth + 1)?;
            self.push(")")?;
        }
        self.push(") ")?;
        self.term(subject, binders, depth + 1)?;
        self.push(")")
    }
    fn push(&mut self, text: &str) -> Result<()> {
        self.output.push(text)
    }
    fn name(&self, original: &str) -> Result<String> {
        match original {
            "#pt-nat" | "#pt-false" => Ok(original.into()),
            _ if foundation::label(original).is_some() => Ok(original.into()),
            _ => self.names.forward(original),
        }
    }
    fn level(&mut self, level: &Level) -> Result<()> {
        self.push(&level.source(&self.universes)?)
    }
    fn levels(&mut self, levels: &[Level]) -> Result<()> {
        self.push("(")?;
        for (index, level) in levels.iter().enumerate() {
            if index != 0 {
                self.push(" ")?;
            }
            self.level(level)?;
        }
        self.push(")")
    }
    fn universe_binders(&mut self, universes: &[String]) -> Result<()> {
        self.push("(")?;
        for (index, _) in universes.iter().enumerate() {
            if index != 0 {
                self.push(" ")?;
            }
            self.push(&format!("u{index}"))?;
        }
        self.push(")")
    }
    fn terms(&mut self, values: &[T], binders: usize, depth: usize) -> Result<()> {
        self.push("(")?;
        for (index, value) in values.iter().enumerate() {
            if index != 0 {
                self.push(" ")?;
            }
            self.term(value, binders, depth + 1)?;
        }
        self.push(")")
    }
    fn domains(&mut self, values: &[T], binders: usize, indices: bool) -> Result<()> {
        self.push(if indices { "(#indices" } else { "(" })?;
        for (index, value) in values.iter().enumerate() {
            if indices || index != 0 {
                self.push(" ")?;
            }
            self.push(&format!(
                "({}v{} ",
                if indices { "#parameter " } else { "" },
                binders + index
            ))?;
            self.term(value, binders + index, 0)?;
            self.push(")")?;
        }
        self.push(")")
    }
    fn inductive(&mut self, name: &str, universes: &[String], family: &Family) -> Result<()> {
        self.push(&format!("(#math-inductive {} ", self.name(name)?))?;
        self.universe_binders(universes)?;
        self.push(" ")?;
        self.domains(&family.parameters, 0, false)?;
        let roots = self.kernel.nested.roots(&family.group)?;
        if roots.len() > 1 {
            self.push(" (#mutual")?;
            for root in roots {
                self.push(&format!(" {}", self.name(&root)?))?;
            }
            self.push(")")?;
        }
        if !family.indices.is_empty() {
            self.push(" ")?;
            self.domains(&family.indices, family.parameters.len(), true)?;
        }
        self.push(" (#pt-sort ")?;
        self.level(&family.sort)?;
        self.push(") (")?;
        for (index, constructor) in family.constructors.iter().enumerate() {
            if index != 0 {
                self.push(" ")?;
            }
            self.push(&format!("({} ", self.name(&constructor.name)?))?;
            self.domains(&constructor.fields, family.parameters.len(), false)?;
            if !family.indices.is_empty() {
                self.push(" ")?;
                self.terms(
                    &constructor.result_indices,
                    family.parameters.len() + constructor.fields.len(),
                    0,
                )?;
            }
            self.push(")")?;
        }
        self.push("))")
    }
    fn definition(
        &mut self,
        name: &str,
        universes: &[String],
        ty: &T,
        value: &T,
        kind: &str,
    ) -> Result<()> {
        if kind == "theorem" {
            self.push(&format!("(#theorem {} (#universes", self.name(name)?))?;
            for index in 0..universes.len() {
                self.push(&format!(" u{index}"))?;
            }
            self.push(") (#parameters) (#statement ")?;
            self.term(ty, 0, 0)?;
            self.push(") (#proof ")?;
            self.term(value, 0, 0)?;
            self.push("))")
        } else {
            self.push(&format!(
                "({} {} ",
                if matches!(kind, "opaque" | "axiom") {
                    "#math-opaque"
                } else {
                    "#math-definition"
                },
                self.name(name)?
            ))?;
            self.universe_binders(universes)?;
            self.push(" ")?;
            self.term(ty, 0, 0)?;
            self.push(" ")?;
            self.term(value, 0, 0)?;
            self.push(")")
        }
    }
}

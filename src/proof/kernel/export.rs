//! Bounded replay of lean4export 3.1.0 records. Export claims are not evidence:
//! every accepted declaration is checked by the ordinary dependent kernel.
use super::*;
use crate::lsp::json::Json;
use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::io::BufRead;

#[path = "export_foundations.rs"]
mod axioms;
#[path = "export_candidates.rs"]
mod candidates;
#[path = "export_checked.rs"]
mod checked;
#[path = "export_expressions.rs"]
mod expressions;
#[cfg(test)]
#[path = "export_fixtures_tests.rs"]
mod fixtures_tests;
#[path = "export_inductive.rs"]
mod inductives;
#[path = "export_initializers.rs"]
mod initializers;
#[path = "export_inventory.rs"]
mod inventory;
#[path = "export_levels.rs"]
mod levels;
#[path = "export_limits.rs"]
mod limits;
pub use limits::LeanExportLimits;
#[path = "export_names.rs"]
mod names;
#[path = "export_quotient.rs"]
mod quotient;
#[path = "export_report.rs"]
mod report;
#[path = "export_source.rs"]
mod source;
use super::scratch as spool;
#[path = "export_strings.rs"]
mod strings;
#[path = "export_terms.rs"]
mod terms;
pub use source::{
    LeanExportArtifactTranslation, LeanExportReceiptTranslation, LeanExportTranslation,
};

pub const LEAN_EXPORT_FORMAT: &str = "3.1.0";
pub const LEAN_EXPORT_VERSION: &str = "4.33.1";
pub const LEAN_EXPORT_GITHASH: &str = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6";
const EXPORTER_REVISION: &str = "15f6055e299ad5b89345e533cc2192f4cc00f659";
const MAX_LINE: usize = 8 * 1024 * 1024;
const MAX_BYTES: u64 = 64 * 1024 * 1024;
const MAX_NAMES: usize = 100_000;
const MAX_NAME_BYTES: usize = 16 * 1024 * 1024;
const MAX_LEVELS: usize = 20_000;
const MAX_EXPRESSIONS: usize = 200_000;
const MAX_EXPRESSION_DEPTH: usize = 256;
const MAX_DECLARATIONS: usize = 4096;
const MAX_DEPENDENCIES: usize = 1_000_000;

/// Default replay is constructive. Lean4 enables only the three pinned,
/// fixed-signature logical axioms, checked through ordinary native adapters.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum LeanFoundationPolicy {
    #[default]
    Constructive,
    Lean4,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeanDeclarationReport {
    pub name: String,
    pub identity: String,
    pub kind: String,
    pub line: usize,
    pub sha256: String,
    pub dependencies: Vec<String>,
}

#[derive(Clone, Debug)]
pub struct LeanExportReport {
    pub budget: crate::ProofBudget,
    pub limits: LeanExportLimits,
    /// Selected native output profile, when this replay emits native source.
    pub native_limits: Option<crate::NativeProofLimits>,
    pub target: String,
    pub input_sha256: String,
    pub bytes: u64,
    pub records: u64,
    pub declarations: Vec<LeanDeclarationReport>,
    /// Additional checked primitive packages, separate from exported axioms.
    pub foundations: Vec<String>,
    /// All accepted fixed axiom declarations in the input, sorted by name.
    pub axioms: Vec<String>,
    /// The selected theorem's transitive axiom closure, sorted by name.
    pub target_axioms: Vec<String>,
}

/// A checked replay receipt whose declaration inventory can remain paged.
/// All declarations and the target's axiom closure are checked before this
/// value is returned. Receipt bytes and scratch storage are not proof inputs.
pub struct LeanExportReceipt {
    summary: LeanExportReport,
    declarations: inventory::Inventory,
}

impl std::fmt::Debug for LeanExportReceipt {
    fn fmt(&self, output: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        output
            .debug_struct("LeanExportReceipt")
            .field("summary", &self.summary)
            .field("declaration_count", &self.declaration_count())
            .finish_non_exhaustive()
    }
}

impl LeanExportReceipt {
    pub fn native_limits(&self) -> Option<crate::NativeProofLimits> {
        self.summary.native_limits
    }
    pub fn limits(&self) -> LeanExportLimits {
        self.summary.limits
    }
    pub fn declaration_count(&self) -> usize {
        self.declarations.len()
    }
    pub fn axioms(&self) -> &[String] {
        &self.summary.axioms
    }
    pub fn target_axioms(&self) -> &[String] {
        &self.summary.target_axioms
    }
    /// Explicitly materialize all declaration reports for in-memory callers.
    pub fn into_report(mut self) -> std::result::Result<LeanExportReport, LeanExportError> {
        self.summary.declarations =
            self.declarations
                .into_vec()
                .map_err(|message| LeanExportError {
                    line: (self.summary.records as usize).saturating_add(1),
                    message,
                })?;
        Ok(self.summary)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeanExportError {
    pub line: usize,
    pub message: String,
}
impl std::fmt::Display for LeanExportError {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(out, "Lean export line {}: {}", self.line, self.message)
    }
}
impl std::error::Error for LeanExportError {}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Name {
    key: String,
    display: String,
    depth: usize,
}
struct Replay {
    kernel: Kernel,
    limits: LeanExportLimits,
    names: names::Names,
    name_bytes: usize,
    levels: levels::Levels,
    expressions: expressions::Expressions,
    reports: inventory::Inventory,
    checked: checked::Index,
    target: String,
    selected: Option<(String, String, String)>,
    ambiguous_target: bool,
    axioms: BTreeSet<String>,
    dependency_count: usize,
    payload_bytes: usize,
    dependency_bytes: usize,
    transformation_bytes: usize,
    natural_literals: bool,
    string_literals: bool,
    line: usize,
    input_hash: hash::Sha256,
    digest: Option<String>,
    retain_bodies: bool,
    initializers: initializers::Initializers,
    quotient_stage: usize,
    foundation_policy: LeanFoundationPolicy,
}

/// Reads the actual pinned NDJSON protocol without executing Lean or trusting
/// a claimed check result. This entry point rejects all axiom records.
pub fn check_lean_export<R: BufRead>(
    reader: R,
    target: &str,
) -> std::result::Result<LeanExportReport, LeanExportError> {
    check_lean_export_with_policy(reader, target, LeanFoundationPolicy::Constructive)
}

/// Select a fixed foundation policy explicitly. Even Lean4 rejects arbitrary
/// axioms and checks native initializers against every imported signature.
pub fn check_lean_export_with_policy<R: BufRead>(
    reader: R,
    target: &str,
    policy: LeanFoundationPolicy,
) -> std::result::Result<LeanExportReport, LeanExportError> {
    check_lean_export_with_budget(reader, target, policy, crate::ProofBudget::default())
}

/// Replay every declaration with explicitly selected resource accounting.
/// Budget selection cannot authorize a logical axiom or an unchecked term.
pub fn check_lean_export_with_budget<R: BufRead>(
    reader: R,
    target: &str,
    policy: LeanFoundationPolicy,
    budget: crate::ProofBudget,
) -> std::result::Result<LeanExportReport, LeanExportError> {
    check_lean_export_with_limits(reader, target, policy, budget, LeanExportLimits::default())
}

/// Check all input using explicit cumulative input limits and kernel budgets.
pub fn check_lean_export_with_limits<R: BufRead>(
    reader: R,
    target: &str,
    policy: LeanFoundationPolicy,
    budget: crate::ProofBudget,
    limits: LeanExportLimits,
) -> std::result::Result<LeanExportReport, LeanExportError> {
    check_lean_export_receipt_with_limits(reader, target, policy, budget, limits)?.into_report()
}

/// Check the entire export and retain a paged inventory for streamed receipts.
/// Resource limits and logical checks are identical to the materialized API.
pub fn check_lean_export_receipt_with_budget<R: BufRead>(
    reader: R,
    target: &str,
    policy: LeanFoundationPolicy,
    budget: crate::ProofBudget,
) -> std::result::Result<LeanExportReceipt, LeanExportError> {
    check_lean_export_receipt_with_limits(
        reader,
        target,
        policy,
        budget,
        LeanExportLimits::default(),
    )
}

/// Retain a paged receipt with explicitly selected cumulative input limits.
pub fn check_lean_export_receipt_with_limits<R: BufRead>(
    reader: R,
    target: &str,
    policy: LeanFoundationPolicy,
    budget: crate::ProofBudget,
    limits: LeanExportLimits,
) -> std::result::Result<LeanExportReceipt, LeanExportError> {
    let _stage = crate::timing::stage("lean_export_replay");
    replay_export(reader, target, false, policy, budget, limits).map(|(_, report, _)| report)
}

/// Replays the full export, translates its checked environment to ordinary Lim
/// declarations, and independently checks the complete native source output.
pub fn translate_lean_export<R: BufRead>(
    reader: R,
    target: &str,
) -> std::result::Result<LeanExportTranslation, LeanExportError> {
    translate_lean_export_with_policy(reader, target, LeanFoundationPolicy::Constructive)
}

/// Replay with explicit fixed foundations, then check the emitted declarations,
/// initializer correspondence, opacity and selected theorem's assumption closure.
pub fn translate_lean_export_with_policy<R: BufRead>(
    reader: R,
    target: &str,
    policy: LeanFoundationPolicy,
) -> std::result::Result<LeanExportTranslation, LeanExportError> {
    translate_lean_export_with_budget(reader, target, policy, crate::ProofBudget::default())
}

/// Independently recheck native output with the selected resource budget.
pub fn translate_lean_export_with_budget<R: BufRead>(
    reader: R,
    target: &str,
    policy: LeanFoundationPolicy,
    budget: crate::ProofBudget,
) -> std::result::Result<LeanExportTranslation, LeanExportError> {
    translate_lean_export_with_limits(reader, target, policy, budget, LeanExportLimits::default())
}

/// Materialize independently checked native output with selected input limits.
pub fn translate_lean_export_with_limits<R: BufRead>(
    reader: R,
    target: &str,
    policy: LeanFoundationPolicy,
    budget: crate::ProofBudget,
    limits: LeanExportLimits,
) -> std::result::Result<LeanExportTranslation, LeanExportError> {
    translate_lean_export_with_profiles(
        reader,
        target,
        policy,
        budget,
        limits,
        crate::NativeProofLimits::default(),
    )
}

/// Check raw input and materialize independently checked native output using
/// separately selected cumulative input and native source resource profiles.
pub fn translate_lean_export_with_profiles<R: BufRead>(
    reader: R,
    target: &str,
    policy: LeanFoundationPolicy,
    budget: crate::ProofBudget,
    limits: LeanExportLimits,
    native_limits: crate::NativeProofLimits,
) -> std::result::Result<LeanExportTranslation, LeanExportError> {
    let translation = translate_lean_export_receipt_with_profiles(
        reader,
        target,
        policy,
        budget,
        limits,
        native_limits,
    )?;
    Ok(LeanExportTranslation {
        report: translation.receipt.into_report()?,
        target: translation.target,
        source: translation.source,
    })
}

/// Independently check native output while retaining paged declaration reports.
/// The native source string remains owned; parsed declarations are released.
pub fn translate_lean_export_receipt_with_budget<R: BufRead>(
    reader: R,
    target: &str,
    policy: LeanFoundationPolicy,
    budget: crate::ProofBudget,
) -> std::result::Result<LeanExportReceiptTranslation, LeanExportError> {
    translate_lean_export_receipt_with_limits(
        reader,
        target,
        policy,
        budget,
        LeanExportLimits::default(),
    )
}

/// Native source and a paged receipt with selected cumulative input limits.
pub fn translate_lean_export_receipt_with_limits<R: BufRead>(
    reader: R,
    target: &str,
    policy: LeanFoundationPolicy,
    budget: crate::ProofBudget,
    limits: LeanExportLimits,
) -> std::result::Result<LeanExportReceiptTranslation, LeanExportError> {
    translate_lean_export_receipt_with_profiles(
        reader,
        target,
        policy,
        budget,
        limits,
        crate::NativeProofLimits::default(),
    )
}

/// Independently checked source with paged reports and explicit native limits.
pub fn translate_lean_export_receipt_with_profiles<R: BufRead>(
    reader: R,
    target: &str,
    policy: LeanFoundationPolicy,
    budget: crate::ProofBudget,
    limits: LeanExportLimits,
    native_limits: crate::NativeProofLimits,
) -> std::result::Result<LeanExportReceiptTranslation, LeanExportError> {
    let native_limits = native_limits
        .validate()
        .map_err(|message| LeanExportError { line: 0, message })?;
    let (mut replay, mut receipt, identity) = {
        let _stage = crate::timing::stage("lean_export_replay");
        replay_export(reader, target, true, policy, budget, limits)?
    };
    receipt.summary.native_limits = Some(native_limits);
    let _stage = crate::timing::stage("lean_export_source");
    let line = replay.line.saturating_add(1);
    let result = source::render(&mut replay, receipt, &identity)
        .map_err(|message| LeanExportError { line, message });
    drop(replay);
    result
}

/// Replay and independently check a bounded native artifact without retaining
/// the whole emitted source string. No bytes are published before validation.
pub fn translate_lean_export_artifact_with_budget<R: BufRead>(
    reader: R,
    target: &str,
    policy: LeanFoundationPolicy,
    budget: crate::ProofBudget,
) -> std::result::Result<LeanExportArtifactTranslation, LeanExportError> {
    translate_lean_export_artifact_with_limits(
        reader,
        target,
        policy,
        budget,
        LeanExportLimits::default(),
    )
}

/// Check and spool native output with selected cumulative raw input limits.
/// Native source encoding bounds and native checking budgets remain separate.
pub fn translate_lean_export_artifact_with_limits<R: BufRead>(
    reader: R,
    target: &str,
    policy: LeanFoundationPolicy,
    budget: crate::ProofBudget,
    limits: LeanExportLimits,
) -> std::result::Result<LeanExportArtifactTranslation, LeanExportError> {
    translate_lean_export_artifact_with_profiles(
        reader,
        target,
        policy,
        budget,
        limits,
        crate::NativeProofLimits::default(),
    )
}

/// Check and spool output with explicit, independent raw and native profiles.
pub fn translate_lean_export_artifact_with_profiles<R: BufRead>(
    reader: R,
    target: &str,
    policy: LeanFoundationPolicy,
    budget: crate::ProofBudget,
    limits: LeanExportLimits,
    native_limits: crate::NativeProofLimits,
) -> std::result::Result<LeanExportArtifactTranslation, LeanExportError> {
    let native_limits = native_limits
        .validate()
        .map_err(|message| LeanExportError { line: 0, message })?;
    let (mut replay, mut receipt, identity) = {
        let _stage = crate::timing::stage("lean_export_replay");
        replay_export(reader, target, true, policy, budget, limits)?
    };
    receipt.summary.native_limits = Some(native_limits);
    let _stage = crate::timing::stage("lean_export_source");
    let line = replay.line.saturating_add(1);
    source::render_artifact(&mut replay, receipt, &identity)
        .map_err(|message| LeanExportError { line, message })
}

fn replay_export<R: BufRead>(
    reader: R,
    target: &str,
    retain_bodies: bool,
    policy: LeanFoundationPolicy,
    budget: crate::ProofBudget,
    limits: LeanExportLimits,
) -> std::result::Result<(Replay, LeanExportReceipt, String), LeanExportError> {
    let limits = limits
        .validate()
        .map_err(|message| LeanExportError { line: 0, message })?;
    let mut replay = Replay::with_limits(budget, retain_bodies, limits);
    replay.foundation_policy = policy;
    replay_reader(reader, target, replay)
}

fn replay_reader<R: BufRead>(
    mut reader: R,
    target: &str,
    mut replay: Replay,
) -> std::result::Result<(Replay, LeanExportReceipt, String), LeanExportError> {
    let budget = replay.kernel.budget;
    replay.target = target.to_owned();
    let mut total = 0u64;
    let mut line = Vec::new();
    loop {
        line.clear();
        let count = std::io::Read::take(&mut reader, (MAX_LINE + 1) as u64)
            .read_until(b'\n', &mut line)
            .map_err(|why| LeanExportError {
                line: replay.line + 1,
                message: format!("input read failed: {why}"),
            })?;
        if count == 0 {
            break;
        }
        replay.line += 1;
        let result = (|| {
            if line.len() > MAX_LINE {
                return Err("export line byte limit exceeded".into());
            }
            total = total
                .checked_add(line.len() as u64)
                .ok_or("export byte count overflow")?;
            if total > replay.limits.max_bytes {
                return Err("export total byte limit exceeded; no theorem was established".into());
            }
            let text = std::str::from_utf8(&line).map_err(|_| "export must be UTF-8")?;
            let record = crate::lsp::json::parse(text)
                .map_err(|why| format!("invalid export JSON: {why}"))?;
            replay.input_hash.update(&line);
            // Only declarations need a finalized prefix. Invalidate it for
            // every record, including unused primitive tables after a target.
            replay.digest = None;
            if replay.line == 1 {
                replay.metadata(&record)
            } else {
                replay.record(&record)
            }
        })();
        result.map_err(|message| LeanExportError {
            line: replay.line,
            message,
        })?;
    }
    let end_line = replay.line.saturating_add(1);
    let failure = |message| LeanExportError {
        line: end_line,
        message,
    };
    if replay.line == 0 {
        return Err(failure("missing export metadata".into()));
    }
    replay.reset_budget().map_err(failure)?;
    if replay.natural_literals {
        replay.check_natural_signature().map_err(failure)?;
    }
    if replay.quotient_stage != 0 && replay.quotient_stage != 4 {
        return Err(failure("incomplete checked quotient package".into()));
    }
    if replay.ambiguous_target {
        return Err(failure("theorem target is missing or ambiguous".into()));
    }
    let (target_name, identity, kind) = replay
        .selected
        .take()
        .ok_or_else(|| failure("theorem target is missing or ambiguous".into()))?;
    if kind != "theorem" {
        return Err(failure(
            "the selected export declaration is not a theorem".into(),
        ));
    }
    let target_axioms = replay.target_axioms(&identity).map_err(failure)?;
    let report = LeanExportReport {
        budget,
        limits: replay.limits,
        native_limits: None,
        target: target_name,
        input_sha256: hash::hex(&replay.input_hash.clone().finish()),
        bytes: total,
        records: replay.line as u64,
        axioms: std::mem::take(&mut replay.axioms).into_iter().collect(),
        target_axioms,
        declarations: vec![],
        foundations: if replay.quotient_stage == 4 {
            vec!["quotient-computation-v1".into()]
        } else {
            vec![]
        },
    };
    let report = LeanExportReceipt {
        summary: report,
        declarations: std::mem::replace(&mut replay.reports, inventory::Inventory::new()),
    };
    Ok((replay, report, identity))
}

impl Replay {
    #[cfg(test)]
    fn new() -> Self {
        Self::with_retention(crate::ProofBudget::default(), false)
    }
    #[cfg(test)]
    fn with_retention(budget: crate::ProofBudget, retain_bodies: bool) -> Self {
        Self::with_limits(budget, retain_bodies, LeanExportLimits::default())
    }
    fn with_limits(
        budget: crate::ProofBudget,
        retain_bodies: bool,
        limits: LeanExportLimits,
    ) -> Self {
        let mut kernel = Kernel::with_budget_and_scratch_limit(budget, limits.max_scratch_bytes);
        kernel.enable_declaration_spilling();
        let default_scratch = limits.max_scratch_bytes == spool::DEFAULT_BYTES;
        Self {
            kernel,
            limits,
            names: if default_scratch {
                names::Names::with_count_limit(limits.max_names)
            } else {
                names::Names::with_count_and_scratch_limits(
                    limits.max_names,
                    limits.max_scratch_bytes,
                )
            },
            name_bytes: 0,
            levels: if default_scratch {
                levels::Levels::new()
            } else {
                levels::Levels::with_scratch_limit(limits.max_scratch_bytes)
            },
            expressions: if default_scratch {
                expressions::Expressions::new(false)
            } else {
                expressions::Expressions::with_scratch_limit(false, limits.max_scratch_bytes)
            },
            reports: if default_scratch {
                inventory::Inventory::with_count_limit(limits.max_declarations)
            } else {
                inventory::Inventory::with_limits(limits.max_declarations, limits.max_scratch_bytes)
            },
            checked: if default_scratch {
                checked::Index::with_count_limit(limits.max_declarations)
            } else {
                checked::Index::with_limits(limits.max_declarations, limits.max_scratch_bytes)
            },
            target: String::new(),
            selected: None,
            ambiguous_target: false,
            axioms: BTreeSet::new(),
            dependency_count: 0,
            payload_bytes: 0,
            dependency_bytes: 0,
            transformation_bytes: 0,
            natural_literals: false,
            string_literals: false,
            line: 0,
            input_hash: hash::Sha256::new(),
            digest: None,
            retain_bodies,
            initializers: if default_scratch {
                initializers::Initializers::with_count_limit(retain_bodies, limits.max_declarations)
            } else {
                initializers::Initializers::with_limits(
                    retain_bodies,
                    limits.max_declarations,
                    limits.max_scratch_bytes,
                )
            },
            quotient_stage: 0,
            foundation_policy: LeanFoundationPolicy::Constructive,
        }
    }
    fn reset_budget(&mut self) -> Result<()> {
        // Count even temporary transformations across declarations. A stream
        // cannot retain many individually permitted expanded declarations.
        self.transformation_bytes = self
            .transformation_bytes
            .saturating_add(self.kernel.transformed_bytes);
        if self.transformation_bytes > self.kernel.budget.total_bytes() {
            return Err(format!("export cumulative transformation allocation limit exceeded ({} > {} bytes); no theorem was established", self.transformation_bytes, self.kernel.budget.total_bytes()));
        }
        self.kernel.reset_budget();
        Ok(())
    }
    fn metadata(&self, value: &Json) -> Result<()> {
        let meta = fields(value, &["meta"])?;
        let meta = fields(&meta["meta"], &["lean", "exporter", "format"])?;
        let lean = fields(&meta["lean"], &["version", "githash"])?;
        let exporter = fields(&meta["exporter"], &["name", "version"])?;
        let format = fields(&meta["format"], &["version"])?;
        if string(&lean["version"])? != LEAN_EXPORT_VERSION
            || string(&lean["githash"])? != LEAN_EXPORT_GITHASH
            || string(&exporter["name"])? != "lean4export"
            || string(&exporter["version"])? != LEAN_EXPORT_FORMAT
            || string(&format["version"])? != LEAN_EXPORT_FORMAT
        {
            return Err(
                "export metadata does not match pinned Lean 4.33.1 / lean4export NDJSON 3.1.0"
                    .into(),
            );
        }
        Ok(())
    }
    fn record(&mut self, value: &Json) -> Result<()> {
        let Json::Object(record) = value else {
            return Err("an export record must be an object".into());
        };
        if record.len() == 2 {
            if record.contains_key("in") {
                return self.name_record(value);
            }
            if record.contains_key("il") {
                return self.level_record(value);
            }
            if record.contains_key("ie") {
                return self.expression_record(value);
            }
        }
        if record.len() != 1 {
            return Err(
                "export records require exactly one tagged form and its matching index".into(),
            );
        }
        let (tag, body) = record.iter().next().ok_or("empty export record")?;
        if (1..4).contains(&self.quotient_stage) && tag != "quot" {
            return Err("quotient package must finish before other declarations".into());
        }
        let result = match tag.as_str() {
            "def" | "thm" | "opaque" => self.definition(tag, body),
            "inductive" => self.inductive(body),
            "axiom" => self.axiom_record(body),
            "quot" => self.quotient_record(body),
            "meta" => Err("export metadata is permitted only as the first record".into()),
            _ => Err(format!("unsupported export record '{tag}'")),
        };
        self.expressions.end_record();
        result?;
        if self.kernel.trim_completed_declarations()? {
            self.expressions.sweep_dead();
        }
        Ok(())
    }
    fn name_id(&self, value: &Json) -> Result<usize> {
        let id = index(value)?;
        if id >= self.names.len() {
            return Err("name reference must refer to an earlier record".into());
        }
        Ok(id)
    }
    fn name(&self, value: &Json) -> Result<Name> {
        Ok(self.names.get(self.name_id(value)?)?.into_owned())
    }
    fn level_id(&self, value: &Json) -> Result<usize> {
        let id = index(value)?;
        if id >= self.levels.len() {
            return Err("universe reference must refer to an earlier record".into());
        }
        Ok(id)
    }
    fn level(&self, value: &Json) -> Result<Level> {
        Ok(self.levels.get(self.level_id(value)?)?.into_owned())
    }
    fn expression(&self, value: &Json) -> Result<T> {
        self.expressions
            .get(index(value)?, &self.names, &self.levels)
    }
    fn expression_depth(&self, value: &Json) -> Result<usize> {
        self.expressions.depth(index(value)?)
    }
    fn expression_id(&self, value: &Json) -> Result<usize> {
        let id = index(value)?;
        self.expressions.depth(id)?;
        Ok(id)
    }
    fn universes(&self, value: &Json) -> Result<Vec<String>> {
        let values = array(value, 32)?;
        let mut names = vec![];
        for value in values {
            let name = self.name(value)?;
            if name.depth == 0 || names.contains(&name.key) {
                return Err("universe parameters must be distinct nonanonymous names".into());
            }
            names.push(name.key);
        }
        Ok(names)
    }
    fn definition(&mut self, tag: &str, body: &Json) -> Result<()> {
        let keys = match tag {
            "def" => &[
                "name",
                "levelParams",
                "type",
                "value",
                "all",
                "hints",
                "safety",
            ][..],
            "opaque" => &["name", "levelParams", "type", "value", "all", "isUnsafe"][..],
            _ => &["name", "levelParams", "type", "value", "all"][..],
        };
        let data = fields(body, keys)?;
        let name = self.name(&data["name"])?;
        if tag == "def" {
            if string(&data["safety"])? != "safe" {
                return Err("unsafe and partial definitions cannot enter the proof kernel".into());
            }
            match &data["hints"] {
                Json::String(hint) if matches!(hint.as_str(), "opaque" | "abbrev") => {}
                Json::Object(_) => {
                    let hints = fields(&data["hints"], &["regular"])?;
                    index(&hints["regular"])?;
                }
                _ => return Err("invalid definition reducibility hint".into()),
            }
        } else if tag == "opaque" && boolean(&data["isUnsafe"])? {
            return Err("unsafe opaque declarations are forbidden".into());
        }
        let group = self.name_list(&data["all"], 64)?;
        if !group.iter().any(|member| member.key == name.key)
            || group.iter().map(|n| &n.key).collect::<HashSet<_>>().len() != group.len()
        {
            return Err(
                "declaration provenance 'all' must contain distinct names including itself".into(),
            );
        }
        let universes = self.universes(&data["levelParams"])?;
        let ty = self.expression(&data["type"])?;
        let value = self.expression(&data["value"])?;
        let retained = if self.retain_bodies && tag != "def" {
            Some(initializers::Initializer::Source(
                self.expression_id(&data["value"])?,
            ))
        } else {
            None
        };
        let dependencies = dependencies(&[ty.clone(), value.clone()])?;
        self.dependencies_known(&dependencies, &[])?;
        self.room(1)?;
        self.reset_budget()?;
        let checked = if tag == "opaque" {
            self.kernel
                .opaque_definition(&name.key, universes, ty, value)
        } else {
            self.kernel
                .definition(&name.key, universes, ty, value, tag == "thm")
        };
        checked.map_err(|why| format!("declaration '{}': {why}", name.display))?;
        self.remember_initializer(
            &name,
            if tag == "thm" {
                "theorem"
            } else if tag == "def" {
                "definition"
            } else {
                "opaque"
            },
            dependencies,
            retained,
        )
    }
    fn name_list(&self, value: &Json, limit: usize) -> Result<Vec<Name>> {
        array(value, limit)?
            .iter()
            .map(|value| self.name(value))
            .collect()
    }
    fn dependencies_known(&self, dependencies: &[String], local: &[String]) -> Result<()> {
        for dependency in dependencies {
            if !self.is_checked(dependency)?
                && !local.contains(dependency)
                && !(self.foundation_policy == LeanFoundationPolicy::Lean4
                    && foundation::label(dependency).is_some())
            {
                return Err(format!(
                    "unknown or unchecked declaration dependency '{dependency}'"
                ));
            }
        }
        Ok(())
    }
    fn checked_index(&self, name: &str) -> Result<Option<usize>> {
        self.checked.find(name, &self.reports)
    }
    fn is_checked(&self, name: &str) -> Result<bool> {
        Ok(self.checked_index(name)?.is_some())
    }
    fn room(&self, more: usize) -> Result<()> {
        if self
            .reports
            .len()
            .checked_add(more)
            .is_none_or(|n| n > self.limits.max_declarations)
        {
            return Err("export declaration limit exceeded".into());
        }
        Ok(())
    }
    fn remember(&mut self, name: &Name, kind: &str, dependencies: Vec<String>) -> Result<()> {
        self.remember_initializer(name, kind, dependencies, None)
    }
    fn remember_initializer(
        &mut self,
        name: &Name,
        kind: &str,
        dependencies: Vec<String>,
        initializer: Option<initializers::Initializer>,
    ) -> Result<()> {
        self.dependency_count = self
            .dependency_count
            .checked_add(dependencies.len())
            .ok_or("dependency count overflow")?;
        self.dependency_bytes =
            dependencies
                .iter()
                .try_fold(self.dependency_bytes, |total, name| {
                    total
                        .checked_add(name.len() + 32)
                        .ok_or("dependency byte count overflow")
                })?;
        if self.dependency_count > self.limits.max_dependencies
            || self.dependency_bytes > self.limits.max_dependency_bytes
        {
            return Err("export dependency manifest limit exceeded".into());
        }
        if name.depth == 0 || self.is_checked(&name.key)? {
            return Err("duplicate or anonymous declaration".into());
        }
        // Hash the complete prefix through this record, not just the
        // declaration's JSON IDs. Members of one inductive/quotient record
        // share this immutable digest; primitive records never finalize it.
        let digest = self
            .digest
            .get_or_insert_with(|| hash::hex(&self.input_hash.clone().finish()));
        let index = self.reports.len();
        self.reports.push(LeanDeclarationReport {
            name: name.display.clone(),
            identity: name.key.clone(),
            kind: kind.into(),
            line: self.line,
            sha256: digest.clone(),
            dependencies,
        })?;
        self.initializers.push(index, initializer)?;
        self.checked.insert(&name.key, index)?;
        // Retain only the selector match and the three authorized axiom
        // names. Avoid scanning and decoding the complete paged inventory at
        // EOF; target validation still happens after every record is checked.
        if name.display == self.target || name.key == self.target {
            if self.selected.is_some() {
                self.ambiguous_target = true;
            } else {
                self.selected = Some((name.display.clone(), name.key.clone(), kind.into()));
            }
        }
        if kind == "axiom" {
            self.axioms.insert(name.display.clone());
        }
        Ok(())
    }
}

fn fields<'a>(value: &'a Json, keys: &[&str]) -> Result<&'a BTreeMap<String, Json>> {
    let Json::Object(data) = value else {
        return Err("export form requires an object".into());
    };
    if data.len() != keys.len() || !keys.iter().all(|key| data.contains_key(*key)) {
        return Err(format!(
            "export form requires exactly these fields: {}",
            keys.join(", ")
        ));
    }
    Ok(data)
}
fn array(value: &Json, limit: usize) -> Result<&[Json]> {
    let Json::Array(values) = value else {
        return Err("export form requires an array".into());
    };
    if values.len() > limit {
        return Err("export array limit exceeded".into());
    }
    Ok(values)
}
fn index(value: &Json) -> Result<usize> {
    let Json::Number(value) = value else {
        return Err("export indices require unsigned decimal integers".into());
    };
    if value.is_empty() || !value.bytes().all(|b| b.is_ascii_digit()) {
        return Err("export indices require unsigned decimal integers".into());
    }
    let value: u32 = value.parse().map_err(|_| "export index exceeds u32")?;
    Ok(value as usize)
}
fn string(value: &Json) -> Result<&str> {
    value
        .string()
        .ok_or_else(|| "export form requires a string".into())
}
fn boolean(value: &Json) -> Result<bool> {
    if let Json::Bool(value) = value {
        Ok(*value)
    } else {
        Err("export form requires a boolean".into())
    }
}
fn text_json(value: &str) -> Json {
    Json::String(value.into())
}
#[cfg(test)]
fn number_json(value: u64) -> Json {
    Json::Number(value.to_string())
}
#[cfg(test)]
fn object<const N: usize>(values: [(&str, Json); N]) -> Json {
    Json::Object(values.into_iter().map(|(k, v)| (k.into(), v)).collect())
}

fn dependencies(roots: &[T]) -> Result<Vec<String>> {
    let mut stack = roots.to_vec();
    let mut seen = HashSet::new();
    let mut names = BTreeSet::new();
    let mut bytes = 0usize;
    while let Some(value) = stack.pop() {
        if !seen.insert(Arc::as_ptr(&value) as usize) {
            continue;
        }
        if seen.len() > MAX_EXPRESSIONS {
            return Err("export dependency traversal limit exceeded".into());
        }
        match value.as_ref() {
            Term::QuotType(_, a, r) => stack.extend([a.clone(), r.clone()]),
            Term::QuotMake(_, a, r, x) => stack.extend([a.clone(), r.clone(), x.clone()]),
            Term::QuotLift {
                ty,
                relation,
                target,
                function,
                respect,
                subject,
                ..
            } => stack.extend(
                [ty, relation, target, function, respect, subject]
                    .into_iter()
                    .cloned(),
            ),
            Term::QuotInduct {
                ty,
                relation,
                motive,
                branch,
                subject,
                ..
            } => stack.extend([ty, relation, motive, branch, subject].into_iter().cloned()),
            Term::NatLiteral { family: name, .. } | Term::Global(name, _) => {
                names.insert(name.clone());
            }
            Term::Pi(a, b)
            | Term::Lam(a, b)
            | Term::App(a, b)
            | Term::Sigma(a, b)
            | Term::Refl(a, b) => {
                stack.push(a.clone());
                stack.push(b.clone());
            }
            Term::Let(a, b, c) | Term::Pair(a, b, c) | Term::Eq(a, b, c) => {
                stack.extend([a.clone(), b.clone(), c.clone()])
            }
            Term::First(a) | Term::Second(a) => stack.push(a.clone()),
            Term::Project {
                family, subject, ..
            } => {
                names.insert(family.clone());
                stack.push(subject.clone());
            }
            Term::Ctor {
                family,
                constructor,
                parameters,
                fields,
                ..
            } => {
                names.insert(family.clone());
                names.insert(constructor.clone());
                stack.extend(parameters.iter().chain(fields).cloned());
            }
            Term::Induct {
                family,
                parameters,
                indices,
                motive,
                branches,
                subject,
                ..
            } => {
                names.insert(family.clone());
                stack.extend(parameters.iter().chain(indices).chain(branches).cloned());
                stack.extend([motive.clone(), subject.clone()]);
            }
            Term::MutualInduct {
                family,
                parameters,
                indices,
                cases,
                subject,
                ..
            } => {
                names.insert(family.clone());
                stack.extend(parameters.iter().chain(indices).cloned());
                stack.push(subject.clone());
                for case in cases {
                    names.insert(case.family.clone());
                    stack.push(case.motive.clone());
                    stack.extend(case.branches.iter().cloned());
                }
            }
            Term::NestedInduct {
                family,
                parameters,
                indices,
                cases,
                subject,
                ..
            } => {
                names.insert(family.clone());
                stack.extend(parameters.iter().chain(indices).cloned());
                stack.push(subject.clone());
                for case in cases {
                    stack.extend([case.selector.clone(), case.motive.clone()]);
                    stack.extend(case.branches.iter().cloned());
                }
            }
            Term::EqElim {
                ty,
                left,
                motive,
                base,
                right,
                proof,
            } => stack.extend([
                ty.clone(),
                left.clone(),
                motive.clone(),
                base.clone(),
                right.clone(),
                proof.clone(),
            ]),
            Term::Recur(..) | Term::SelfType | Term::SelfAt(_) => {
                return Err("unexpanded recursive marker in export evidence".into())
            }
            Term::Sort(_) | Term::Var(_) => {}
        }
    }
    for name in &names {
        bytes = bytes.saturating_add(name.len() + 32);
        if bytes > MAX_NAME_BYTES {
            return Err("export dependency byte limit exceeded".into());
        }
    }
    Ok(names.into_iter().collect())
}

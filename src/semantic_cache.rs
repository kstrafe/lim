//! Persistent inference facts, never a certificate that a program is safe.
//!
//! All validation gates still run. The initial dependency boundary is the
//! entire expanded program plus source dependencies, cfg, target and compiler.
//! IDs are serialized by declaration name, never by arena position.
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    fs,
    hash::Hash,
    io::Read,
    path::{Path, PathBuf},
};

use crate::{
    typed_body::{ParameterLoanSummary, ParameterStoreSummary, WordInputRequirement, WordTagGuard},
    typed_flow::ParameterSummary,
    typed_ir::{AggregateId, DeclarationId, Declarations, FieldId, GlobalId, VariantId},
    typed_place::Segment,
    CompileConfig, Item, Program, Type,
};

const MAGIC: &[u8] = b"lim-semantic-v44\0";
const LIMIT: usize = 16 * 1024 * 1024;
type Entries = HashMap<(String, bool), Vec<u8>>;

struct State {
    path: PathBuf,
    key: Vec<u8>,
    digest: u128,
    eligible: HashSet<String>,
    entries: Entries,
    dirty: bool,
}
thread_local! { static CACHE: RefCell<Option<State>> = const { RefCell::new(None) }; }

/// Scoped to final validation, not speculative generator planning. New facts
/// are published only when the whole program has passed semantic validation.
pub(crate) struct Session(Option<State>);
impl Session {
    pub fn begin(
        directory: &Path,
        program: &Program,
        config: &CompileConfig,
        target: &str,
    ) -> Self {
        let _timing = crate::timing::detail("semantic.cache_load");
        let eligible = program
            .items
            .iter()
            .filter_map(|item| match item {
                Item::Function(f)
                    if !f.external
                        && program
                            .declaration_spans
                            .get(&f.name)
                            .is_some_and(|span| span.source_id != 0) =>
                {
                    Some(f.name.clone())
                }
                _ => None,
            })
            .collect::<HashSet<_>>();
        let state = if eligible.is_empty() {
            None
        } else {
            let key = context_key(program, config, target);
            let digest = crate::generator::stable_hash(&key);
            let path = directory
                .join("semantic")
                .join(format!("summaries-{digest:032x}.bin"));
            let entries = load(&path, &key).unwrap_or_default();
            Some(State {
                path,
                key,
                digest,
                eligible,
                entries,
                dirty: false,
            })
        };
        Self(CACHE.with(|slot| slot.replace(state)))
    }

    pub fn publish(&self) {
        let _timing = crate::timing::detail("semantic.cache_publish");
        CACHE.with(|slot| {
            let mut slot = slot.borrow_mut();
            let Some(state) = slot.as_mut().filter(|s| s.dirty) else {
                return;
            };
            let bytes = envelope(&state.key, &state.entries);
            if bytes.len() <= LIMIT
                && fs::create_dir_all(state.path.parent().unwrap()).is_ok()
                && crate::write_output_atomic(&state.path, &bytes).is_ok()
            {
                state.dirty = false;
            }
        });
    }
}
impl Drop for Session {
    fn drop(&mut self) {
        CACHE.with(|slot| {
            slot.replace(self.0.take());
        });
    }
}

pub(crate) fn lookup(
    name: &str,
    contents: bool,
    declarations: &Declarations,
) -> Option<ParameterSummary> {
    CACHE.with(|slot| {
        let slot = slot.borrow();
        let state = slot.as_ref()?;
        if !state.eligible.contains(name) {
            return None;
        }
        let bytes = state.entries.get(&(name.to_owned(), contents));
        let result = bytes.and_then(|bytes| {
            let mut reader = Reader(bytes);
            let result = ParameterSummary::read(&mut reader, declarations)?;
            reader.0.is_empty().then_some(result)
        });
        crate::cache_report::record(
            "semantic-summary",
            &state.path,
            &format!("{name}:{contents}:{:032x}", state.digest),
            if result.is_some() { "hit" } else { "miss" },
        );
        result
    })
}

pub(crate) fn record(
    name: &str,
    contents: bool,
    facts: &ParameterSummary,
    declarations: &Declarations,
) {
    CACHE.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(state) = slot.as_mut().filter(|s| s.eligible.contains(name)) else {
            return;
        };
        let mut bytes = Vec::new();
        facts.write(&mut bytes, declarations);
        state.entries.insert((name.to_owned(), contents), bytes);
        state.dirty = true;
    });
}

fn context_key(program: &Program, config: &CompileConfig, target: &str) -> Vec<u8> {
    fn program_key(program: &Program, bytes: &mut Vec<u8>) {
        put_bytes(bytes, format!("{:?}", program.items).as_bytes());
        put_bytes(bytes, program.source.as_deref().unwrap_or("").as_bytes());
        put_usize(bytes, program.source_files.len());
        for file in &program.source_files {
            put_bytes(bytes, file.path.as_os_str().as_encoded_bytes());
            put_bytes(bytes, file.source.as_bytes());
            put_bytes(bytes, file.import_prefix.as_bytes());
        }
        match &program.generator_validation {
            None => bytes.push(0),
            Some(Ok(witnesses)) => {
                bytes.push(1);
                program_key(witnesses, bytes);
            }
            Some(Err(error)) => {
                bytes.push(2);
                put_bytes(bytes, format!("{error:?}").as_bytes());
            }
        }
    }
    let mut bytes = Vec::new();
    put_bytes(&mut bytes, env!("LIM_BUILD_FINGERPRINT").as_bytes());
    put_bytes(&mut bytes, env!("CARGO_PKG_VERSION").as_bytes());
    put_bytes(&mut bytes, target.as_bytes());
    let mut values = config.values.iter().collect::<Vec<_>>();
    values.sort();
    put_usize(&mut bytes, values.len());
    for (key, value) in values {
        put_bytes(&mut bytes, key.as_bytes());
        put_bytes(&mut bytes, value.as_bytes());
    }
    put_usize(&mut bytes, config.module_paths.len());
    for path in &config.module_paths {
        put_bytes(&mut bytes, path.as_os_str().as_encoded_bytes());
    }
    program_key(program, &mut bytes);
    bytes
}

fn envelope(key: &[u8], entries: &Entries) -> Vec<u8> {
    let mut payload = Vec::new();
    let mut entries = entries.iter().collect::<Vec<_>>();
    entries.sort_by(|a, b| a.0.cmp(b.0));
    put_usize(&mut payload, entries.len());
    for ((name, mode), bytes) in entries {
        put_bytes(&mut payload, name.as_bytes());
        payload.push(u8::from(*mode));
        put_bytes(&mut payload, bytes);
    }
    let mut bytes = MAGIC.to_vec();
    put_bytes(&mut bytes, key);
    bytes.extend_from_slice(&crate::generator::stable_hash(&payload).to_le_bytes());
    put_bytes(&mut bytes, &payload);
    bytes
}

fn load(path: &Path, key: &[u8]) -> Option<Entries> {
    let mut bytes = Vec::new();
    fs::File::open(path)
        .ok()?
        .take((LIMIT + 1) as u64)
        .read_to_end(&mut bytes)
        .ok()?;
    if bytes.len() > LIMIT {
        return None;
    }
    decode_envelope(&bytes, key)
}

fn decode_envelope(bytes: &[u8], key: &[u8]) -> Option<Entries> {
    let mut r = Reader(bytes.strip_prefix(MAGIC)?);
    if r.bytes()? != key {
        return None;
    }
    let checksum = u128::from_le_bytes(r.take(16)?.try_into().ok()?);
    let payload = r.bytes()?;
    if !r.0.is_empty() || checksum != crate::generator::stable_hash(payload) {
        return None;
    }
    let mut r = Reader(payload);
    let count = r.count()?;
    let mut entries = HashMap::new();
    for _ in 0..count {
        let name = r.string()?;
        let mode = r.boolean()?;
        if entries.insert((name, mode), r.bytes()?.to_vec()).is_some() {
            return None;
        }
    }
    r.0.is_empty().then_some(entries)
}

fn put_usize(bytes: &mut Vec<u8>, value: usize) {
    bytes.extend_from_slice(&(value as u64).to_le_bytes());
}
fn put_bytes(bytes: &mut Vec<u8>, value: &[u8]) {
    put_usize(bytes, value.len());
    bytes.extend_from_slice(value);
}
struct Reader<'a>(&'a [u8]);
impl<'a> Reader<'a> {
    fn take(&mut self, length: usize) -> Option<&'a [u8]> {
        let bytes = self.0.get(..length)?;
        self.0 = &self.0[length..];
        Some(bytes)
    }
    fn usize(&mut self) -> Option<usize> {
        usize::try_from(u64::from_le_bytes(self.take(8)?.try_into().ok()?)).ok()
    }
    fn count(&mut self) -> Option<usize> {
        let n = self.usize()?;
        (n <= self.0.len()).then_some(n)
    }
    fn bytes(&mut self) -> Option<&'a [u8]> {
        let n = self.count()?;
        self.take(n)
    }
    fn string(&mut self) -> Option<String> {
        Some(std::str::from_utf8(self.bytes()?).ok()?.to_owned())
    }
    fn boolean(&mut self) -> Option<bool> {
        match self.take(1)?[0] {
            0 => Some(false),
            1 => Some(true),
            _ => None,
        }
    }
}

trait Codec: Sized {
    fn write(&self, bytes: &mut Vec<u8>, d: &Declarations);
    fn read(r: &mut Reader<'_>, d: &Declarations) -> Option<Self>;
}
impl Codec for usize {
    fn write(&self, b: &mut Vec<u8>, _: &Declarations) {
        put_usize(b, *self);
    }
    fn read(r: &mut Reader<'_>, _: &Declarations) -> Option<Self> {
        r.usize()
    }
}
impl Codec for u128 {
    fn write(&self, b: &mut Vec<u8>, _: &Declarations) {
        b.extend_from_slice(&self.to_le_bytes());
    }
    fn read(r: &mut Reader<'_>, _: &Declarations) -> Option<Self> {
        Some(Self::from_le_bytes(r.take(16)?.try_into().ok()?))
    }
}
impl Codec for bool {
    fn write(&self, b: &mut Vec<u8>, _: &Declarations) {
        b.push(u8::from(*self));
    }
    fn read(r: &mut Reader<'_>, _: &Declarations) -> Option<Self> {
        r.boolean()
    }
}
impl<T: Codec> Codec for Option<T> {
    fn write(&self, b: &mut Vec<u8>, d: &Declarations) {
        b.push(u8::from(self.is_some()));
        if let Some(v) = self {
            v.write(b, d);
        }
    }
    fn read(r: &mut Reader<'_>, d: &Declarations) -> Option<Self> {
        Some(if r.boolean()? {
            Some(T::read(r, d)?)
        } else {
            None
        })
    }
}
impl<T: Codec> Codec for Vec<T> {
    fn write(&self, b: &mut Vec<u8>, d: &Declarations) {
        put_usize(b, self.len());
        for v in self {
            v.write(b, d);
        }
    }
    fn read(r: &mut Reader<'_>, d: &Declarations) -> Option<Self> {
        (0..r.count()?).map(|_| T::read(r, d)).collect()
    }
}
impl<A: Codec, B: Codec> Codec for (A, B) {
    fn write(&self, b: &mut Vec<u8>, d: &Declarations) {
        self.0.write(b, d);
        self.1.write(b, d);
    }
    fn read(r: &mut Reader<'_>, d: &Declarations) -> Option<Self> {
        Some((A::read(r, d)?, B::read(r, d)?))
    }
}
impl<K: Codec + Ord + Hash, V: Codec> Codec for HashMap<K, V> {
    fn write(&self, b: &mut Vec<u8>, d: &Declarations) {
        let mut entries = self.iter().collect::<Vec<_>>();
        entries.sort_by(|a, b| a.0.cmp(b.0));
        put_usize(b, entries.len());
        for (k, v) in entries {
            k.write(b, d);
            v.write(b, d);
        }
    }
    fn read(r: &mut Reader<'_>, d: &Declarations) -> Option<Self> {
        let mut result = Self::new();
        for _ in 0..r.count()? {
            if result.insert(K::read(r, d)?, V::read(r, d)?).is_some() {
                return None;
            }
        }
        Some(result)
    }
}
impl<T: Codec + Ord + Hash> Codec for HashSet<T> {
    fn write(&self, b: &mut Vec<u8>, d: &Declarations) {
        let mut values = self.iter().collect::<Vec<_>>();
        values.sort();
        put_usize(b, values.len());
        for v in values {
            v.write(b, d);
        }
    }
    fn read(r: &mut Reader<'_>, d: &Declarations) -> Option<Self> {
        let mut result = Self::new();
        for _ in 0..r.count()? {
            if !result.insert(T::read(r, d)?) {
                return None;
            }
        }
        Some(result)
    }
}
impl Codec for AggregateId {
    fn write(&self, b: &mut Vec<u8>, d: &Declarations) {
        put_bytes(
            b,
            d.declaration_name(DeclarationId::Aggregate(*self))
                .as_bytes(),
        );
    }
    fn read(r: &mut Reader<'_>, d: &Declarations) -> Option<Self> {
        d.aggregate_id(&Type::Named(r.string()?))
    }
}
impl Codec for GlobalId {
    fn write(&self, b: &mut Vec<u8>, d: &Declarations) {
        put_bytes(
            b,
            d.declaration_name(DeclarationId::Global(*self)).as_bytes(),
        );
    }
    fn read(r: &mut Reader<'_>, d: &Declarations) -> Option<Self> {
        d.global_id(&r.string()?)
    }
}
impl Codec for FieldId {
    fn write(&self, b: &mut Vec<u8>, d: &Declarations) {
        self.owner.write(b, d);
        self.index.write(b, d);
    }
    fn read(r: &mut Reader<'_>, d: &Declarations) -> Option<Self> {
        let owner = AggregateId::read(r, d)?;
        let index = r.usize()?;
        d.structs
            .get(d.declaration_name(DeclarationId::Aggregate(owner)))?
            .get(index)?;
        Some(Self { owner, index })
    }
}
impl Codec for VariantId {
    fn write(&self, b: &mut Vec<u8>, d: &Declarations) {
        self.owner.write(b, d);
        self.index.write(b, d);
    }
    fn read(r: &mut Reader<'_>, d: &Declarations) -> Option<Self> {
        let owner = AggregateId::read(r, d)?;
        let index = r.usize()?;
        d.enums
            .get(d.declaration_name(DeclarationId::Aggregate(owner)))?
            .get(index)?;
        Some(Self { owner, index })
    }
}
impl Codec for Segment {
    fn write(&self, b: &mut Vec<u8>, d: &Declarations) {
        match self {
            Self::Dereference => b.push(0),
            Self::Field(id) => {
                b.push(1);
                id.write(b, d);
            }
            Self::ThreadCapture(id, index) => {
                b.push(2);
                id.write(b, d);
                index.write(b, d);
            }
            Self::Tuple(index) => {
                b.push(3);
                index.write(b, d);
            }
            Self::Payload(id, index) => {
                b.push(4);
                id.write(b, d);
                index.write(b, d);
            }
            Self::Index(index) => {
                b.push(5);
                index.write(b, d);
            }
            Self::DynamicIndex => b.push(6),
            Self::SliceHalf(index) => {
                b.push(7);
                index.write(b, d);
            }
            Self::SliceRange { start, end } => {
                b.push(8);
                start.write(b, d);
                end.write(b, d);
            }
            Self::SliceRangeUnknown => b.push(9),
            Self::SliceIndex(index) => {
                b.push(10);
                index.write(b, d);
            }
            Self::SliceDynamicIndex => b.push(11),
        }
    }
    fn read(r: &mut Reader<'_>, d: &Declarations) -> Option<Self> {
        Some(match r.take(1)?[0] {
            0 => Self::Dereference,
            1 => Self::Field(FieldId::read(r, d)?),
            2 => {
                let owner = AggregateId::read(r, d)?;
                let index = r.usize()?;
                d.thread_capture_schemas
                    .get(d.declaration_name(DeclarationId::Aggregate(owner)))?
                    .parameters
                    .get(index)?;
                Self::ThreadCapture(owner, index)
            }
            3 => Self::Tuple(r.usize()?),
            4 => Self::Payload(VariantId::read(r, d)?, r.usize()?),
            5 => Self::Index(u128::read(r, d)?),
            6 => Self::DynamicIndex,
            7 => Self::SliceHalf(r.usize()?),
            8 => Self::SliceRange {
                start: u128::read(r, d)?,
                end: u128::read(r, d)?,
            },
            9 => Self::SliceRangeUnknown,
            10 => Self::SliceIndex(u128::read(r, d)?),
            11 => Self::SliceDynamicIndex,
            _ => return None,
        })
    }
}
macro_rules! record_codec {
    ($ty:ty, $($field:ident),+ $(,)?) => {
        impl Codec for $ty {
            fn write(&self, b: &mut Vec<u8>, d: &Declarations) { $(self.$field.write(b, d);)+ }
            fn read(r: &mut Reader<'_>, d: &Declarations) -> Option<Self> { Some(Self { $($field: Codec::read(r, d)?,)+ }) }
        }
    };
}
record_codec!(
    ParameterLoanSummary,
    fresh_allocation,
    owned_allocation,
    global,
    parameter,
    mutable,
    pinned,
    lifetime_only,
    maybe_absent,
    word_stored,
    word_view_address,
    reborrow,
    referent_projection,
    input_storage,
    storage,
    storage_inputs
);
record_codec!(
    ParameterStoreSummary,
    destination,
    sources,
    definitely_written,
    preserves_bytes,
    variants_definitely_written,
    variants,
    scalars
);
record_codec!(WordTagGuard, address, variant);
record_codec!(crate::typed_body::ScalarReturnFact, storage, values);
record_codec!(crate::typed_body::WordReturnGuarantee, condition, storage);
record_codec!(
    crate::typed_body::WordScalarGuard,
    address,
    by_value,
    values,
    excluded
);
record_codec!(
    WordInputRequirement,
    loan,
    guards,
    scalar_guards,
    unresolved
);
record_codec!(
    ParameterSummary,
    word_inputs,
    scalar_returns,
    word_returns,
    returned,
    stores,
    mutations,
    clears,
    bounds,
    output_stores,
    output_clears
);

#[cfg(test)]
mod tests {
    use super::*;

    fn declarations(source: &str) -> Declarations {
        crate::typecheck::resolve_program_for_analysis(
            &crate::parse_program(source).unwrap(),
            false,
        )
        .unwrap()
    }

    #[test]
    fn unproved_word_entry_obligations_survive_summary_serialization() {
        let d = declarations("(#fn identity (: value (#ref #u64)) (#ref #u64) (#return value))");
        let mut facts = d.flows["identity"].parameter_summary(&d.bodies["identity"], false);
        // A cache hit must retain the distinction between a possible loan
        // lifetime and a definitely initialized concealed word-cell value.
        facts.returned[0].word_stored = true;
        facts.returned[0].maybe_absent = true;
        facts
            .word_returns
            .push(crate::typed_body::WordReturnGuarantee {
                condition: crate::typed_body::ScalarReturnFact {
                    storage: vec![crate::typed_place::Segment::Index(7)],
                    values: vec![1, 2],
                },
                storage: vec![crate::typed_place::Segment::Index(0)],
            });
        let loan = facts.returned[0].clone();
        facts.word_inputs.push(WordInputRequirement {
            loan: loan.clone(),
            guards: Vec::new(),
            scalar_guards: vec![
                crate::typed_body::WordScalarGuard {
                    address: loan.clone(),
                    by_value: false,
                    values: vec![0, u128::MAX],
                    excluded: false,
                },
                crate::typed_body::WordScalarGuard {
                    address: loan,
                    by_value: true,
                    values: vec![1],
                    excluded: true,
                },
            ],
            unresolved: true,
        });
        let mut bytes = Vec::new();
        facts.write(&mut bytes, &d);
        let mut reader = Reader(&bytes);
        let restored = ParameterSummary::read(&mut reader, &d).unwrap();
        assert_eq!(restored, facts);
        assert!(restored.word_inputs[0].unresolved);
        assert!(reader.0.is_empty());
        for end in 0..bytes.len() {
            assert!(ParameterSummary::read(&mut Reader(&bytes[..end]), &d).is_none());
        }
    }

    #[test]
    fn inferred_summaries_round_trip_in_both_transfer_modes() {
        let mut d = declarations(
            "(#struct Holder () (: value (#ref #u64)))
          (#enum Choice () ((Choice.Found Holder) Choice.Missing))
          (#fn choose (: owner (#ref #u64) : flag #bool) Choice
            (#return (#if flag (Choice.Found (#struct-literal Holder (: value owner))) Choice.Missing)))
          (#fn set (: slot (#ref-mut (#ref #u64)) : value (#ref #u64)) ()
            (#deref-set slot value) (#return ()))
          (#fn project (: slot (#ref-mut (#ref-mut #u64))) (#ref-mut #u64)
            (#return (#borrow-mut (#deref (#deref slot)))))
          (#struct Counter () (: pc #u64))
          (#fn make () Counter (#return (#struct-literal Counter (: pc 0u64))))
          (#fn bounded (: flag #bool) Counter
            (#if flag
              (#block (#return (#struct-literal Counter (: pc 0u64))) (#unreachable))
              (#block (#return (#struct-literal Counter (: pc 1u64))) (#unreachable)))
            (#return (#unreachable)))
          (#fn unknown (: flag #bool : pc #u64) Counter
            (#if flag
              (#block (#return (#struct-literal Counter (: pc 0u64))) (#unreachable))
              (#block (#return (#struct-literal Counter (: pc pc))) (#unreachable)))
            (#return (#unreachable)))
          (#fn main () #u64 (#return 42u64))",
        );
        for name in [
            "choose", "set", "project", "make", "bounded", "unknown", "main",
        ] {
            for mode in [false, true] {
                d.bodies.get_mut(name).unwrap().staged_parameter_contents = mode;
                let facts = d.flows[name].parameter_summary(&d.bodies[name], mode);
                if name == "project" {
                    assert!(facts.returned.iter().any(|loan| loan.reborrow));
                }
                if name == "make" || name == "bounded" {
                    assert_eq!(facts.scalar_returns.len(), 1);
                    assert_eq!(
                        facts.scalar_returns[0].values,
                        if name == "make" { vec![0] } else { vec![0, 1] }
                    );
                }
                if name == "unknown" {
                    assert!(
                        facts.scalar_returns.is_empty(),
                        "one unknown return must remove the whole field guarantee"
                    );
                }
                let mut bytes = Vec::new();
                facts.write(&mut bytes, &d);
                let mut r = Reader(&bytes);
                assert_eq!(ParameterSummary::read(&mut r, &d), Some(facts));
                assert!(r.0.is_empty());
                for end in 0..bytes.len() {
                    assert!(ParameterSummary::read(&mut Reader(&bytes[..end]), &d).is_none());
                }
            }
        }
    }

    #[test]
    fn declaration_ids_are_remapped_by_name_not_arena_index() {
        let source = "(#static shared #u64 0u64) (#struct Holder () (: value (#ref #u64)))
          (#enum Choice () ((Choice.Found Holder) Choice.Missing)) (#fn main () #u64 (#return 0u64))";
        let before = declarations(source);
        let after = declarations(&format!(
            "(#static aAA #u64 1u64)
          (#struct AAAHolder () (: value #u64)) (#enum AAAChoice () ((AAAChoice.AAAFound #u64))) {source}"
        ));
        let field = before
            .field_id(&Type::Named("Holder".into()), "value")
            .unwrap();
        let variant = before
            .variant_id(&Type::Named("Choice".into()), "Choice.Found")
            .unwrap();
        let segments = vec![
            Segment::Dereference,
            Segment::Field(field),
            Segment::Tuple(2),
            Segment::Payload(variant, 0),
            Segment::Index(u128::MAX),
            Segment::DynamicIndex,
            Segment::SliceHalf(1),
            Segment::SliceRange { start: 1, end: 8 },
            Segment::SliceRangeUnknown,
            Segment::SliceIndex(3),
            Segment::SliceDynamicIndex,
        ];
        let mut bytes = Vec::new();
        segments.write(&mut bytes, &before);
        let mapped = Vec::<Segment>::read(&mut Reader(&bytes), &after).unwrap();
        assert_eq!(
            mapped[1],
            Segment::Field(
                after
                    .field_id(&Type::Named("Holder".into()), "value")
                    .unwrap()
            )
        );
        assert_eq!(
            mapped[3],
            Segment::Payload(
                after
                    .variant_id(&Type::Named("Choice".into()), "Choice.Found")
                    .unwrap(),
                0
            )
        );
        let global = before.global_id("shared").unwrap();
        bytes.clear();
        global.write(&mut bytes, &before);
        assert_eq!(
            GlobalId::read(&mut Reader(&bytes), &after),
            after.global_id("shared")
        );
    }

    #[test]
    fn envelope_rejects_corruption_truncation_schema_and_context_changes() {
        let entries = HashMap::from([(("f".into(), true), vec![1, 2, 3])]);
        let bytes = envelope(b"context", &entries);
        assert_eq!(decode_envelope(&bytes, b"context"), Some(entries));
        assert!(decode_envelope(&bytes, b"different compiler or dependency").is_none());
        for end in 0..bytes.len() {
            assert!(decode_envelope(&bytes[..end], b"context").is_none());
        }
        for index in 0..bytes.len() {
            let mut damaged = bytes.clone();
            damaged[index] ^= 0x80;
            assert!(
                decode_envelope(&damaged, b"context").is_none(),
                "byte {index}"
            );
        }
        let mut trailing = bytes;
        trailing.push(0);
        assert!(decode_envelope(&trailing, b"context").is_none());
    }

    #[test]
    fn invalid_record_tags_and_unbounded_lengths_are_rejected() {
        let d = declarations("(#fn main () #u64 (#return 0u64))");
        assert!(bool::read(&mut Reader(&[2]), &d).is_none());
        assert!(Segment::read(&mut Reader(&[255]), &d).is_none());
        assert!(Vec::<Segment>::read(&mut Reader(&u64::MAX.to_le_bytes()), &d).is_none());
        assert!(AggregateId::read(&mut Reader(&[255]), &d).is_none());
    }

    #[test]
    fn context_is_cfg_order_independent_but_tracks_all_dependencies_and_witnesses() {
        let mut program = crate::parse_program("(#fn main () #u64 (#return 0u64))").unwrap();
        let mut a = CompileConfig::default();
        a.set("a", "1");
        a.set("b", "2");
        let mut b = CompileConfig::default();
        b.set("b", "2");
        b.set("a", "1");
        let key = context_key(&program, &a, "target");
        assert_eq!(key, context_key(&program, &b, "target"));
        b.set("b", "3");
        assert_ne!(key, context_key(&program, &b, "target"));
        assert_ne!(key, context_key(&program, &a, "another target"));
        b = a.clone();
        b.add_module_path("extra");
        assert_ne!(key, context_key(&program, &b, "target"));
        program.source_files.push(crate::SourceFile {
            import_prefix: String::new(),
            path: "dep.lim".into(),
            source: "dependency".into(),
        });
        let dependency_key = context_key(&program, &a, "target");
        assert_ne!(key, dependency_key);
        program.source_files[0].source.push_str(" changed");
        assert_ne!(dependency_key, context_key(&program, &a, "target"));
        let before_instance = context_key(&program, &a, "target");
        program.source_files[0].import_prefix = "different-instance".into();
        assert_ne!(before_instance, context_key(&program, &a, "target"));
        let before_witness = context_key(&program, &a, "target");
        program.generator_validation = Some(Ok(std::sync::Arc::new(
            crate::parse_program("(#fn witness () #u64 (#return 1u64))").unwrap(),
        )));
        assert_ne!(before_witness, context_key(&program, &a, "target"));
    }
}

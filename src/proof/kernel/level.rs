//! Exact universe arithmetic over all nonnegative assignments. A level is the
//! maximum of affine terms, each enabled by a conjunction of nonzero variables.
//! This represents imax without enumerating universe assignments or sampling.
use super::core::Result;
use std::collections::{BTreeMap, BTreeSet, HashMap};
#[path = "level_source.rs"]
mod source;

pub(super) const LEVEL: u32 = 65_535;
const TERMS: usize = 256;
const GUARDS: usize = 64;
const NORMALIZATION_WORK: usize = 200_000;
const COMPARISON_WORK: usize = 50_000;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Monomial {
    base: Option<String>,
    nonzero: BTreeSet<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub(super) struct Level {
    terms: BTreeMap<Monomial, u32>,
}

fn spend(work: &mut usize) -> Result<()> {
    *work = work
        .checked_sub(1)
        .ok_or("universe arithmetic resource limit exceeded")?;
    Ok(())
}

impl Level {
    /// Conservative local payload accounting for bounded term transformations.
    pub(super) fn memory_weight(&self) -> usize {
        self.terms.keys().fold(0usize, |total, monomial| {
            monomial.nonzero.iter().fold(
                total
                    .saturating_add(96)
                    .saturating_add(monomial.base.as_ref().map_or(0, String::len)),
                |total, name| total.saturating_add(64).saturating_add(name.len()),
            )
        })
    }
    pub fn number(number: u32) -> Result<Self> {
        if number > LEVEL {
            return Err("universe level limit exceeded".into());
        }
        let mut level = Self::default();
        if number != 0 {
            level.insert(
                Monomial {
                    base: None,
                    nonzero: BTreeSet::new(),
                },
                number,
            )?;
        }
        Ok(level)
    }

    pub fn variable(name: String) -> Self {
        Self {
            terms: BTreeMap::from([(
                Monomial {
                    base: Some(name),
                    nonzero: BTreeSet::new(),
                },
                0,
            )]),
        }
    }

    pub fn numeral(&self) -> Option<u32> {
        if self.terms.is_empty() {
            return Some(0);
        }
        if self.terms.len() == 1 {
            let (term, offset) = self.terms.first_key_value()?;
            if term.base.is_none() && term.nonzero.is_empty() {
                return Some(*offset);
            }
        }
        None
    }

    fn insert(&mut self, mut term: Monomial, offset: u32) -> Result<()> {
        if offset > LEVEL {
            return Err("universe level limit exceeded".into());
        }
        if offset == 0 {
            let Some(base) = &term.base else {
                return Ok(());
            };
            // x gated by x>0 is x, including at zero. x+k needs the gate if k>0.
            term.nonzero.remove(base);
        }
        if term.nonzero.len() > GUARDS {
            return Err("universe guard limit exceeded".into());
        }
        self.terms
            .entry(term)
            .and_modify(|old| *old = (*old).max(offset))
            .or_insert(offset);
        if self.terms.len() > TERMS {
            return Err("universe term limit exceeded".into());
        }
        Ok(())
    }

    /// Whether the right monomial alone dominates the left on every assignment.
    fn dominated(left: &Monomial, lo: u32, right: &Monomial, ro: u32) -> bool {
        match &left.base {
            None => {
                right.nonzero.is_subset(&left.nonzero)
                    && u64::from(ro)
                        + u64::from(
                            right
                                .base
                                .as_ref()
                                .is_some_and(|v| left.nonzero.contains(v)),
                        )
                        >= u64::from(lo)
            }
            Some(base) => {
                if right.base.as_ref() != Some(base) || ro < lo {
                    return false;
                }
                right
                    .nonzero
                    .iter()
                    .all(|v| left.nonzero.contains(v) || v == base && lo == 0)
            }
        }
    }

    fn normalize(mut self) -> Result<Self> {
        let terms = self.terms.iter().collect::<Vec<_>>();
        let mut removed = BTreeSet::new();
        let mut work = NORMALIZATION_WORK;
        for (left, lo) in &terms {
            for (right, ro) in &terms {
                spend(&mut work)?;
                if left == right {
                    continue;
                }
                if Self::dominated(left, **lo, right, **ro) {
                    // Keep one representative if different syntactic terms
                    // ever denote the same function; never remove both.
                    if right < left || !Self::dominated(right, **ro, left, **lo) {
                        removed.insert((*left).clone());
                        break;
                    }
                }
            }
        }
        for term in removed {
            self.terms.remove(&term);
        }
        Ok(self)
    }

    pub fn successor(&self) -> Result<Self> {
        self.offset(1)
    }

    fn offset(&self, amount: u32) -> Result<Self> {
        if amount == 0 {
            return Ok(self.clone());
        }
        let mut result = Self::number(amount)?;
        for (term, offset) in &self.terms {
            let offset = offset
                .checked_add(amount)
                .filter(|n| *n <= LEVEL)
                .ok_or("universe level limit exceeded")?;
            result.insert(term.clone(), offset)?;
        }
        result.normalize()
    }

    pub fn maximum(&self, other: &Self) -> Result<Self> {
        let mut result = self.clone();
        for (term, offset) in &other.terms {
            result.insert(term.clone(), *offset)?;
        }
        result.normalize()
    }

    /// Keep this level only where condition is nonzero, otherwise return zero.
    fn gated(&self, condition: &Self) -> Result<Self> {
        if condition.zero() || self.zero() {
            return Self::number(0);
        }
        if condition.positive() {
            return Ok(self.clone());
        }
        let mut result = Self::default();
        let mut work = NORMALIZATION_WORK;
        for (left, offset) in &self.terms {
            for (right, ro) in &condition.terms {
                spend(&mut work)?;
                let mut guarded = left.clone();
                guarded.nonzero.extend(right.nonzero.iter().cloned());
                if *ro == 0 {
                    if let Some(base) = &right.base {
                        guarded.nonzero.insert(base.clone());
                    } else {
                        continue;
                    }
                }
                result.insert(guarded, *offset)?;
            }
        }
        result.normalize()
    }

    pub fn imax(&self, other: &Self) -> Result<Self> {
        other.maximum(&self.gated(other)?)
    }

    pub fn zero(&self) -> bool {
        self.terms.is_empty()
    }

    fn positive(&self) -> bool {
        self.terms
            .iter()
            .any(|(term, offset)| term.nonzero.is_empty() && *offset > 0)
    }

    fn minimum(&self, nonzero: &BTreeSet<String>, work: &mut usize) -> Result<u64> {
        let mut value = 0;
        for (term, offset) in &self.terms {
            spend(work)?;
            if term.nonzero.is_subset(nonzero) {
                let base = term.base.as_ref().is_some_and(|v| nonzero.contains(v));
                value = value.max(u64::from(*offset) + u64::from(base));
            }
        }
        Ok(value)
    }

    pub fn at_most(&self, other: &Self) -> Result<bool> {
        if self == other || self.zero() {
            return Ok(true);
        }
        if let (Some(a), Some(b)) = (self.numeral(), other.numeral()) {
            return Ok(a <= b);
        }
        let mut work = COMPARISON_WORK;
        for (left, offset) in &self.terms {
            if let Some(base) = &left.base {
                let mut positive = left.nonzero.clone();
                positive.insert(base.clone());
                // Hold the other variables at their minima and let base grow.
                // Only an enabled occurrence of that same base can dominate it.
                let mut covered = false;
                for (right, ro) in &other.terms {
                    spend(&mut work)?;
                    if right.base.as_ref() == Some(base)
                        && ro >= offset
                        && right.nonzero.is_subset(&positive)
                    {
                        covered = true;
                        break;
                    }
                }
                if !covered {
                    return Ok(false);
                }
                // At base=0 the affine offset still contributes unless the
                // left term itself requires base to be positive.
                if !left.nonzero.contains(base)
                    && *offset > 0
                    && other.minimum(&left.nonzero, &mut work)? < u64::from(*offset)
                {
                    return Ok(false);
                }
            } else if other.minimum(&left.nonzero, &mut work)? < u64::from(*offset) {
                return Ok(false);
            }
        }
        Ok(true)
    }

    pub fn equivalent(&self, other: &Self) -> Result<bool> {
        Ok(self.at_most(other)? && other.at_most(self)?)
    }

    /// The implication needed by Prop elimination, not just a syntactic test:
    /// whenever self is zero, other must also be zero under the same assignment.
    pub fn zero_implies_zero(&self, other: &Self) -> Result<bool> {
        other.at_most(&other.gated(self)?)
    }

    pub fn substitute(&self, values: &HashMap<String, Level>) -> Result<Self> {
        let lookup = |name: &str| {
            values
                .get(name)
                .ok_or_else(|| format!("undeclared universe parameter '{name}'"))
        };
        let mut result = Self::default();
        for (term, offset) in &self.terms {
            let mut value = match &term.base {
                Some(base) => lookup(base)?.offset(*offset)?,
                None => Self::number(*offset)?,
            };
            for variable in &term.nonzero {
                value = value.gated(lookup(variable)?)?;
            }
            result = result.maximum(&value)?;
        }
        Ok(result)
    }
}

pub(super) fn same_levels(left: &[Level], right: &[Level]) -> Result<bool> {
    if left.len() != right.len() {
        return Ok(false);
    }
    for (left, right) in left.iter().zip(right) {
        if !left.equivalent(right)? {
            return Ok(false);
        }
    }
    Ok(true)
}

#[cfg(test)]
#[path = "level_tests.rs"]
mod tests;

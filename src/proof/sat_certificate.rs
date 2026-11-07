//! Independent unit-propagation checking of SAT refutations. This module does
//! not use the searcher's assignments, watches, decision levels or reasons.
//! Each derived clause is checked against the original CNF and earlier proved
//! clauses. Negating it must give a contradiction using only the supplied hints.
use super::{Error, Result};
use std::sync::Arc;

const VARIABLE_LIMIT: usize = 100_000;
const WORK_LIMIT: usize = 2_000_000;

pub(super) struct Certificate {
    pub variables: usize,
    pub axioms: Arc<[Vec<i32>]>,
    pub steps: Vec<Step>,
}

pub(super) struct Step {
    pub clause: Vec<i32>,
    pub hints: Vec<usize>,
}

struct Checker {
    assignment: Vec<i8>,
    touched: Vec<usize>,
    work: usize,
}

impl Checker {
    fn tick(&mut self, amount: usize) -> Result<()> {
        self.work = self.work.saturating_add(amount);
        if self.work > WORK_LIMIT {
            return Err(Error::limit(
                "SAT certificate checking work budget exhausted",
            ));
        }
        Ok(())
    }

    fn variable(&mut self, literal: i32) -> Result<usize> {
        self.tick(1)?;
        let variable = literal.unsigned_abs() as usize;
        if variable == 0 || variable >= self.assignment.len() {
            return Err(Error::checker("invalid SAT certificate literal"));
        }
        Ok(variable)
    }

    fn assign(&mut self, literal: i32) -> bool {
        let variable = literal.unsigned_abs() as usize;
        let value = if literal > 0 { 1 } else { -1 };
        if self.assignment[variable] == 0 {
            self.assignment[variable] = value;
            self.touched.push(variable);
            false
        } else {
            self.assignment[variable] != value
        }
    }

    fn proves(&mut self, clause: &[i32], hints: &[usize], database: &[&[i32]]) -> Result<()> {
        self.tick(self.touched.len())?;
        for variable in self.touched.drain(..) {
            self.assignment[variable] = 0;
        }
        // Validate even redundant hints or a tautological target. An invalid
        // certificate must not be accepted by an early-success shortcut.
        for &hint in hints {
            self.tick(1)?;
            if hint >= database.len() {
                return Err(Error::checker(
                    "SAT certificate has a forward or invalid clause hint",
                ));
            }
        }
        let mut conflict = false;
        for &literal in clause {
            self.variable(literal)?;
            conflict |= self.assign(-literal);
        }
        for &hint in hints {
            if conflict {
                break;
            }
            let mut unit = None;
            let mut satisfied = false;
            let mut nonunit = false;
            for &literal in database[hint] {
                // Original and previously proved clauses were validated before
                // entering the database; this scan charges their actual use.
                self.tick(1)?;
                let value = self.assignment[literal.unsigned_abs() as usize];
                if value == 0 {
                    if unit.is_some_and(|known| known != literal) {
                        nonunit = true;
                    } else {
                        unit = Some(literal);
                    }
                } else if (value > 0) == (literal > 0) {
                    satisfied = true;
                    break;
                }
            }
            if satisfied {
                continue;
            }
            if nonunit {
                return Err(Error::checker(
                    "SAT certificate hint is not unit under its assumptions",
                ));
            }
            conflict = match unit {
                None => true,
                Some(literal) => self.assign(literal),
            };
        }
        if !conflict {
            return Err(Error::checker(
                "SAT certificate does not derive a contradiction",
            ));
        }
        Ok(())
    }
}

impl Certificate {
    pub(super) fn check_against(&self, variables: usize, original: &Arc<[Vec<i32>]>) -> Result<()> {
        if self.variables != variables || self.axioms != *original {
            return Err(Error::checker(
                "SAT certificate does not match the original query",
            ));
        }
        self.check()
    }

    pub(super) fn check(&self) -> Result<()> {
        let _timing = crate::timing::detail("proof.sat_certificate");
        if self.variables > VARIABLE_LIMIT {
            return Err(Error::limit("SAT certificate variable budget exhausted"));
        }
        // Preflight sizes before allocating the clause database. Proofs and
        // source CNFs remain immutable throughout checking.
        let size = self
            .axioms
            .iter()
            .map(Vec::len)
            .chain(
                self.steps
                    .iter()
                    .map(|step| step.clause.len().saturating_add(step.hints.len())),
            )
            .fold(
                self.axioms.len().saturating_add(self.steps.len()),
                usize::saturating_add,
            );
        if size > WORK_LIMIT {
            return Err(Error::limit("SAT certificate storage budget exhausted"));
        }
        if self.steps.last().is_none_or(|step| !step.clause.is_empty()) {
            return Err(Error::checker(
                "SAT certificate is missing its final empty clause",
            ));
        }
        let mut checker = Checker {
            assignment: vec![0; self.variables + 1],
            touched: Vec::new(),
            work: 0,
        };
        let mut database = Vec::with_capacity(self.axioms.len() + self.steps.len());
        for clause in self.axioms.iter() {
            checker.tick(1)?;
            for &literal in clause {
                checker.variable(literal)?;
            }
            database.push(clause.as_slice());
        }
        for step in &self.steps {
            checker.tick(1)?;
            checker.proves(&step.clause, &step.hints, &database)?;
            database.push(&step.clause);
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "sat_certificate_tests.rs"]
mod tests;

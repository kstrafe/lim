use super::*;
use crate::proof::ProofOutcome;

fn cert(variables: usize, axioms: Vec<Vec<i32>>, steps: Vec<Step>) -> Certificate {
    Certificate {
        variables,
        axioms: axioms.into(),
        steps,
    }
}

fn step(clause: &[i32], hints: &[usize]) -> Step {
    Step {
        clause: clause.to_vec(),
        hints: hints.to_vec(),
    }
}

fn outcome(certificate: &Certificate) -> ProofOutcome {
    certificate
        .check()
        .unwrap_err()
        .diagnostic_code()
        .proof_outcome()
        .unwrap()
}

fn invalid(certificate: &Certificate) {
    assert_eq!(outcome(certificate), ProofOutcome::CheckerError);
}

fn four_clause_unsat() -> Certificate {
    cert(
        2,
        vec![vec![1, 2], vec![1, -2], vec![-1, 2], vec![-1, -2]],
        vec![step(&[1], &[0, 1]), step(&[], &[4, 2, 3])],
    )
}

#[test]
fn checks_hinted_resolution_chain() {
    four_clause_unsat().check().unwrap();
}

#[test]
fn a_valid_refutation_of_another_query_is_not_evidence_for_this_query() {
    let certificate = cert(1, vec![vec![1], vec![-1]], vec![step(&[], &[0, 1])]);
    certificate.check().unwrap();
    let original: Arc<[Vec<i32>]> = vec![vec![1]].into();
    let error = certificate.check_against(1, &original).unwrap_err();
    assert_eq!(
        error.diagnostic_code().proof_outcome(),
        Some(ProofOutcome::CheckerError)
    );
    let same: Arc<[Vec<i32>]> = vec![vec![1], vec![-1]].into();
    certificate.check_against(1, &same).unwrap();
    let error = certificate.check_against(2, &same).unwrap_err();
    assert_eq!(
        error.diagnostic_code().proof_outcome(),
        Some(ProofOutcome::CheckerError)
    );
}

#[test]
fn accepts_positive_unit_contradiction_and_empty_axiom() {
    cert(1, vec![vec![1], vec![-1]], vec![step(&[], &[0, 1])])
        .check()
        .unwrap();
    cert(0, vec![vec![]], vec![step(&[], &[0])])
        .check()
        .unwrap();
}

#[test]
fn handles_duplicate_and_tautological_axiom_literals() {
    cert(
        2,
        vec![vec![1, 1], vec![-1, 2], vec![-1, -2]],
        vec![step(&[1], &[0, 0]), step(&[], &[3, 1, 2])],
    )
    .check()
    .unwrap();
    cert(
        2,
        vec![vec![1, -1], vec![2], vec![-2]],
        vec![step(&[], &[1, 2])],
    )
    .check()
    .unwrap();
    invalid(&cert(1, vec![vec![1, -1]], vec![step(&[], &[0])]));
}

#[test]
fn accepts_tautological_target_but_validates_all_its_hints() {
    cert(
        1,
        vec![vec![1], vec![-1]],
        vec![step(&[1, -1], &[]), step(&[], &[0, 1])],
    )
    .check()
    .unwrap();
    invalid(&cert(1, vec![], vec![step(&[1, -1], &[]), step(&[], &[0])]));
    invalid(&cert(
        1,
        vec![],
        vec![step(&[1, -1], &[0]), step(&[], &[0])],
    ));
}

#[test]
fn rejects_tampered_learned_clause_and_missing_final_empty_clause() {
    invalid(&cert(
        2,
        vec![vec![1, 2], vec![1, -2], vec![-1, 2], vec![-1, -2]],
        vec![step(&[-1], &[0, 1]), step(&[], &[4, 2, 3])],
    ));
    invalid(&cert(
        1,
        vec![vec![1], vec![-1]],
        vec![step(&[], &[0, 1]), step(&[1], &[])],
    ));
}

#[test]
fn rejects_missing_wrong_future_and_nonunit_hints() {
    invalid(&cert(
        2,
        vec![vec![1, 2], vec![1, -2], vec![-1, 2], vec![-1, -2]],
        vec![step(&[1], &[0]), step(&[], &[4, 2, 3])],
    ));
    invalid(&cert(1, vec![vec![1], vec![-1]], vec![step(&[], &[1, 99])]));
    invalid(&cert(
        1,
        vec![vec![1], vec![-1]],
        vec![step(&[], &[2]), step(&[], &[0, 1])],
    ));
    invalid(&cert(2, vec![vec![1, 2]], vec![step(&[], &[0])]));
}

#[test]
fn rejects_refutation_of_satisfiable_cnf() {
    invalid(&cert(1, vec![vec![1]], vec![step(&[], &[0])]));
    invalid(&cert(2, vec![vec![1, 2]], vec![step(&[], &[0])]));
    // Proving [1] assumes -1 only for that step. The final empty clause
    // cannot inherit that temporary assumption and refute a satisfiable CNF.
    invalid(&cert(
        1,
        vec![vec![1]],
        vec![step(&[1], &[0]), step(&[], &[0, 1])],
    ));
}

#[test]
fn validates_zero_minimum_and_out_of_range_literals_everywhere() {
    for literal in [0, i32::MIN, 2, -2] {
        invalid(&cert(1, vec![vec![literal]], vec![step(&[], &[0])]));
        invalid(&cert(
            1,
            vec![],
            vec![step(&[literal, literal], &[]), step(&[], &[0])],
        ));
    }
}

#[test]
fn reports_variable_and_storage_limits_as_resource_limits() {
    let too_many_variables = cert(100_001, vec![vec![1], vec![-1]], vec![step(&[], &[0, 1])]);
    assert_eq!(outcome(&too_many_variables), ProofOutcome::ResourceLimit);
    let too_many_literals = cert(1, vec![vec![1; 2_000_001]], vec![step(&[], &[0])]);
    assert_eq!(outcome(&too_many_literals), ProofOutcome::ResourceLimit);
}

#[test]
fn repeated_valid_hints_cannot_bypass_the_replay_work_budget() {
    let mut long = vec![2; 1024];
    long.push(1);
    let mut hints = vec![0];
    hints.extend(std::iter::repeat_n(1, 2048));
    hints.push(2);
    let certificate = cert(2, vec![vec![1], long, vec![-1]], vec![step(&[], &hints)]);
    assert_eq!(outcome(&certificate), ProofOutcome::ResourceLimit);
}

#[test]
fn seeded_fabricated_certificates_cannot_refute_any_brute_force_model() {
    fn next(seed: &mut u64, bound: usize) -> usize {
        *seed ^= *seed << 13;
        *seed ^= *seed >> 7;
        *seed ^= *seed << 17;
        (*seed as usize) % bound
    }
    fn random_clause(seed: &mut u64, variables: usize) -> Vec<i32> {
        (0..next(seed, 4))
            .map(|_| {
                let variable = next(seed, variables) as i32 + 1;
                if next(seed, 2) == 0 {
                    variable
                } else {
                    -variable
                }
            })
            .collect()
    }
    let mut seed = 0xc3a7_9211_d067_4e5bu64;
    let mut accepted = 0;
    let mut satisfiable = 0;
    for _ in 0..4096 {
        let variables = next(&mut seed, 4) + 1;
        let axioms = (0..next(&mut seed, 7))
            .map(|_| random_clause(&mut seed, variables))
            .collect::<Vec<_>>();
        let has_model = (0..1usize << variables).any(|model| {
            axioms.iter().all(|clause| {
                clause.iter().any(|&literal| {
                    (model & (1 << (literal.unsigned_abs() - 1)) != 0) == (literal > 0)
                })
            })
        });
        satisfiable += usize::from(has_model);
        let count = next(&mut seed, 4) + 1;
        let steps = (0..count)
            .map(|index| {
                let clause = if index + 1 == count {
                    Vec::new()
                } else {
                    random_clause(&mut seed, variables)
                };
                let hints = (0..next(&mut seed, 8))
                    .map(|_| next(&mut seed, axioms.len() + index + 2))
                    .collect();
                Step { clause, hints }
            })
            .collect();
        let certificate = cert(variables, axioms, steps);
        if certificate.check().is_ok() {
            accepted += 1;
            assert!(!has_model, "accepted a refutation of a satisfiable formula");
        }
    }
    assert!(accepted > 0, "campaign must exercise accepted derivations");
    assert!(
        satisfiable > 0,
        "campaign must exercise satisfiable source formulas"
    );
}

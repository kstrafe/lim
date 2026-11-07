//! Structured proof outcomes are assigned at failure sites, never recovered
//! from the wording of a diagnostic or a user-provided identifier.
use crate::DiagnosticCode;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProofOutcome {
    Proved,
    Counterexample,
    Unsupported,
    ResourceLimit,
    Invalid,
    InductionFailure,
    ContractFailure,
    CheckerError,
}

impl ProofOutcome {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Proved => "proved",
            Self::Counterexample => "counterexample",
            Self::Unsupported => "unsupported",
            Self::ResourceLimit => "resource_limit",
            Self::Invalid => "invalid",
            Self::InductionFailure => "induction_failure",
            Self::ContractFailure => "contract_failure",
            Self::CheckerError => "checker_error",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Error {
    kind: Failure,
    message: String,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Failure {
    Counterexample,
    Unsupported,
    ResourceLimit,
    Invalid,
    InductionFailure,
    ContractFailure,
    CheckerError,
}

impl Error {
    pub fn invalid(message: impl Into<String>) -> Self {
        Self {
            kind: Failure::Invalid,
            message: message.into(),
        }
    }
    pub fn unsupported(message: impl Into<String>) -> Self {
        Self {
            kind: Failure::Unsupported,
            message: message.into(),
        }
    }
    pub fn limit(message: impl Into<String>) -> Self {
        Self {
            kind: Failure::ResourceLimit,
            message: message.into(),
        }
    }
    pub fn counterexample(message: impl Into<String>) -> Self {
        Self {
            kind: Failure::Counterexample,
            message: message.into(),
        }
    }
    pub fn induction(message: impl Into<String>) -> Self {
        Self {
            kind: Failure::InductionFailure,
            message: message.into(),
        }
    }
    pub fn checker(message: impl Into<String>) -> Self {
        Self {
            kind: Failure::CheckerError,
            message: message.into(),
        }
    }
    pub fn contract(message: impl Into<String>) -> Self {
        Self {
            kind: Failure::ContractFailure,
            message: message.into(),
        }
    }
    pub fn context(mut self, context: impl AsRef<str>) -> Self {
        self.message.push_str("; ");
        self.message.push_str(context.as_ref());
        self
    }
    pub fn diagnostic_code(&self) -> DiagnosticCode {
        match self.kind {
            Failure::Counterexample => DiagnosticCode::ProofCounterexample,
            Failure::Unsupported => DiagnosticCode::ProofUnsupported,
            Failure::ResourceLimit => DiagnosticCode::ProofResourceLimit,
            Failure::Invalid => DiagnosticCode::ProofInvalid,
            Failure::InductionFailure => DiagnosticCode::ProofInduction,
            Failure::ContractFailure => DiagnosticCode::ProofContract,
            Failure::CheckerError => DiagnosticCode::ProofInternal,
        }
    }
}

impl From<String> for Error {
    fn from(message: String) -> Self {
        Self::invalid(message)
    }
}
impl From<&str> for Error {
    fn from(message: &str) -> Self {
        Self::invalid(message)
    }
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let prefix = match self.kind {
            Failure::Counterexample => "disproved",
            Failure::Invalid => "invalid proposition",
            _ => "unproved",
        };
        write!(f, "{prefix}: {}", self.message)
    }
}
impl std::error::Error for Error {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn context_and_english_messages_cannot_change_the_failure_kind() {
        let message = "disproved unsupported SAT budget exhausted proved";
        for (error, outcome) in [
            (Error::invalid(message), ProofOutcome::Invalid),
            (Error::unsupported(message), ProofOutcome::Unsupported),
            (Error::limit(message), ProofOutcome::ResourceLimit),
            (Error::counterexample(message), ProofOutcome::Counterexample),
            (Error::induction(message), ProofOutcome::InductionFailure),
            (Error::contract(message), ProofOutcome::ContractFailure),
            (Error::checker(message), ProofOutcome::CheckerError),
        ] {
            let error = error.context("while checking a different budget");
            assert_eq!(error.diagnostic_code().proof_outcome(), Some(outcome));
            assert!(error.to_string().contains(message));
        }
    }
}

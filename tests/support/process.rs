//! Launch freshly written executables despite transient inherited writers.
#![allow(dead_code)]

use std::{
    io,
    process::{Child, Command, ExitStatus},
    thread,
    time::{Duration, Instant},
};

/// Closing our writer is not enough on Linux: a concurrent fork can retain a
/// copy until that child execs. CLOEXEC does not close it at fork, and rename
/// does not change the inode's write count. Retry only a failed launch, never a
/// child's exit status, and keep retries inside the caller's existing budget.
pub fn spawn(command: &mut Command, budget: Duration) -> io::Result<Child> {
    retry_spawn(|| command.spawn(), budget)
}

pub fn status(command: &mut Command) -> io::Result<ExitStatus> {
    spawn(command, Duration::from_secs(5))?.wait()
}

fn retry_spawn<T>(mut attempt: impl FnMut() -> io::Result<T>, budget: Duration) -> io::Result<T> {
    let started = Instant::now();
    loop {
        match attempt() {
            Err(error)
                if cfg!(target_os = "linux")
                    && error.kind() == io::ErrorKind::ExecutableFileBusy =>
            {
                let remaining = budget.saturating_sub(started.elapsed());
                if remaining.is_zero() {
                    return Err(error);
                }
                thread::sleep(remaining.min(Duration::from_millis(1)));
            }
            result => return result,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn other_errors_are_not_retried() {
        let mut attempts = 0;
        let error = retry_spawn::<()>(
            || {
                attempts += 1;
                Err(io::Error::from(io::ErrorKind::PermissionDenied))
            },
            Duration::from_secs(1),
        )
        .unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::PermissionDenied);
        assert_eq!(attempts, 1);
    }

    #[test]
    fn persistent_busy_error_obeys_budget() {
        let mut attempts = 0;
        let error = retry_spawn::<()>(
            || {
                attempts += 1;
                Err(io::Error::from(io::ErrorKind::ExecutableFileBusy))
            },
            Duration::ZERO,
        )
        .unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::ExecutableFileBusy);
        assert_eq!(attempts, 1);
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn only_failed_launches_are_retried() {
        let mut attempts = 0;
        let status = retry_spawn(
            || {
                attempts += 1;
                if attempts < 3 {
                    Err(io::Error::from(io::ErrorKind::ExecutableFileBusy))
                } else {
                    Ok(42)
                }
            },
            Duration::from_secs(5),
        )
        .unwrap();
        assert_eq!(status, 42);
        assert_eq!(attempts, 3);
    }
}

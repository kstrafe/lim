mod support;
use std::{process::Command, time::Duration};

#[test]
fn output_is_drained_and_bounded_on_both_streams() {
    let output = support::run(
        Command::new("sh").args([
            "-c",
            "head -c 100000 /dev/zero; head -c 100000 /dev/zero >&2",
        ]),
        Duration::from_secs(3),
        110000,
    )
    .unwrap();
    assert!(output.0.success());
    assert_eq!(output.1.len(), 100000);
    assert_eq!(output.2.len(), 100000);
    let error = support::run(
        Command::new("sh").args(["-c", "echo marker >&2; yes noisy"]),
        Duration::from_secs(3),
        1024,
    )
    .unwrap_err();
    assert!(error.contains("output limit exceeded"));
    assert!(error.len() < 2400);
}

#[test]
fn timeout_and_parent_exit_close_descendant_pipes() {
    let error = support::run(
        Command::new("sh").args(["-c", "sleep 30 & wait"]),
        Duration::from_millis(50),
        1024,
    )
    .unwrap_err();
    assert!(error.contains("timeout"));
    let started = std::time::Instant::now();
    let output = support::run(
        Command::new("sh").args(["-c", "sleep 30 & exit 0"]),
        Duration::from_secs(1),
        1024,
    )
    .unwrap();
    assert!(output.0.success());
    assert!(started.elapsed() < Duration::from_secs(2));
}

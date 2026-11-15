mod support;
use std::{fs, process::Command, time::Duration};

#[test]
fn fieldless_variant_returns_from_a_payload_enum() {
    let scratch = support::Scratch::new("fieldless-return");
    let input = scratch.path().join("main.lim");
    let binary = scratch.path().join("program");
    fs::write(
        &input,
        "#enum Answer () ((Answer.Value #u64) Answer.Empty)
#fn empty {
  #params = ();
  #returns = Answer;
  #body = ( (#return Answer.Empty)
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#return (#match (#call empty ())
            (#case Answer.Empty 42u64) (#case (Answer.Value value) value)))\n  );\n}\n",
    )
    .unwrap();
    let (status, _, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(input)
            .arg("-o")
            .arg(&binary),
        Duration::from_secs(20),
        65536,
    )
    .unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    let (status, _, _) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
    assert_eq!(status.code(), Some(42));
}

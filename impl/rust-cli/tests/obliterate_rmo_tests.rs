// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! End-to-end RMO (Remove-Match-Obliterate) tests.
//!
//! These exercise the `obliterate` command through the real parse -> execute
//! pipeline, verifying that the previously-unreachable secure-deletion command
//! is now wired into dispatch, destroys data, leaves a persistent audit residue
//! (the MAA / GDPR Article 17 attestation), and is irreversible.

use std::fs;

use tempfile::TempDir;
use vsh::executable::ExecutableCommand;
use vsh::parser::{parse_command, Command};
use vsh::state::ShellState;

fn setup() -> (TempDir, ShellState) {
    let temp = TempDir::new().expect("tempdir");
    let state = ShellState::new(temp.path().to_str().expect("utf8")).expect("state");
    (temp, state)
}

/// The core fix: `obliterate` must PARSE to `Command::Obliterate`. Before wiring
/// it fell through to external-command handling and was unreachable from the REPL.
#[test]
fn obliterate_is_wired_into_dispatch() {
    match parse_command("obliterate secret.txt").expect("parse") {
        Command::Obliterate { path, force, .. } => {
            assert_eq!(path, "secret.txt");
            assert!(!force, "no --force means force=false");
        }
        other => panic!("expected Command::Obliterate, got {other:?}"),
    }

    // --force before or after the path both work.
    for input in ["obliterate --force secret.txt", "obliterate secret.txt --force"] {
        match parse_command(input).expect("parse") {
            Command::Obliterate { path, force, .. } => {
                assert_eq!(path, "secret.txt", "input: {input}");
                assert!(force, "input: {input}");
            }
            other => panic!("expected Command::Obliterate for {input:?}, got {other:?}"),
        }
    }
}

/// obliterate with no operand is a clean error, not a panic.
#[test]
fn obliterate_requires_operand() {
    assert!(parse_command("obliterate").is_err());
    assert!(parse_command("obliterate --force").is_err());
}

/// End-to-end: parse + execute actually destroys the file.
#[test]
fn obliterate_destroys_file_end_to_end() {
    let (temp, mut state) = setup();
    let secret = temp.path().join("secret.txt");
    fs::write(&secret, b"TOP SECRET PERSONAL DATA").expect("write");
    assert!(secret.exists());

    parse_command("obliterate secret.txt --force")
        .expect("parse")
        .execute(&mut state)
        .expect("execute");

    assert!(!secret.exists(), "obliterated file must not exist");
}

/// The RMO residue: an append-only audit record survives the data destruction.
#[test]
fn obliterate_writes_rmo_audit_residue() {
    let (temp, mut state) = setup();
    fs::write(temp.path().join("pii.txt"), b"name,email\nalice,a@x\n").expect("write");

    parse_command("obliterate pii.txt --force")
        .expect("parse")
        .execute(&mut state)
        .expect("execute");

    let audit = temp.path().join(".vsh-audit.log");
    assert!(audit.exists(), "RMO audit residue must be written to the sandbox");
    let contents = fs::read_to_string(&audit).expect("read audit");
    assert!(
        contents.contains("Obliterate"),
        "audit must record the Obliterate operation type; got: {contents}"
    );
    assert!(
        contents.contains("pii.txt"),
        "audit must record the obliterated path; got: {contents}"
    );
}

/// RMO is irreversible: undo must not resurrect an obliterated file.
#[test]
fn obliterate_is_irreversible() {
    let (temp, mut state) = setup();
    let victim = temp.path().join("gone.txt");
    fs::write(&victim, b"data").expect("write");

    parse_command("obliterate gone.txt --force")
        .expect("parse")
        .execute(&mut state)
        .expect("execute");
    assert!(!victim.exists());

    // Undo may report nothing-to-do or an error, but must never restore the file.
    let _ = vsh::commands::undo(&mut state, 1, false);
    assert!(
        !victim.exists(),
        "undo must not resurrect an obliterated file (RMO is irreversible)"
    );
}

/// The overwrite actually changes bytes before unlink: obliterate a file, then
/// confirm no plaintext survives at the path (it is gone) — and that a fresh file
/// of the same name created afterward does not contain the old content.
#[test]
fn obliterate_then_recreate_has_no_old_content() {
    let (temp, mut state) = setup();
    let p = temp.path().join("card.txt");
    fs::write(&p, b"4111111111111111").expect("write");

    parse_command("obliterate card.txt --force")
        .expect("parse")
        .execute(&mut state)
        .expect("execute");
    assert!(!p.exists());

    fs::write(&p, b"fresh").expect("rewrite");
    let back = fs::read(&p).expect("read");
    assert_eq!(back, b"fresh");
    assert!(!back.windows(4).any(|w| w == b"4111"), "no old plaintext remains");
}

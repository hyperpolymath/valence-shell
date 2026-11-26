// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! Regressions for review findings on the containment work: the inherited
//! `PWD`, the append baseline after a truncation in the same command, and
//! history written before paths were relative to the session root.

#![cfg(unix)]

use std::fs;
use std::path::Path;
use std::process::{Command, Output, Stdio};

fn shell(root: &Path, script: &str) -> Output {
    Command::new(env!("CARGO_BIN_EXE_vsh"))
        .arg("-r")
        .arg(root)
        .arg("-c")
        .arg(script)
        .current_dir(std::env::temp_dir())
        .env("NO_COLOR", "1")
        .env_remove("RUST_BACKTRACE")
        .stdin(Stdio::null())
        .output()
        .expect("start the built shell")
}

#[test]
fn started_elsewhere_the_child_sees_the_session_root_as_pwd() {
    let root = tempfile::tempdir().unwrap();
    let root_path = fs::canonicalize(root.path()).unwrap();
    let out = shell(&root_path, "env");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let line = format!("PWD={}", root_path.display());
    assert!(stdout.lines().any(|l| l == line), "env did not show {line}");
}

#[test]
fn undoing_an_append_after_a_truncation_in_one_command_leaves_the_truncated_state() {
    let root = tempfile::tempdir().unwrap();
    let root_path = fs::canonicalize(root.path()).unwrap();
    let f = root_path.join("f");
    fs::write(&f, "0123456789").unwrap();
    // One `undo` takes back the append only. The file is then as the
    // truncation left it (empty), not padded back to its old length.
    shell(&root_path, "echo hi > f 2>> f; undo");
    assert_eq!(fs::read(&f).unwrap(), b"");
    shell(&root_path, "undo");
    assert_eq!(fs::read(&f).unwrap(), b"0123456789");
}

#[test]
fn history_from_before_the_root_relative_format_is_not_applied() {
    let root = tempfile::tempdir().unwrap();
    let root_path = fs::canonicalize(root.path()).unwrap();
    fs::write(root_path.join("keep"), "x").unwrap();
    // An old record: `touch keep` made in a subdirectory would hold "keep".
    let old = r#"{"history":[{"id":"00000000-0000-4000-8000-000000000001","op_type":"CreateFile","path":"keep","undo_data":null,"timestamp":"2026-01-01T00:00:00Z","executed":true,"undone":false,"by":null}],"transactions":[],"active_transaction":null}"#;
    fs::write(root_path.join(".vsh_state.json"), old).unwrap();
    shell(&root_path, "undo");
    assert!(root_path.join("keep").exists(), "legacy record was applied");
    assert!(root_path.join(".vsh_state.json.legacy").exists());
}

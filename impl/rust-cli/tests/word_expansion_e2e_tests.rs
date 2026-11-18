// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! End-to-end tests for argument glob expansion, run through the `vsh` binary.
//!
//! Before the word-expansion stage (`vsh::word`), globs were expanded only
//! for external commands that also had a redirection: `wc -c *.txt` passed
//! `*.txt` to `wc`, pipelines and `echo` never expanded, and quoted patterns
//! reached the program with a stray backslash (`echo '*.txt'` printed
//! `\*.txt`). Each test runs `vsh -c` in a directory holding `a.txt`,
//! `b.txt` and `c.log`.

use std::path::Path;
use std::process::{Command, Output};

use tempfile::TempDir;

fn fixture() -> TempDir {
    let dir = TempDir::new().unwrap();
    for name in ["a.txt", "b.txt", "c.log"] {
        std::fs::write(dir.path().join(name), b"").unwrap();
    }
    dir
}

fn vsh(dir: &Path, script: &str) -> Output {
    Command::new(env!("CARGO_BIN_EXE_vsh"))
        .arg("-c")
        .arg(script)
        .current_dir(dir)
        .output()
        .expect("vsh runs")
}

fn stdout(dir: &Path, script: &str) -> String {
    let out = vsh(dir, script);
    assert!(
        out.status.success(),
        "`{script}` failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).unwrap()
}

#[test]
fn external_command_without_redirect_gets_the_matches() {
    let dir = fixture();
    assert_eq!(
        stdout(dir.path(), "wc -c *.txt"),
        "0 a.txt\n0 b.txt\n0 total\n"
    );
}

#[test]
fn external_command_with_redirect_gets_the_matches() {
    let dir = fixture();
    stdout(dir.path(), "wc -c *.txt > out.wc");
    assert_eq!(
        std::fs::read_to_string(dir.path().join("out.wc")).unwrap(),
        "0 a.txt\n0 b.txt\n0 total\n"
    );
}

#[test]
fn every_pipeline_stage_gets_the_matches() {
    let dir = fixture();
    assert_eq!(stdout(dir.path(), "ls *.txt | wc -l").trim(), "2");
    assert_eq!(stdout(dir.path(), "printf '%s\\n' *.log | cat"), "c.log\n");
}

#[test]
fn builtin_echo_gets_the_matches() {
    let dir = fixture();
    assert_eq!(stdout(dir.path(), "echo *.txt"), "a.txt b.txt\n");
    assert_eq!(stdout(dir.path(), "echo -n *.log"), "c.log");
}

#[test]
fn quoted_patterns_stay_literal_without_a_backslash() {
    let dir = fixture();
    assert_eq!(stdout(dir.path(), "echo '*.txt'"), "*.txt\n");
    assert_eq!(stdout(dir.path(), "echo \"*.txt\""), "*.txt\n");
    assert_eq!(stdout(dir.path(), "echo \\*.txt"), "*.txt\n");
    assert_eq!(
        stdout(dir.path(), "printf '%s\\n' '*.txt' \"*.txt\" \\*.txt"),
        "*.txt\n*.txt\n*.txt\n"
    );
    assert_eq!(
        stdout(dir.path(), "printf '%s\\n' '*.txt' | cat"),
        "*.txt\n"
    );
}

#[test]
fn a_pattern_that_matches_nothing_is_passed_literally() {
    let dir = fixture();
    assert_eq!(stdout(dir.path(), "echo *.none"), "*.none\n");
    assert_eq!(stdout(dir.path(), "printf '%s\\n' *.none"), "*.none\n");
    assert_eq!(
        stdout(dir.path(), "printf '%s\\n' *.none > out.none; cat out.none"),
        "*.none\n"
    );
}

#[test]
fn a_partly_quoted_word_globs_only_its_unquoted_part() {
    let dir = fixture();
    std::fs::write(dir.path().join("*x.txt"), b"").unwrap();
    std::fs::write(dir.path().join("ax.txt"), b"").unwrap();
    assert_eq!(stdout(dir.path(), "echo '*'x.*"), "*x.txt\n");
    assert_eq!(stdout(dir.path(), "echo *x.*"), "*x.txt ax.txt\n");
}

#[test]
fn braces_expand_unquoted_and_stay_literal_quoted() {
    let dir = fixture();
    assert_eq!(stdout(dir.path(), "echo a{1,2} '{a,b}'"), "a1 a2 {a,b}\n");
}

#[test]
fn function_arguments_get_the_matches() {
    let dir = fixture();
    assert_eq!(
        stdout(dir.path(), "f() { echo \"$#:$1:$2\"; }; f *.txt"),
        "2:a.txt:b.txt\n"
    );
}

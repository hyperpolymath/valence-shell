// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! The shell must not add a fixed wait to every program it runs.
//!
//! It used to check on a running child every 50 ms, so each external command
//! took at least that long: a hundred of them took over five seconds, against
//! about 0.15 s in bash. These tests run the built shell.

use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

fn vsh(dir: &std::path::Path, script: &str) -> (i32, Duration) {
    let started = Instant::now();
    let status = Command::new(env!("CARGO_BIN_EXE_vsh"))
        .arg("-r")
        .arg(dir)
        .arg("-c")
        .arg(script)
        .current_dir(dir)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .expect("start the built shell");
    (status.code().unwrap_or(-1), started.elapsed())
}

#[test]
fn a_hundred_short_programs_are_not_each_held_for_a_fixed_interval() {
    let dir = tempfile::tempdir().expect("temporary directory");
    let words: Vec<String> = (1..=100).map(|i| i.to_string()).collect();
    let script = format!("for i in {}; do sleep 0; done", words.join(" "));

    let (code, took) = vsh(dir.path(), &script);

    assert_eq!(code, 0, "the loop should succeed");
    // A fixed 50 ms wait per program gives 5 s. The limit leaves room for a
    // slow machine while still failing if such a wait comes back.
    assert!(
        took < Duration::from_millis(2500),
        "100 short programs took {took:?}"
    );
}

#[test]
fn a_program_that_runs_for_a_while_is_still_waited_for() {
    let dir = tempfile::tempdir().expect("temporary directory");

    let (code, took) = vsh(dir.path(), "sleep 0.3; exit 4");

    assert_eq!(code, 4, "the status given to exit should be the shell's");
    assert!(
        took >= Duration::from_millis(300),
        "the shell returned after {took:?}, before the program finished"
    );
}

// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! A command that fails fails only itself, and `set -e` ends the shell.
//!
//! A built-in that failed used to be an error that unwound through every
//! command around it: `mkdir x || echo no` never ran `echo no`, a loop
//! stopped at its first failure, and a script ended at the first built-in
//! that failed. That last one stood in for `set -e`, which was not
//! implemented: `set -e; false; echo after` printed `after`.
//!
//! Now each command is a boundary. A failure prints what went wrong and
//! gives a status, and whatever ran the command goes on. `set -e` ends the
//! shell at a simple command that fails, except in a condition and in an
//! `&&` or `||` list before its last command.
//!
//! Every expected output and status here is what GNU bash 5.2.21 gives for
//! the same line (`bash -c`, standard error not compared); dash 5.2 agrees
//! except where a case says otherwise. Each test runs the built shell.

use std::process::{Command, Stdio};

/// Runs `script` with `vsh -c` in a fresh directory. Returns the standard
/// output, without the shell's own `[op:` receipt lines, and the status.
fn vsh(script: &str) -> (String, i32) {
    let dir = tempfile::tempdir().expect("temporary directory");
    let output = Command::new(env!("CARGO_BIN_EXE_vsh"))
        .arg("-r")
        .arg(dir.path())
        .arg("-c")
        .arg(script)
        .current_dir(dir.path())
        .env("HOME", dir.path())
        .env("NO_COLOR", "1")
        .env_remove("RUST_BACKTRACE")
        .stdin(Stdio::null())
        .output()
        .expect("start the built shell");
    let stdout = String::from_utf8_lossy(&output.stdout)
        .split_inclusive('\n')
        .filter(|line| !line.starts_with("[op:") && !line.starts_with("[txn:"))
        .collect();
    (stdout, output.status.code().unwrap_or(-1))
}

/// Runs each case and reports every one that differs, not only the first.
fn check(cases: &[(&str, &str, i32)]) {
    let wrong: Vec<String> = cases
        .iter()
        .filter_map(|&(script, out, status)| {
            let (got_out, got_status) = vsh(script);
            (got_out != out || got_status != status).then(|| {
                format!(
                    "  {script}\n    expected {out:?}, status {status}\n    got      \
                     {got_out:?}, status {got_status}"
                )
            })
        })
        .collect();
    assert!(
        wrong.is_empty(),
        "{} of {} cases differ from bash:\n{}",
        wrong.len(),
        cases.len(),
        wrong.join("\n")
    );
}

#[test]
fn a_command_that_fails_fails_only_itself() {
    check(&[
        // The line from the review of #233.
        (
            r#"f() { local x=inner; mkdir /no/such/parent/dir; }; x=outer; f; echo "$x""#,
            "outer\n",
            0,
        ),
        ("mkdir no/such/dir; echo rc=$?", "rc=1\n", 0),
        ("mkdir no/such/dir || echo fallback", "fallback\n", 0),
        ("rm nosuch && echo no; echo rc=$?", "rc=1\n", 0),
        (
            "for i in 1 2; do rm nosuch; echo body$i; done; echo end",
            "body1\nbody2\nend\n",
            0,
        ),
        (
            "f() { rm nosuch; echo infunc; }; f; echo rc=$?",
            "infunc\nrc=0\n",
            0,
        ),
        (
            "f() { rm nosuch; }; if f; then echo yes; else echo no; fi",
            "no\n",
            0,
        ),
        (
            "case x in x) rm nosuch; echo arm;; esac; echo end",
            "arm\nend\n",
            0,
        ),
        (
            "trap 'echo bye' EXIT; rm nosuch; echo after",
            "after\nbye\n",
            0,
        ),
    ]);
}

/// The status a failure gives. dash differs on the first three: it ends the
/// shell at `return` and `local` outside a function, and at the `eval`.
#[test]
fn a_failure_gives_the_status_bash_gives() {
    check(&[
        ("return 0; echo rc=$?", "rc=2\n", 0),
        ("eval 'if'; echo rc=$?", "rc=2\n", 0),
        ("local y=1; echo rc=$?", "rc=1\n", 0),
        // No branch ran: status 0. It was 1, which `set -e` would take for
        // a failure.
        ("if false; then :; fi; echo rc=$?", "rc=0\n", 0),
    ]);
}

#[test]
fn set_e_ends_the_shell_at_a_command_that_fails() {
    check(&[
        ("set -e; false; echo after", "", 1),
        ("set -e; rm nosuch; echo after", "", 1),
        ("set -e; f() { false; echo infunc; }; f; echo after", "", 1),
        ("set -e; true && false; echo after", "", 1),
        (
            "set -e; for i in 1 2; do false; echo body; done; echo after",
            "",
            1,
        ),
        // A function that returns a failure is a command that fails.
        ("set -e; f() { return 3; }; f; echo after", "", 3),
        // The EXIT trap still runs.
        (
            "set -e; trap 'echo bye' EXIT; false; echo after",
            "bye\n",
            1,
        ),
    ]);
}

#[test]
fn set_e_does_not_apply_to_a_condition_or_inside_a_list() {
    check(&[
        ("set -e; false && true; echo after", "after\n", 0),
        ("set -e; false || true; echo after", "after\n", 0),
        (
            "set -e; mkdir no/such/dir || true; echo after",
            "after\n",
            0,
        ),
        ("set -e; if false; then :; fi; echo after", "after\n", 0),
        (
            "set -e; if mkdir no/such/dir; then :; else echo no; fi; echo after",
            "no\nafter\n",
            0,
        ),
        ("set -e; while false; do :; done; echo after", "after\n", 0),
        // A function called as a condition is in the condition too.
        (
            "set -e; f() { false; echo infunc; }; if f; then echo y; fi; echo after",
            "infunc\ny\nafter\n",
            0,
        ),
        ("set -e; set +e; false; echo after", "after\n", 0),
    ]);
}

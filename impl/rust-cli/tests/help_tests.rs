// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! `help` is a command of the shell.
//!
//! The interactive banner tells the user to type `help`. The default
//! interactive loop answered "help: Command not found". These tests run the
//! built shell.

use std::process::{Command, Stdio};

fn vsh(script: &str) -> (i32, String, String) {
    let dir = tempfile::tempdir().expect("temporary directory");
    let output = Command::new(env!("CARGO_BIN_EXE_vsh"))
        .arg("-r")
        .arg(dir.path())
        .arg("-c")
        .arg(script)
        .current_dir(dir.path())
        .env("NO_COLOR", "1")
        .env_remove("RUST_BACKTRACE")
        .stdin(Stdio::null())
        .output()
        .expect("start the built shell");
    (
        output.status.code().unwrap_or(-1),
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

#[test]
fn help_lists_the_commands() {
    let (code, stdout, stderr) = vsh("help");

    assert_eq!(code, 0, "stderr: {stderr}");
    for name in ["mkdir", "undo", "rollback", "obliterate", "explain", "help"] {
        assert!(stdout.contains(name), "`help` should list {name}: {stdout}");
    }
}

#[test]
fn help_for_one_command_describes_it() {
    let (code, stdout, stderr) = vsh("help mkdir");

    assert_eq!(code, 0, "stderr: {stderr}");
    assert!(stdout.contains("mkdir"), "stdout: {stdout}");
}

/// The topic is expanded like any other operand.
#[test]
fn help_takes_its_topic_from_a_variable() {
    let (code, stdout, stderr) = vsh("topic=mkdir; help $topic");

    assert_eq!(code, 0, "stderr: {stderr}");
    assert!(stdout.contains("Create a directory"), "stdout: {stdout}");
}

#[test]
fn help_for_an_unknown_command_says_so() {
    let (code, _, stderr) = vsh("help nosuchcommand");

    assert_ne!(code, 0);
    assert!(
        stderr.contains("No help available"),
        "stderr should say there is no help: {stderr}"
    );
}

#[test]
fn help_does_not_promise_things_that_are_not_there() {
    for script in ["help", "help mkdir", "help undo"] {
        let (_, stdout, _) = vsh(script);

        assert!(
            !stdout.contains("man vsh"),
            "`{script}`: there are no manual pages"
        );
        assert!(
            !stdout.contains("help -v"),
            "`{script}`: there is no -v option"
        );
    }
}

/// Help that is captured or piped is written as it is, not handed to a
/// pager. On a system with `more` and no `less` the pager was started with
/// options it does not take, and the help text was lost.
#[cfg(unix)]
#[test]
fn help_is_not_paged_when_it_is_not_going_to_a_terminal() {
    use std::os::unix::fs::PermissionsExt;

    let dir = tempfile::tempdir().expect("temporary directory");
    let bin = tempfile::tempdir().expect("directory for a stand-in pager");
    // The only pager on the path, and it refuses whatever it is given.
    let more = bin.path().join("more");
    std::fs::write(&more, "#!/bin/sh\nexit 1\n").expect("write the stand-in");
    std::fs::set_permissions(&more, std::fs::Permissions::from_mode(0o755))
        .expect("make it runnable");

    let output = Command::new(env!("CARGO_BIN_EXE_vsh"))
        .arg("-r")
        .arg(dir.path())
        .arg("-c")
        .arg("help mkdir")
        .current_dir(dir.path())
        .env("PATH", bin.path())
        .env("NO_COLOR", "1")
        .env("LINES", "5")
        .env_remove("RUST_BACKTRACE")
        .stdin(Stdio::null())
        .output()
        .expect("start the built shell");
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(output.status.success());
    assert!(
        stdout.contains("mkdir") && stdout.lines().count() > 5,
        "the help text should be on standard output: {stdout:?}"
    );
}

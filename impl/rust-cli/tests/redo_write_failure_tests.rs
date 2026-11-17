// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! A redo whose file write fails part-way must leave the file as it found it
//! and stay on the redo stack.
//!
//! The write failure is real: the test lowers this process's file-size limit
//! (`RLIMIT_FSIZE`) so that the kernel refuses the write with `EFBIG` after
//! the first 4096 bytes. That limit is process-wide, which is why this test
//! lives in a binary of its own with a single test.
#![cfg(target_os = "linux")]

use std::fs;
use std::path::Path;

use tempfile::TempDir;
use vsh::commands;
use vsh::executable::ExecutableCommand;
use vsh::parser::parse_command;
use vsh::state::ShellState;

const LIMIT: u64 = 4096;

fn file_size_limit() -> libc::rlimit {
    let mut limit = libc::rlimit {
        rlim_cur: 0,
        rlim_max: 0,
    };
    // SAFETY: `limit` is a valid, writable `rlimit` for the duration of the call.
    let rc = unsafe { libc::getrlimit(libc::RLIMIT_FSIZE, &mut limit) };
    assert_eq!(rc, 0, "getrlimit");
    limit
}

fn set_file_size_limit(soft: libc::rlim_t) {
    let limit = libc::rlimit {
        rlim_cur: soft,
        rlim_max: file_size_limit().rlim_max,
    };
    // SAFETY: `limit` is a valid `rlimit`; only the soft limit changes, and it
    // never exceeds the hard limit read just above.
    let rc = unsafe { libc::setrlimit(libc::RLIMIT_FSIZE, &limit) };
    assert_eq!(rc, 0, "setrlimit");
}

fn run(state: &mut ShellState, line: &str) {
    parse_command(line)
        .unwrap_or_else(|e| panic!("parse {line:?}: {e}"))
        .execute(state)
        .unwrap_or_else(|e| panic!("execute {line:?}: {e}"));
}

fn bytes(fill: u8, len: usize) -> Vec<u8> {
    vec![fill; len]
}

/// Redo with the limit lowered, expecting failure, then with it restored,
/// expecting success. Returns the error text of the failed attempt.
fn redo_under_limit_then_freely(state: &mut ShellState, unlimited: libc::rlim_t) -> String {
    set_file_size_limit(LIMIT);
    let failed = commands::redo(state, 1, false);
    set_file_size_limit(unlimited);
    let message = format!("{:#}", failed.expect_err("redo over the file-size limit"));
    assert_eq!(
        state.get_redo_stack().len(),
        1,
        "the entry is kept: {message}"
    );
    message
}

#[test]
fn redo_that_fails_part_way_through_a_write_changes_nothing() {
    // With the signal ignored, a write past the limit fails with EFBIG
    // instead of terminating the process.
    // SAFETY: installs the "ignore" disposition for one signal; no handler runs.
    unsafe { libc::signal(libc::SIGXFSZ, libc::SIG_IGN) };
    let unlimited = file_size_limit().rlim_cur;

    let temp = TempDir::new().expect("tempdir");
    let root: &Path = temp.path();
    let mut state = ShellState::new(root.to_str().expect("utf8")).expect("state");
    let big = bytes(0xb1, 2 * LIMIT as usize);
    // External commands run in the process's directory, so sources are
    // outside the sandbox and named absolutely.
    let sources = TempDir::new().expect("tempdir");
    let big_src = sources.path().join("big");
    fs::write(&big_src, &big).expect("write");

    // -- a file a redirection created --------------------------------------
    let created = root.join("created");
    run(
        &mut state,
        &format!("/bin/cat {} > created", big_src.display()),
    );
    assert_eq!(fs::read(&created).expect("read"), big);
    commands::undo(&mut state, 1, false).expect("undo");
    assert!(!created.exists());

    redo_under_limit_then_freely(&mut state, unlimited);
    assert!(!created.exists(), "no partial file is left behind");

    commands::redo(&mut state, 1, false).expect("redo once the limit is lifted");
    assert_eq!(fs::read(&created).expect("read"), big);

    // -- a file a redirection replaced --------------------------------------
    let replaced = root.join("replaced");
    let before = bytes(0xa0, 1000);
    fs::write(&replaced, &before).expect("write");
    run(
        &mut state,
        &format!("/bin/cat {} > replaced", big_src.display()),
    );
    assert_eq!(fs::read(&replaced).expect("read"), big);
    commands::undo(&mut state, 1, false).expect("undo");
    assert_eq!(fs::read(&replaced).expect("read"), before);

    redo_under_limit_then_freely(&mut state, unlimited);
    assert_eq!(
        fs::read(&replaced).expect("read"),
        before,
        "the previous content is put back"
    );

    commands::redo(&mut state, 1, false).expect("redo once the limit is lifted");
    assert_eq!(fs::read(&replaced).expect("read"), big);
    commands::undo(&mut state, 1, false).expect("undo after the retried redo");
    assert_eq!(
        fs::read(&replaced).expect("read"),
        before,
        "the retried redo captured the right undo data"
    );
    commands::redo(&mut state, 1, false).expect("redo");

    // -- a replaced file whose previous content is itself over the limit ----
    // Putting the previous content back must not depend on being able to
    // write that much again: only the overwritten part is rewritten.
    let large = root.join("large");
    let large_before = bytes(0xa1, 3 * LIMIT as usize);
    fs::write(&large, &large_before).expect("write");
    run(
        &mut state,
        &format!("/bin/cat {} > large", big_src.display()),
    );
    assert_eq!(fs::read(&large).expect("read"), big);
    commands::undo(&mut state, 1, false).expect("undo");
    assert_eq!(fs::read(&large).expect("read"), large_before);

    let message = redo_under_limit_then_freely(&mut state, unlimited);
    assert!(
        fs::read(&large).expect("read") == large_before,
        "the previous content is put back even though it is over the limit: {message}"
    );
    assert!(
        !message.contains("could not be restored"),
        "restoring did not fail: {message}"
    );

    commands::redo(&mut state, 1, false).expect("redo once the limit is lifted");
    assert_eq!(fs::read(&large).expect("read"), big);
    commands::undo(&mut state, 1, false).expect("undo after the retried redo");
    assert!(fs::read(&large).expect("read") == large_before);
    commands::redo(&mut state, 1, false).expect("redo");

    // -- a file a redirection appended to -----------------------------------
    let appended = root.join("appended");
    fs::write(&appended, &before).expect("write");
    run(
        &mut state,
        &format!("/bin/cat {} >> appended", big_src.display()),
    );
    let after: Vec<u8> = before.iter().chain(big.iter()).copied().collect();
    assert_eq!(fs::read(&appended).expect("read"), after);
    commands::undo(&mut state, 1, false).expect("undo");
    assert_eq!(fs::read(&appended).expect("read"), before);

    redo_under_limit_then_freely(&mut state, unlimited);
    assert_eq!(
        fs::read(&appended).expect("read"),
        before,
        "the partial append is cut off"
    );

    commands::redo(&mut state, 1, false).expect("redo once the limit is lifted");
    assert_eq!(fs::read(&appended).expect("read"), after);
}

// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! `rm`, and redo of `rm`, must not delete a file whose content cannot be
//! read: the content is the undo data, and without it a later undo would
//! bring the file back empty.
//!
//! Root can read any file, so when the tests run as root this one switches
//! the process's effective user to `nobody` around the calls under test.
//! That switch is process-wide, which is why this test lives in a binary of
//! its own with a single test.
#![cfg(unix)]

use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::Path;

use tempfile::TempDir;
use vsh::commands;
use vsh::state::ShellState;

const NOBODY: libc::uid_t = 65534;

fn effective_uid() -> libc::uid_t {
    // SAFETY: `geteuid` has no preconditions and cannot fail.
    unsafe { libc::geteuid() }
}

fn set_effective_uid(uid: libc::uid_t) {
    // SAFETY: changes only this process's effective user id; the real and
    // saved ids stay root, so the switch back below is permitted.
    let rc = unsafe { libc::seteuid(uid) };
    assert_eq!(rc, 0, "seteuid({uid})");
}

/// Run `f` as a user for whom `unreadable` cannot be read.
fn without_read_access<T>(unreadable: &Path, f: impl FnOnce() -> T) -> T {
    fs::set_permissions(unreadable, fs::Permissions::from_mode(0o000)).expect("chmod 000");
    let was_root = effective_uid() == 0;
    if was_root {
        set_effective_uid(NOBODY);
    }
    assert!(
        fs::read(unreadable).is_err(),
        "the file is unreadable to the user the test runs as"
    );
    let result = f();
    if was_root {
        set_effective_uid(0);
    }
    fs::set_permissions(unreadable, fs::Permissions::from_mode(0o600)).expect("chmod 600");
    result
}

#[test]
fn rm_and_its_redo_do_not_delete_a_file_they_cannot_read() {
    let temp = TempDir::new().expect("tempdir");
    let root = temp.path();
    // The directory stays writable to the unprivileged user, so the unlink
    // itself would succeed; only the read can fail.
    fs::set_permissions(root, fs::Permissions::from_mode(0o777)).expect("chmod dir");
    let mut state = ShellState::new(root.to_str().expect("utf8")).expect("state");
    let f = root.join("f");
    fs::write(&f, b"keep me").expect("write");

    // -- the command ----------------------------------------------------------
    let err = without_read_access(&f, || commands::rm(&mut state, "f", false))
        .expect_err("rm of an unreadable file must fail");
    assert!(err.to_string().contains("was not deleted"), "{err}");
    assert_eq!(
        fs::read(&f).expect("read"),
        b"keep me",
        "the file is intact"
    );
    assert!(state.history.is_empty(), "nothing was recorded");

    // -- its redo ---------------------------------------------------------------
    commands::rm(&mut state, "f", false).expect("rm of a readable file");
    commands::undo(&mut state, 1, false).expect("undo");
    assert_eq!(fs::read(&f).expect("read"), b"keep me");

    let recorded = state.history.len();
    let redone = without_read_access(&f, || commands::redo(&mut state, 1, false));
    assert!(
        redone.is_err(),
        "redo of rm on an unreadable file must fail"
    );
    assert_eq!(
        fs::read(&f).expect("read"),
        b"keep me",
        "the file is intact"
    );
    assert_eq!(state.history.len(), recorded, "nothing was recorded");
    assert_eq!(state.get_redo_stack().len(), 1, "the entry is kept");

    // Readable again: the same redo works, and its undo restores the bytes.
    commands::redo(&mut state, 1, false).expect("redo");
    assert!(!f.exists());
    commands::undo(&mut state, 1, false).expect("undo after redo");
    assert_eq!(fs::read(&f).expect("read"), b"keep me");
}

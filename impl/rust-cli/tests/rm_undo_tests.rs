// SPDX-License-Identifier: MPL-2.0
//! `rm` and its undo: the file comes back as it was, links are treated as
//! links, and nothing outside the session root is touched.

#![cfg(unix)]

mod fixtures;

use fixtures::sandbox;
use std::fs;
use std::os::unix::fs::{symlink, PermissionsExt};
use std::time::{Duration, UNIX_EPOCH};
use vsh::commands;
use vsh::state::{Operation, OperationType, ShellState};

#[test]
fn undo_of_rm_restores_content_mode_and_modification_time() {
    let (sandbox, mut state) = sandbox();
    let path = sandbox.root.join("secret");
    fs::write(&path, "TOPSECRET").unwrap();
    fs::set_permissions(&path, fs::Permissions::from_mode(0o640)).unwrap();
    let long_ago = UNIX_EPOCH + Duration::new(1_500_000_000, 123_000_000);
    fs::File::options()
        .write(true)
        .open(&path)
        .unwrap()
        .set_modified(long_ago)
        .unwrap();

    commands::rm(&mut state, "secret", false).unwrap();
    assert!(!path.exists());
    commands::undo(&mut state, 1, false).unwrap();

    let meta = fs::metadata(&path).unwrap();
    assert_eq!(fs::read(&path).unwrap(), b"TOPSECRET");
    assert_eq!(meta.permissions().mode() & 0o7777, 0o640);
    assert_eq!(meta.modified().unwrap(), long_ago);
}

#[test]
fn undo_of_rm_survives_a_restart() {
    let (sandbox, mut state) = sandbox();
    let path = sandbox.root.join("s");
    fs::write(&path, "X").unwrap();
    fs::set_permissions(&path, fs::Permissions::from_mode(0o600)).unwrap();
    commands::rm(&mut state, "s", false).unwrap();
    drop(state);

    let mut state = ShellState::new(sandbox.root.to_str().unwrap()).unwrap();
    commands::undo(&mut state, 1, false).unwrap();
    assert_eq!(
        fs::metadata(&path).unwrap().permissions().mode() & 0o7777,
        0o600
    );
}

#[test]
fn rm_of_a_symlink_removes_the_link_and_undo_puts_it_back() {
    let (sandbox, mut state) = sandbox();
    let victim = sandbox.outside.join("victim");
    fs::write(&victim, "PRECIOUS").unwrap();
    symlink(&victim, sandbox.root.join("link")).unwrap();

    commands::rm(&mut state, "link", false).unwrap();
    assert!(fs::symlink_metadata(sandbox.root.join("link")).is_err());
    assert_eq!(fs::read(&victim).unwrap(), b"PRECIOUS");
    // The link's target is recorded, not the target's content.
    let op = state.history.last().unwrap();
    assert_eq!(op.op_type, OperationType::Unlink);
    assert_eq!(
        op.undo_data.as_deref(),
        Some(victim.to_str().unwrap().as_bytes())
    );

    commands::undo(&mut state, 1, false).unwrap();
    assert_eq!(fs::read_link(sandbox.root.join("link")).unwrap(), victim);
    assert_eq!(fs::read(&victim).unwrap(), b"PRECIOUS");
}

#[test]
fn rm_can_remove_a_dangling_symlink() {
    let (sandbox, mut state) = sandbox();
    symlink("nowhere", sandbox.root.join("dangling")).unwrap();
    commands::rm(&mut state, "dangling", false).unwrap();
    assert!(fs::symlink_metadata(sandbox.root.join("dangling")).is_err());
}

#[test]
fn rm_does_not_reach_through_a_symlinked_directory() {
    let (sandbox, mut state) = sandbox();
    fs::write(sandbox.outside.join("victim"), "PRECIOUS").unwrap();
    symlink(&sandbox.outside, sandbox.root.join("lp")).unwrap();

    assert!(commands::rm(&mut state, "lp/victim", false).is_err());
    assert_eq!(
        fs::read(sandbox.outside.join("victim")).unwrap(),
        b"PRECIOUS"
    );
    assert!(state.history.is_empty());
}

/// A link target is a string of bytes and need not be text. Undo of `rm`
/// puts back the same bytes. It used to store the target as text, with what
/// was not text replaced, and so made a link to a different path.
#[test]
fn undo_restores_a_link_whose_target_is_not_text() {
    use std::ffi::OsStr;
    use std::os::unix::ffi::OsStrExt;

    let (sandbox, mut state) = sandbox();
    let target = OsStr::from_bytes(b"t\xffarget");
    let link = sandbox.root.join("link");
    symlink(target, &link).unwrap();

    commands::rm(&mut state, "link", false).unwrap();
    assert!(fs::symlink_metadata(&link).is_err());

    commands::undo(&mut state, 1, false).unwrap();
    assert_eq!(fs::read_link(&link).unwrap().as_os_str(), target);
}

/// A link that is removed, put back and removed again (`rm link; undo;
/// redo`) can be put back again. The redone record used to lose the link's
/// target, so the second undo failed with "Missing symlink target for
/// undo".
#[test]
fn a_redone_rm_of_a_link_can_be_undone_again() {
    let (sandbox, mut state) = sandbox();
    let link = sandbox.root.join("link");
    symlink("target", &link).unwrap();

    commands::rm(&mut state, "link", false).unwrap();
    commands::undo(&mut state, 1, false).unwrap();
    commands::redo(&mut state, 1, false).unwrap();
    assert!(fs::symlink_metadata(&link).is_err());

    commands::undo(&mut state, 1, false).unwrap();
    assert_eq!(fs::read_link(&link).unwrap().to_str(), Some("target"));
}

/// A removal that is redone removes the file a second time, and its record
/// must hold the content again. It held none, so `rm f; undo; redo; undo`
/// put an empty file, readable by its owner only, in place of `f`.
#[test]
fn a_redone_rm_can_be_undone_again() {
    let (sandbox, mut state) = sandbox();
    let path = sandbox.root.join("f");
    fs::write(&path, "precious").unwrap();
    fs::set_permissions(&path, fs::Permissions::from_mode(0o640)).unwrap();

    commands::rm(&mut state, "f", false).unwrap();
    commands::undo(&mut state, 1, false).unwrap();
    commands::redo(&mut state, 1, false).unwrap();
    assert!(!path.exists());

    commands::undo(&mut state, 1, false).unwrap();
    assert_eq!(fs::read(&path).unwrap(), b"precious");
    assert_eq!(
        fs::metadata(&path).unwrap().permissions().mode() & 0o7777,
        0o640
    );
}

/// The redone removal keeps what the file holds when it is removed. That
/// is not always what the first removal saved: the file can have been
/// changed in between.
#[test]
fn a_redone_rm_keeps_what_the_file_holds_then() {
    let (sandbox, mut state) = sandbox();
    let path = sandbox.root.join("f");
    fs::write(&path, "first").unwrap();

    commands::rm(&mut state, "f", false).unwrap();
    commands::undo(&mut state, 1, false).unwrap();
    fs::write(&path, "changed since").unwrap();
    commands::redo(&mut state, 1, false).unwrap();
    commands::undo(&mut state, 1, false).unwrap();

    assert_eq!(fs::read(&path).unwrap(), b"changed since");
}

/// A removal whose record holds no content cannot be undone. Undo used to
/// write an empty file in its place and report success.
#[test]
fn undo_of_a_removal_with_no_content_fails_and_creates_nothing() {
    let (sandbox, mut state) = sandbox();
    state.record_operation(Operation::new(
        OperationType::DeleteFile,
        "gone".to_string(),
        None,
    ));

    let refused = commands::undo(&mut state, 1, false).unwrap_err();

    assert!(
        format!("{refused:#}").contains("holds no content"),
        "{refused:#}"
    );
    assert!(!sandbox.root.join("gone").exists());
}

/// What is redone must still be a regular file. A removal is not redone on
/// a directory or a link that has taken the file's place.
#[test]
fn a_removal_is_not_redone_on_something_that_is_not_a_regular_file() {
    let (sandbox, mut state) = sandbox();
    let path = sandbox.root.join("f");
    fs::write(&path, "content").unwrap();

    commands::rm(&mut state, "f", false).unwrap();
    commands::undo(&mut state, 1, false).unwrap();
    fs::remove_file(&path).unwrap();
    symlink(sandbox.outside.join("victim"), &path).unwrap();
    fs::write(sandbox.outside.join("victim"), "OUTSIDE").unwrap();

    let refused = commands::redo(&mut state, 1, false).unwrap_err();

    assert!(
        format!("{refused:#}").contains("not a regular file"),
        "{refused:#}"
    );
    assert!(fs::symlink_metadata(&path).unwrap().is_symlink());
    assert_eq!(
        fs::read(sandbox.outside.join("victim")).unwrap(),
        b"OUTSIDE"
    );
}

// SPDX-License-Identifier: MPL-2.0
//! `obliterate` destroys only what it was pointed at.
//!
//! It must never follow a symbolic link, never overwrite a file that has
//! another name, never run inside a transaction, and never destroy anything
//! before its audit entry is written. When it refuses, nothing is changed.

#![cfg(unix)]

mod fixtures;

use fixtures::tempfile::TempDir;
use std::fs;
use std::os::unix::fs::symlink;
use std::path::PathBuf;
use vsh::commands::secure_deletion::{obliterate_path, secure_delete};
use vsh::state::ShellState;

/// A session root and a sibling directory that must never change.
struct Sandbox {
    _temp: TempDir,
    root: PathBuf,
    outside: PathBuf,
}

fn sandbox() -> (Sandbox, ShellState) {
    let temp = TempDir::new().unwrap();
    let root = temp.path().join("root");
    let outside = temp.path().join("outside");
    fs::create_dir(&root).unwrap();
    fs::create_dir(&outside).unwrap();
    let state = ShellState::new(root.to_str().unwrap()).unwrap();
    (
        Sandbox {
            _temp: temp,
            root,
            outside,
        },
        state,
    )
}

fn audit_log(sandbox: &Sandbox) -> String {
    fs::read_to_string(sandbox.root.join(".vsh-audit.log")).unwrap_or_default()
}

#[test]
fn a_plain_file_is_obliterated_and_audited_before_and_after() {
    let (sandbox, mut state) = sandbox();
    fs::write(sandbox.root.join("secret"), "SECRET").unwrap();

    obliterate_path(&mut state, "secret", false, true).unwrap();

    assert!(!sandbox.root.join("secret").exists());
    let log = audit_log(&sandbox);
    let intent = log.find("obliterate-intent").expect("intent entry");
    let outcome = log.find("\"obliterated\"").expect("outcome entry");
    assert!(intent < outcome, "the intent entry must come first");
}

#[test]
fn a_symlink_is_refused_and_its_target_is_untouched() {
    let (sandbox, mut state) = sandbox();
    fs::write(sandbox.outside.join("victim"), "PRECIOUS").unwrap();
    fs::write(sandbox.root.join("inside"), "INSIDE").unwrap();
    symlink(sandbox.outside.join("victim"), sandbox.root.join("out")).unwrap();
    symlink("inside", sandbox.root.join("in")).unwrap();

    // Even a link to a file inside the root is refused: the request named
    // the link, not the file.
    for link in ["out", "in"] {
        let refused = obliterate_path(&mut state, link, false, true).unwrap_err();
        assert!(refused.to_string().contains("symbolic link"), "{refused}");
        assert!(sandbox.root.join(link).is_symlink(), "{link} must remain");
    }
    assert_eq!(
        fs::read(sandbox.outside.join("victim")).unwrap(),
        b"PRECIOUS"
    );
    assert_eq!(fs::read(sandbox.root.join("inside")).unwrap(), b"INSIDE");
    assert!(audit_log(&sandbox).is_empty(), "a refusal writes no entry");
}

#[test]
fn a_symlink_to_a_directory_is_refused() {
    let (sandbox, mut state) = sandbox();
    fs::write(sandbox.outside.join("victim"), "PRECIOUS").unwrap();
    symlink(&sandbox.outside, sandbox.root.join("dirlink")).unwrap();

    assert!(obliterate_path(&mut state, "dirlink", false, true).is_err());
    assert_eq!(
        fs::read(sandbox.outside.join("victim")).unwrap(),
        b"PRECIOUS"
    );
}

#[test]
fn a_hard_linked_file_is_refused() {
    let (sandbox, mut state) = sandbox();
    fs::write(sandbox.outside.join("victim"), "PRECIOUS").unwrap();
    fs::hard_link(sandbox.outside.join("victim"), sandbox.root.join("hl")).unwrap();

    let refused = obliterate_path(&mut state, "hl", false, true).unwrap_err();
    assert!(refused.to_string().contains("hard links"), "{refused}");
    assert_eq!(
        fs::read(sandbox.outside.join("victim")).unwrap(),
        b"PRECIOUS"
    );
    assert!(sandbox.root.join("hl").exists());
}

#[test]
fn obliterate_is_refused_inside_a_transaction() {
    let (sandbox, mut state) = sandbox();
    fs::write(sandbox.root.join("f"), "DATA").unwrap();
    fs::create_dir(sandbox.root.join("d")).unwrap();
    state.begin_transaction("t").unwrap();

    for target in ["f", "d"] {
        let refused = obliterate_path(&mut state, target, false, true).unwrap_err();
        assert!(refused.to_string().contains("transaction"), "{refused}");
    }
    assert_eq!(fs::read(sandbox.root.join("f")).unwrap(), b"DATA");
    assert!(sandbox.root.join("d").is_dir());
}

#[test]
fn nothing_is_destroyed_when_the_audit_entry_cannot_be_written() {
    let (sandbox, mut state) = sandbox();
    fs::write(sandbox.root.join("f"), "DATA").unwrap();
    fs::create_dir(sandbox.root.join("d")).unwrap();
    fs::write(sandbox.root.join("d/inner"), "INNER").unwrap();
    // A directory where the audit log should be: no entry can be written.
    fs::create_dir(sandbox.root.join(".vsh-audit.log")).unwrap();

    for target in ["f", "d"] {
        let refused = obliterate_path(&mut state, target, false, true).unwrap_err();
        assert!(format!("{refused:#}").contains("audit"), "{refused:#}");
    }
    assert_eq!(fs::read(sandbox.root.join("f")).unwrap(), b"DATA");
    assert_eq!(fs::read(sandbox.root.join("d/inner")).unwrap(), b"INNER");
}

#[test]
fn a_directory_is_obliterated_without_following_the_links_in_it() {
    let (sandbox, mut state) = sandbox();
    fs::write(sandbox.outside.join("victim"), "PRECIOUS").unwrap();
    fs::create_dir_all(sandbox.root.join("d/sub")).unwrap();
    fs::write(sandbox.root.join("d/a"), "A").unwrap();
    fs::write(sandbox.root.join("d/sub/b"), "B").unwrap();
    symlink(sandbox.outside.join("victim"), sandbox.root.join("d/out")).unwrap();
    symlink(&sandbox.outside, sandbox.root.join("d/sub/outdir")).unwrap();

    obliterate_path(&mut state, "d", false, true).unwrap();

    assert!(!sandbox.root.join("d").exists());
    // The links are gone; what they pointed to is not.
    assert_eq!(
        fs::read(sandbox.outside.join("victim")).unwrap(),
        b"PRECIOUS"
    );
    assert!(sandbox.outside.is_dir());
}

#[test]
fn a_directory_holding_a_hard_linked_file_is_refused_whole() {
    let (sandbox, mut state) = sandbox();
    fs::write(sandbox.outside.join("victim"), "PRECIOUS").unwrap();
    fs::create_dir(sandbox.root.join("d")).unwrap();
    fs::write(sandbox.root.join("d/a"), "A").unwrap();
    fs::hard_link(sandbox.outside.join("victim"), sandbox.root.join("d/hl")).unwrap();

    let refused = obliterate_path(&mut state, "d", false, true).unwrap_err();
    assert!(refused.to_string().contains("hard links"), "{refused}");

    // Nothing in the directory was touched, not even the ordinary file.
    assert_eq!(fs::read(sandbox.root.join("d/a")).unwrap(), b"A");
    assert_eq!(
        fs::read(sandbox.outside.join("victim")).unwrap(),
        b"PRECIOUS"
    );
    assert!(audit_log(&sandbox).is_empty());
}

#[test]
fn secure_delete_refuses_links_too() {
    let (sandbox, _state) = sandbox();
    fs::write(sandbox.outside.join("victim"), "PRECIOUS").unwrap();
    fs::write(sandbox.outside.join("other"), "OTHER").unwrap();
    symlink(sandbox.outside.join("victim"), sandbox.root.join("sl")).unwrap();
    fs::hard_link(sandbox.outside.join("other"), sandbox.root.join("hl")).unwrap();
    fs::write(sandbox.root.join("plain"), "PLAIN").unwrap();

    assert!(secure_delete(&sandbox.root.join("sl")).is_err());
    assert!(secure_delete(&sandbox.root.join("hl")).is_err());
    assert_eq!(
        fs::read(sandbox.outside.join("victim")).unwrap(),
        b"PRECIOUS"
    );
    assert_eq!(fs::read(sandbox.outside.join("other")).unwrap(), b"OTHER");

    secure_delete(&sandbox.root.join("plain")).unwrap();
    assert!(!sandbox.root.join("plain").exists());
}

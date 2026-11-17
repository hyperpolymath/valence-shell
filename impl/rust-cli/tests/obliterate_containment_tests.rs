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

/// After obliteration the history holds none of the file's earlier content,
/// and no earlier operation on it can be undone or redone.
#[test]
fn obliterate_scrubs_the_history_of_the_path() {
    use vsh::parser::parse_command;
    use vsh::ExecutableCommand;

    let (sandbox, mut state) = sandbox();
    let run = |state: &mut ShellState, command: &str| {
        parse_command(command).unwrap().execute(state).unwrap();
    };
    fs::write(sandbox.root.join("other"), "OTHER").unwrap();
    fs::write(sandbox.root.join("f"), "SECRETA").unwrap();
    // `rm` then `undo` puts the content into the history twice over: as the
    // undo data of the removal, and in the redo stack.
    run(&mut state, "rm f");
    run(&mut state, "undo");
    run(&mut state, "rm other");

    obliterate_path(&mut state, "f", false, true).unwrap();

    for op in &state.history {
        let holds = op
            .undo_data
            .as_deref()
            .is_some_and(|data| data.windows(7).any(|w| w == b"SECRETA"));
        assert!(
            !holds,
            "{:?} on {} still holds the content",
            op.op_type, op.path
        );
        // Every earlier operation on `f` is closed off. The obliteration
        // itself stays as the record of what happened.
        if op.path == "f" && op.op_type != vsh::state::OperationType::Obliterate {
            assert!(op.undone, "{:?} on f can still be undone", op.op_type);
        }
    }
    assert!(state.redo_stack.iter().all(|op| op.path != "f"));
    let saved = fs::read_to_string(sandbox.root.join(".vsh_state.json")).unwrap();
    let compact: String = saved.chars().filter(|c| !c.is_whitespace()).collect();
    assert!(
        !compact.contains("83,69,67,82,69,84,65"),
        "SECRETA is still saved"
    );

    // Operations on other paths are untouched: undo restores `other`. The
    // newest operation is the obliteration, which undo passes over, so two
    // steps are asked for.
    vsh::commands::undo(&mut state, 2, false).unwrap();
    assert_eq!(fs::read(sandbox.root.join("other")).unwrap(), b"OTHER");
    assert!(!sandbox.root.join("f").exists());
}

/// Obliterating a directory scrubs the history of everything in it.
#[test]
fn obliterating_a_directory_scrubs_what_was_in_it() {
    let (sandbox, mut state) = sandbox();
    fs::create_dir(sandbox.root.join("d")).unwrap();
    fs::write(sandbox.root.join("d/inner"), "SECRETB").unwrap();
    fs::write(sandbox.root.join("dx"), "NOTINDIR").unwrap();
    vsh::commands::rm(&mut state, "d/inner", false).unwrap();
    vsh::commands::rm(&mut state, "dx", false).unwrap();

    obliterate_path(&mut state, "d", false, true).unwrap();

    let inner = state
        .history
        .iter()
        .find(|op| op.path == "d/inner")
        .unwrap();
    assert!(inner.undo_data.is_none() && inner.undone);
    // `dx` only shares a prefix with `d`; it is not inside it.
    let sibling = state.history.iter().find(|op| op.path == "dx").unwrap();
    assert_eq!(sibling.undo_data.as_deref(), Some(&b"NOTINDIR"[..]));
    assert!(!sibling.undone);
}

#[test]
fn the_session_root_itself_cannot_be_obliterated() {
    let (sandbox, mut state) = sandbox();
    fs::write(sandbox.root.join("f"), "DATA").unwrap();
    assert!(obliterate_path(&mut state, ".", false, true).is_err());
    assert_eq!(fs::read(sandbox.root.join("f")).unwrap(), b"DATA");
}

/// The history may hold a file's earlier content as undo data. Obliterate
/// forgets it and saves the history before it destroys anything. If that
/// save fails, the content would outlive the file in the saved state, so
/// nothing is obliterated. Before, the file was destroyed first and a failed
/// save was only a warning.
#[test]
fn nothing_is_destroyed_when_the_scrubbed_history_cannot_be_saved() {
    let (sandbox, mut state) = sandbox();
    fs::write(sandbox.root.join("f"), "SECRET").unwrap();
    fs::create_dir(sandbox.root.join("d")).unwrap();
    fs::write(sandbox.root.join("d/inner"), "INNER").unwrap();
    // A directory where the saved state should be: it cannot be written.
    let saved = sandbox.root.join(".vsh_state.json");
    let _ = fs::remove_file(&saved);
    fs::create_dir(&saved).unwrap();

    for target in ["f", "d"] {
        let refused = obliterate_path(&mut state, target, false, true).unwrap_err();
        assert!(
            format!("{refused:#}").contains("history could not be saved"),
            "{refused:#}"
        );
    }
    assert_eq!(fs::read(sandbox.root.join("f")).unwrap(), b"SECRET");
    assert_eq!(fs::read(sandbox.root.join("d/inner")).unwrap(), b"INNER");
}

// SPDX-License-Identifier: MPL-2.0
//! `obliterate` destroys only what it was pointed at.
//!
//! It must never follow a symbolic link, never overwrite a file that has
//! another name, never run inside a transaction, and never destroy anything
//! before its audit entry is written. When it refuses, nothing is changed.

#![cfg(unix)]

mod fixtures;

use fixtures::{sandbox, Sandbox};
use std::fs;
use std::os::unix::fs::symlink;
use vsh::commands::secure_deletion::{obliterate_path, secure_delete};
use vsh::state::ShellState;

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
    // The history takes a copy of each file's content, as it would have
    // from earlier work on them.
    for name in ["f", "d/inner"] {
        vsh::commands::rm(&mut state, name, false).unwrap();
        vsh::commands::undo(&mut state, 1, false).unwrap();
    }
    let holds = |state: &ShellState, content: &[u8]| {
        state
            .history
            .iter()
            .any(|op| op.undo_data.as_deref() == Some(content))
    };
    let redo_entries = state.get_redo_stack().len();
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
    // The files are still there, so the history must still be able to undo
    // what was done to them: the scrub is put back when the save fails.
    assert!(holds(&state, b"SECRET"));
    assert!(holds(&state, b"INNER"));
    assert_eq!(state.get_redo_stack().len(), redo_entries);
}

/// One file can have two names when a link inside the session root points
/// at its directory. Obliterating it under one name removes what the
/// history holds about it under the other. Comparing the names as written
/// left the other name's record, and the content in it, in place.
#[test]
fn obliterate_scrubs_what_the_history_holds_under_another_name() {
    let (sandbox, mut state) = sandbox();
    fs::create_dir(sandbox.root.join("real")).unwrap();
    fs::write(sandbox.root.join("real/secret"), "SECRET-CONTENT").unwrap();
    // The history takes a copy of the content under the name `real/secret`.
    vsh::commands::rm(&mut state, "real/secret", false).unwrap();
    vsh::commands::undo(&mut state, 1, false).unwrap();
    symlink("real", sandbox.root.join("alias")).unwrap();

    obliterate_path(&mut state, "alias/secret", false, true).unwrap();

    assert!(!sandbox.root.join("real/secret").exists());
    let holds_it =
        |op: &vsh::state::Operation| op.undo_data.as_deref() == Some(b"SECRET-CONTENT".as_slice());
    assert!(!state.history.iter().any(holds_it), "in the history");
    assert!(
        !state.get_redo_stack().iter().any(holds_it),
        "in the redo stack"
    );
    let reloaded = ShellState::new(sandbox.root.to_str().unwrap()).unwrap();
    assert!(!reloaded.history.iter().any(holds_it), "in the saved state");
}

/// Start the built shell in `root`. A redirection changes where the
/// process writes, so a case with one needs a process of its own.
fn shell(root: &std::path::Path, script: &str) -> std::process::Output {
    std::process::Command::new(env!("CARGO_BIN_EXE_vsh"))
        .arg("-r")
        .arg(root)
        .arg("-c")
        .arg(script)
        .current_dir(root)
        .env("NO_COLOR", "1")
        .env_remove("RUST_BACKTRACE")
        .stdin(std::process::Stdio::null())
        .output()
        .expect("start the built shell")
}

/// Whether an operation's undo data holds `content`.
fn holds(op: &vsh::state::Operation, content: &[u8]) -> bool {
    op.undo_data
        .as_deref()
        .is_some_and(|data| data.windows(content.len()).any(|part| part == content))
}

/// A write through a link saves the bytes of the link's target. The record
/// was kept under the link's name, so obliterating the target left its
/// earlier content in the saved history, and `undo` could bring it back.
/// The record is now kept under the file that was changed, so it is found
/// even when the link has been removed since.
#[test]
fn obliterate_scrubs_content_that_was_saved_through_a_link() {
    for remove_the_link_first in [false, true] {
        let (sandbox, _state) = sandbox();
        fs::write(sandbox.root.join("real"), "SECRET-THROUGH-LINK").unwrap();
        symlink("real", sandbox.root.join("alias")).unwrap();
        let mut script = String::from("echo replacement > alias; ");
        if remove_the_link_first {
            script.push_str("rm alias; ");
        }
        script.push_str("obliterate real --force");

        let output = shell(&sandbox.root, &script);

        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(!sandbox.root.join("real").exists());
        let reloaded = ShellState::new(sandbox.root.to_str().unwrap()).unwrap();
        assert!(
            !reloaded
                .history
                .iter()
                .any(|op| holds(op, b"SECRET-THROUGH-LINK")),
            "the saved history still holds the content (link removed first: \
             {remove_the_link_first})"
        );
    }
}

/// Operations that age out of the history are written to the archive with
/// their undo data. Obliterate scrubbed the history and left that copy.
#[test]
fn obliterate_scrubs_the_history_archive_too() {
    let (sandbox, mut state) = sandbox();
    let archive = sandbox.outside.join("history-archive.jsonl");
    state.max_history_size = Some(1);
    state.history_archive_path = Some(archive.clone());
    fs::write(sandbox.root.join("f"), "ARCHIVED-SECRET").unwrap();
    fs::write(sandbox.root.join("other"), "OTHER-CONTENT").unwrap();
    // The removal of `f` holds its content. Undoing it puts `f` back, and
    // the next operation pushes that record out of the history, into the
    // archive.
    vsh::commands::rm(&mut state, "f", false).unwrap();
    vsh::commands::undo(&mut state, 1, false).unwrap();
    vsh::commands::rm(&mut state, "other", false).unwrap();
    let archived = |archive: &std::path::Path| -> Vec<vsh::state::Operation> {
        fs::read_to_string(archive)
            .unwrap()
            .lines()
            .map(|line| serde_json::from_str(line).unwrap())
            .collect()
    };
    assert!(
        archived(&archive)
            .iter()
            .any(|op| holds(op, b"ARCHIVED-SECRET")),
        "the set-up did not put the content into the archive"
    );

    obliterate_path(&mut state, "f", false, true).unwrap();

    let after = archived(&archive);
    assert!(
        !after.iter().any(|op| holds(op, b"ARCHIVED-SECRET")),
        "the archive still holds the content"
    );
    // The record of `f` is still there, without the content, and what the
    // archive holds about another path is untouched.
    assert!(after.iter().any(|op| op.path == "f"));
    assert!(after.iter().any(|op| holds(op, b"OTHER-CONTENT")));
}

/// The audit entries name the path as the history records it, relative to
/// the session root. They used to carry the path as it was typed, so an
/// obliteration made in `sub` was audited as `f` and recorded as `sub/f`.
#[test]
fn an_obliteration_below_the_root_is_audited_under_the_path_the_history_records() {
    let (sandbox, mut state) = sandbox();
    fs::create_dir(sandbox.root.join("sub")).unwrap();
    fs::write(sandbox.root.join("sub/f"), "CONTENT").unwrap();
    state.set_cwd(&sandbox.root.join("sub")).unwrap();

    obliterate_path(&mut state, "f", false, true).unwrap();

    assert_eq!(state.history.last().unwrap().path, "sub/f");
    let log = audit_log(&sandbox);
    let paths: Vec<String> = log
        .lines()
        .map(|line| serde_json::from_str::<serde_json::Value>(line).unwrap())
        .map(|entry| entry["path"].as_str().unwrap().to_string())
        .collect();
    assert_eq!(paths, ["sub/f", "sub/f"], "{log}");
}

/// An obliteration that fails after it has begun is recorded as failed.
/// By then the intent is in the audit log and the history has been
/// scrubbed. The error used to be returned with nothing more written: an
/// intent with no outcome, and no record in the history, although data
/// was gone.
///
/// The shell walks the directory, then asks. While it waits, a file is put
/// where the walk did not see one, so the directory cannot be removed
/// after its files have been destroyed.
#[test]
fn an_obliteration_that_fails_part_way_is_recorded_as_failed() {
    use std::io::{Read, Write};
    use std::process::{Command, Stdio};

    let (sandbox, _state) = sandbox();
    fs::create_dir_all(sandbox.root.join("dir/inner")).unwrap();
    fs::write(sandbox.root.join("dir/a"), "CONTENT").unwrap();

    let mut child = Command::new(env!("CARGO_BIN_EXE_vsh"))
        .arg("-r")
        .arg(&sandbox.root)
        .arg("-c")
        .arg("obliterate dir")
        .current_dir(&sandbox.root)
        .env("NO_COLOR", "1")
        .env_remove("RUST_BACKTRACE")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("start the built shell");
    let mut stdout = child.stdout.take().unwrap();
    let mut seen = Vec::new();
    let mut byte = [0u8; 1];
    while !seen.ends_with(b"[y/N] ") {
        assert_eq!(
            stdout.read(&mut byte).unwrap(),
            1,
            "the shell ended before it asked: {}",
            String::from_utf8_lossy(&seen)
        );
        seen.push(byte[0]);
    }
    fs::write(sandbox.root.join("dir/inner/late"), "LATE").unwrap();
    child.stdin.take().unwrap().write_all(b"y\n").unwrap();
    let status = child.wait().unwrap();

    assert!(!status.success(), "the command must report the failure");
    assert!(!sandbox.root.join("dir/a").exists(), "`a` was destroyed");
    assert!(sandbox.root.join("dir/inner/late").exists());
    let log = audit_log(&sandbox);
    assert!(log.contains("obliterate-dir-intent"), "{log}");
    assert!(
        log.contains("obliterate-dir-failed-after-1-of-1-files"),
        "{log}"
    );
    let reloaded = ShellState::new(sandbox.root.to_str().unwrap()).unwrap();
    assert!(
        reloaded
            .history
            .iter()
            .any(|op| op.op_type == vsh::state::OperationType::Obliterate && op.path == "dir"),
        "the history has no record of the obliteration"
    );
}

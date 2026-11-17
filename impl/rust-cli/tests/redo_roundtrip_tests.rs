// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! Undo / redo / undo round-trip regression tests.
//!
//! `redo` used to re-execute an operation and record it again with no undo
//! data, so a second undo could not restore the earlier state (`rm f; undo;
//! redo; undo` brought `f` back empty). These tests pin the exact round trip
//! for `rm`, `chmod`, `cp` and `ln -s`: contents are compared byte for byte
//! and modes bit for bit.
//!
//! These are tests of the Rust implementation only. They are `tested-only`
//! evidence for the undo/redo round-trip behaviour that the Lean/Coq theorems
//! assume of the model; they are not a mechanised correspondence proof.

use std::fs;
use std::path::Path;

use tempfile::TempDir;
use vsh::commands;
use vsh::state::{OperationType, ShellState};

/// Bytes that are not valid UTF-8 and contain NUL, CR and LF, so a restore
/// that goes through a `String` or trims anything is caught.
const BINARY: &[u8] = &[
    0x00, 0xff, 0xfe, b'\r', b'\n', 0x80, b'h', b'i', 0x00, b'\n',
];

fn setup() -> (TempDir, ShellState) {
    let temp = TempDir::new().expect("tempdir");
    let state = ShellState::new(temp.path().to_str().expect("utf8")).expect("state");
    (temp, state)
}

fn undo(state: &mut ShellState) {
    commands::undo(state, 1, false).expect("undo");
}

fn redo(state: &mut ShellState) {
    commands::redo(state, 1, false).expect("redo");
}

fn read(path: &Path) -> Vec<u8> {
    fs::read(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

#[cfg(unix)]
fn mode_of(path: &Path) -> u32 {
    use std::os::unix::fs::PermissionsExt;
    fs::symlink_metadata(path)
        .unwrap_or_else(|e| panic!("stat {}: {e}", path.display()))
        .permissions()
        .mode()
        & 0o7777
}

#[cfg(unix)]
fn set_mode(path: &Path, mode: u32) {
    use std::os::unix::fs::PermissionsExt;
    fs::set_permissions(path, fs::Permissions::from_mode(mode)).expect("set mode");
}

// ---------------------------------------------------------------------------
// rm
// ---------------------------------------------------------------------------

/// The reported reproduction: `rm f; undo; redo; undo` must restore "hello".
#[test]
fn rm_undo_redo_undo_restores_content() {
    let (temp, mut state) = setup();
    let f = temp.path().join("f");
    fs::write(&f, b"hello").unwrap();

    commands::rm(&mut state, "f", false).unwrap();
    assert!(!f.exists());

    undo(&mut state);
    assert_eq!(read(&f), b"hello");

    redo(&mut state);
    assert!(!f.exists(), "redo rm must remove the file again");

    undo(&mut state);
    assert_eq!(read(&f), b"hello", "second undo must restore the content");
}

/// Same round trip with non-UTF-8 content, repeated, so the bytes survive
/// any number of undo/redo cycles.
#[test]
fn rm_roundtrip_is_byte_exact_over_many_cycles() {
    let (temp, mut state) = setup();
    let f = temp.path().join("blob.bin");
    fs::write(&f, BINARY).unwrap();

    commands::rm(&mut state, "blob.bin", false).unwrap();

    for cycle in 0..5 {
        undo(&mut state);
        assert_eq!(read(&f), BINARY, "cycle {cycle}: undo");
        redo(&mut state);
        assert!(!f.exists(), "cycle {cycle}: redo");
    }

    undo(&mut state);
    assert_eq!(read(&f), BINARY);
}

/// The operation `redo` records must carry the same undo data the original
/// `rm` captured.
#[test]
fn rm_redo_records_the_undo_data_rm_captured() {
    let (temp, mut state) = setup();
    fs::write(temp.path().join("f"), BINARY).unwrap();

    commands::rm(&mut state, "f", false).unwrap();
    let original = state.history.last().unwrap().undo_data.clone();
    assert_eq!(original.as_deref(), Some(BINARY));

    undo(&mut state);
    redo(&mut state);

    let redone = state.history.last().unwrap();
    assert_eq!(redone.op_type, OperationType::DeleteFile);
    assert!(!redone.undone);
    assert_eq!(redone.undo_data, original);
}

/// The file's mode is not part of what `rm` records, so this only pins that
/// redo of an `rm` whose file was changed between undo and redo captures the
/// content that redo actually deleted, not the content of the first `rm`.
#[test]
fn rm_redo_recaptures_content_present_at_redo_time() {
    let (temp, mut state) = setup();
    let f = temp.path().join("f");
    fs::write(&f, b"first").unwrap();

    commands::rm(&mut state, "f", false).unwrap();
    undo(&mut state);

    // Changed outside the shell between undo and redo.
    fs::write(&f, b"second, and longer").unwrap();

    redo(&mut state);
    assert!(!f.exists());

    undo(&mut state);
    assert_eq!(read(&f), b"second, and longer");
}

// ---------------------------------------------------------------------------
// chmod
// ---------------------------------------------------------------------------

#[cfg(unix)]
#[test]
fn chmod_undo_redo_undo_restores_mode() {
    let (temp, mut state) = setup();
    let f = temp.path().join("f");
    fs::write(&f, b"hello").unwrap();
    set_mode(&f, 0o644);

    commands::chmod(&mut state, "600", "f", false).unwrap();
    assert_eq!(mode_of(&f), 0o600);

    undo(&mut state);
    assert_eq!(mode_of(&f), 0o644);

    redo(&mut state);
    assert_eq!(mode_of(&f), 0o600, "redo chmod must re-apply the mode");

    undo(&mut state);
    assert_eq!(mode_of(&f), 0o644, "second undo must restore the old mode");

    assert_eq!(
        read(&f),
        b"hello",
        "chmod round trip must not touch content"
    );
}

/// A symbolic mode is relative to the mode at the time of the command. Redo
/// must land on the same resulting mode, over repeated cycles, including the
/// setuid/setgid/sticky bits.
#[cfg(unix)]
#[test]
fn chmod_symbolic_roundtrip_over_many_cycles() {
    let (temp, mut state) = setup();
    let f = temp.path().join("f");
    fs::write(&f, b"x").unwrap();
    set_mode(&f, 0o1640);

    commands::chmod(&mut state, "u+x", "f", false).unwrap();
    assert_eq!(mode_of(&f), 0o1740);

    for cycle in 0..4 {
        undo(&mut state);
        assert_eq!(mode_of(&f), 0o1640, "cycle {cycle}: undo");
        redo(&mut state);
        assert_eq!(mode_of(&f), 0o1740, "cycle {cycle}: redo");
    }

    undo(&mut state);
    assert_eq!(mode_of(&f), 0o1640);
}

/// Two stacked chmods: every intermediate mode comes back in order.
#[cfg(unix)]
#[test]
fn chmod_stacked_roundtrip() {
    let (temp, mut state) = setup();
    let f = temp.path().join("f");
    fs::write(&f, b"x").unwrap();
    set_mode(&f, 0o644);

    commands::chmod(&mut state, "600", "f", false).unwrap();
    commands::chmod(&mut state, "755", "f", false).unwrap();

    commands::undo(&mut state, 2, false).unwrap();
    assert_eq!(mode_of(&f), 0o644);

    commands::redo(&mut state, 2, false).unwrap();
    assert_eq!(mode_of(&f), 0o755);

    undo(&mut state);
    assert_eq!(mode_of(&f), 0o600);
    undo(&mut state);
    assert_eq!(mode_of(&f), 0o644);
}

// ---------------------------------------------------------------------------
// cp
// ---------------------------------------------------------------------------

#[test]
fn cp_undo_redo_undo_redo_roundtrip() {
    let (temp, mut state) = setup();
    let src = temp.path().join("src.bin");
    let dst = temp.path().join("dst.bin");
    fs::write(&src, BINARY).unwrap();

    commands::cp(&mut state, "src.bin", "dst.bin", false).unwrap();
    assert_eq!(read(&dst), BINARY);

    for cycle in 0..3 {
        undo(&mut state);
        assert!(!dst.exists(), "cycle {cycle}: undo cp removes the copy");
        assert_eq!(read(&src), BINARY, "cycle {cycle}: source untouched");

        redo(&mut state);
        assert_eq!(read(&dst), BINARY, "cycle {cycle}: redo cp copies again");
        assert_eq!(read(&src), BINARY, "cycle {cycle}: source untouched");
    }

    undo(&mut state);
    assert!(!dst.exists());
    assert_eq!(read(&src), BINARY);
}

/// The operation `redo` records must carry the same data the original `cp`
/// recorded (the source path), or a later redo has nothing to copy from.
#[test]
fn cp_redo_records_the_data_cp_recorded() {
    let (temp, mut state) = setup();
    fs::write(temp.path().join("src"), b"data").unwrap();

    commands::cp(&mut state, "src", "dst", false).unwrap();
    let original = state.history.last().unwrap().undo_data.clone();
    assert_eq!(original.as_deref(), Some(b"src".as_slice()));

    undo(&mut state);
    redo(&mut state);

    let redone = state.history.last().unwrap();
    assert_eq!(redone.op_type, OperationType::CopyFile);
    assert_eq!(redone.path, "dst");
    assert_eq!(redone.undo_data, original);
}

/// `cp` refuses an existing destination. Redo must not be a way around that:
/// a destination that appeared between undo and redo is not overwritten, and
/// the redo entry is kept so redo works once the way is clear.
#[test]
fn cp_redo_does_not_overwrite_a_destination_that_reappeared() {
    let (temp, mut state) = setup();
    let src = temp.path().join("src");
    let dst = temp.path().join("dst");
    fs::write(&src, b"from source").unwrap();

    commands::cp(&mut state, "src", "dst", false).unwrap();
    undo(&mut state);
    assert!(!dst.exists());

    // Created outside the shell between undo and redo.
    fs::write(&dst, BINARY).unwrap();

    let history_len = state.history.len();
    assert!(
        commands::redo(&mut state, 1, false).is_err(),
        "redo cp over an existing destination must fail"
    );
    assert_eq!(read(&dst), BINARY, "the existing destination is intact");
    assert_eq!(
        state.history.len(),
        history_len,
        "a failed redo records nothing"
    );

    // Once the obstacle is gone the same redo still works.
    fs::remove_file(&dst).unwrap();
    redo(&mut state);
    assert_eq!(read(&dst), b"from source");

    undo(&mut state);
    assert!(!dst.exists());
}

// ---------------------------------------------------------------------------
// ln -s
// ---------------------------------------------------------------------------

#[cfg(unix)]
#[test]
fn symlink_undo_redo_undo_redo_roundtrip() {
    let (temp, mut state) = setup();
    let real = temp.path().join("real.bin");
    let link = temp.path().join("link");
    fs::write(&real, BINARY).unwrap();

    commands::symlink(&mut state, "real.bin", "link", false).unwrap();
    assert_eq!(fs::read_link(&link).unwrap(), Path::new("real.bin"));

    for cycle in 0..3 {
        undo(&mut state);
        assert!(
            fs::symlink_metadata(&link).is_err(),
            "cycle {cycle}: undo ln -s removes the link"
        );
        assert_eq!(read(&real), BINARY, "cycle {cycle}: target untouched");

        redo(&mut state);
        assert_eq!(
            fs::read_link(&link).unwrap(),
            Path::new("real.bin"),
            "cycle {cycle}: redo ln -s points at the same target"
        );
        assert_eq!(read(&link), BINARY, "cycle {cycle}: link resolves");
        assert_eq!(read(&real), BINARY, "cycle {cycle}: target untouched");
    }

    undo(&mut state);
    assert!(fs::symlink_metadata(&link).is_err());
    assert_eq!(read(&real), BINARY);
}

/// The operation `redo` records must carry the link target the original
/// `ln -s` recorded.
#[cfg(unix)]
#[test]
fn symlink_redo_records_the_target_ln_recorded() {
    let (temp, mut state) = setup();
    fs::write(temp.path().join("real"), b"x").unwrap();

    commands::symlink(&mut state, "real", "link", false).unwrap();
    let original = state.history.last().unwrap().undo_data.clone();
    assert_eq!(original.as_deref(), Some(b"real".as_slice()));

    undo(&mut state);
    redo(&mut state);

    let redone = state.history.last().unwrap();
    assert_eq!(redone.op_type, OperationType::Symlink);
    assert_eq!(redone.path, "link");
    assert_eq!(redone.undo_data, original);
}

/// `ln -s` refuses an existing link path. A file that appeared at the link
/// path between undo and redo is left intact, byte for byte, and the redo
/// entry is kept.
#[cfg(unix)]
#[test]
fn symlink_redo_does_not_replace_a_file_that_reappeared() {
    let (temp, mut state) = setup();
    let link = temp.path().join("link");
    fs::write(temp.path().join("real"), b"x").unwrap();

    commands::symlink(&mut state, "real", "link", false).unwrap();
    undo(&mut state);

    // Created outside the shell between undo and redo.
    fs::write(&link, BINARY).unwrap();

    let history_len = state.history.len();
    assert!(
        commands::redo(&mut state, 1, false).is_err(),
        "redo ln -s over an existing path must fail"
    );
    assert!(!fs::symlink_metadata(&link)
        .unwrap()
        .file_type()
        .is_symlink());
    assert_eq!(read(&link), BINARY, "the existing file is intact");
    assert_eq!(
        state.history.len(),
        history_len,
        "a failed redo records nothing"
    );

    fs::remove_file(&link).unwrap();
    redo(&mut state);
    assert_eq!(fs::read_link(&link).unwrap(), Path::new("real"));
}

// ---------------------------------------------------------------------------
// Redo re-checks preconditions (mv, touch)
// ---------------------------------------------------------------------------

/// `mv` refuses an existing destination; `fs::rename` alone would replace it.
#[test]
fn mv_redo_does_not_overwrite_a_destination_that_reappeared() {
    let (temp, mut state) = setup();
    let src = temp.path().join("src");
    let dst = temp.path().join("dst");
    fs::write(&src, b"moved").unwrap();

    commands::mv(&mut state, "src", "dst", false).unwrap();
    undo(&mut state);
    assert_eq!(read(&src), b"moved");

    // Created outside the shell between undo and redo.
    fs::write(&dst, BINARY).unwrap();

    assert!(commands::redo(&mut state, 1, false).is_err());
    assert_eq!(read(&dst), BINARY, "the existing destination is intact");
    assert_eq!(read(&src), b"moved", "the source was not moved");

    fs::remove_file(&dst).unwrap();
    redo(&mut state);
    assert_eq!(read(&dst), b"moved");
    assert!(!src.exists());
}

/// `touch` refuses an existing path; redo used to truncate whatever was there.
#[test]
fn touch_redo_does_not_truncate_a_file_that_reappeared() {
    let (temp, mut state) = setup();
    let f = temp.path().join("f");

    commands::touch(&mut state, "f", false).unwrap();
    undo(&mut state);
    assert!(!f.exists());

    // Created outside the shell between undo and redo.
    fs::write(&f, BINARY).unwrap();

    assert!(commands::redo(&mut state, 1, false).is_err());
    assert_eq!(read(&f), BINARY, "the existing file is intact");
}

/// `touch` on a dangling symbolic link fails and creates nothing: it must not
/// write through the link to a file the history knows nothing about.
#[cfg(unix)]
#[test]
fn touch_does_not_write_through_a_dangling_symlink() {
    let (temp, mut state) = setup();
    std::os::unix::fs::symlink("elsewhere", temp.path().join("f")).unwrap();

    assert!(commands::touch(&mut state, "f", false).is_err());
    assert!(!temp.path().join("elsewhere").exists());
    assert!(state.history.is_empty());
}

// ---------------------------------------------------------------------------
// Dangling symbolic links at a destination; content that was not captured
// ---------------------------------------------------------------------------

/// A dangling symbolic link at the destination does not "exist" to
/// `Path::exists`, and `cp` onto it would write through the link to wherever
/// it points, which may be outside the sandbox. The runtime precondition
/// check (`verification::verify_copy_file`, which uses `lstat`) treats it as
/// occupied; this pins that for `cp` and for its redo.
#[cfg(unix)]
#[test]
fn cp_and_its_redo_refuse_a_dangling_symlink_destination() {
    let (temp, mut state) = setup();
    let outside = TempDir::new().expect("tempdir");
    let escape = outside.path().join("escape");
    let dst = temp.path().join("dst");
    fs::write(temp.path().join("src"), b"payload").unwrap();

    commands::cp(&mut state, "src", "dst", false).unwrap();
    undo(&mut state);

    // Planted between undo and redo: dst -> a path outside the sandbox.
    std::os::unix::fs::symlink(&escape, &dst).unwrap();

    assert!(commands::redo(&mut state, 1, false).is_err());
    assert!(!escape.exists(), "redo did not write through the link");
    assert_eq!(fs::read_link(&dst).unwrap(), escape, "the link is intact");
    assert_eq!(state.get_redo_stack().len(), 1, "the entry is kept");

    // The command itself refuses too.
    assert!(commands::cp(&mut state, "src", "dst", false).is_err());
    assert!(!escape.exists());
}

/// `mv` onto a dangling symbolic link would replace the link;
/// `verification::verify_move` refuses it, for the command and for its redo.
#[cfg(unix)]
#[test]
fn mv_and_its_redo_refuse_a_dangling_symlink_destination() {
    let (temp, mut state) = setup();
    let src = temp.path().join("src");
    let dst = temp.path().join("dst");
    fs::write(&src, b"payload").unwrap();

    commands::mv(&mut state, "src", "dst", false).unwrap();
    undo(&mut state);

    std::os::unix::fs::symlink("nowhere", &dst).unwrap();

    assert!(commands::redo(&mut state, 1, false).is_err());
    assert_eq!(fs::read_link(&dst).unwrap(), Path::new("nowhere"));
    assert_eq!(read(&src), b"payload", "the source was not moved");

    assert!(commands::mv(&mut state, "src", "dst", false).is_err());
    assert_eq!(fs::read_link(&dst).unwrap(), Path::new("nowhere"));
}

/// If undo could not read a file's content, redo must refuse to recreate the
/// file: recreating it empty would silently lose what was in it.
#[test]
fn redo_refuses_a_file_whose_content_was_not_captured() {
    use vsh::state::RedoData;

    let (temp, mut state) = setup();
    let f = temp.path().join("f");

    commands::touch(&mut state, "f", false).unwrap();
    fs::write(&f, b"written after the touch").unwrap();
    undo(&mut state);
    assert!(!f.exists());

    // What undo records when the read fails (see the unit test of
    // `capture_redo_data` for the capture side).
    let entry = state.redo_stack.front_mut().expect("redo entry");
    assert!(matches!(entry.redo_data, Some(RedoData::Created { .. })));
    entry.redo_data = Some(RedoData::NotCaptured("Permission denied".to_string()));

    let err = commands::redo(&mut state, 1, false).expect_err("redo must refuse");
    assert!(err.to_string().contains("could not be read"), "{err}");
    assert!(!f.exists(), "nothing was recreated");
    assert_eq!(state.get_redo_stack().len(), 1, "the entry is kept");
}

/// `cp` gives the copy the source's mode, for the command and for its redo,
/// and the copy is never created with a wider mode than the source.
#[cfg(unix)]
#[test]
fn cp_and_its_redo_keep_the_source_mode() {
    let (temp, mut state) = setup();
    let src = temp.path().join("secret");
    let dst = temp.path().join("copy");
    fs::write(&src, BINARY).unwrap();
    set_mode(&src, 0o600);

    commands::cp(&mut state, "secret", "copy", false).unwrap();
    assert_eq!(mode_of(&dst), 0o600);
    assert_eq!(read(&dst), BINARY);

    undo(&mut state);
    redo(&mut state);
    assert_eq!(mode_of(&dst), 0o600);
    assert_eq!(read(&dst), BINARY);
}

/// Redo of an assignment restores the export state undo found, in both
/// directions: here the variable was not exported, and something outside the
/// history exported it between undo and redo.
#[test]
fn assignment_redo_restores_not_exported() {
    use vsh::executable::ExecutableCommand;
    use vsh::parser::parse_command;

    let (_temp, mut state) = setup();
    parse_command("X=1").unwrap().execute(&mut state).unwrap();
    assert!(!state.is_exported("X"));

    undo(&mut state);
    assert_eq!(state.get_variable("X"), None);

    // Outside the history: these calls record nothing.
    state.set_variable("X", "other");
    state.export_variable("X");

    redo(&mut state);
    assert_eq!(state.get_variable("X"), Some("1"));
    assert!(
        !state.is_exported("X"),
        "redo restores the unexported state"
    );
}

/// A variable that is no longer set when its assignment is undone is a state
/// redo must restore, not a failed capture. Shell functions do this: an
/// assignment inside a function is recorded, and returning from the function
/// removes the variable without a record.
#[test]
fn assignment_redo_restores_a_variable_that_was_not_set() {
    use vsh::executable::ExecutableCommand;
    use vsh::parser::parse_command;

    let (_temp, mut state) = setup();
    parse_command("X=1").unwrap().execute(&mut state).unwrap();
    parse_command("X=2").unwrap().execute(&mut state).unwrap();
    // Outside the history: this call records nothing.
    state.unset_variable("X");

    for cycle in 0..3 {
        undo(&mut state);
        assert_eq!(state.get_variable("X"), Some("1"), "cycle {cycle}: undo");
        redo(&mut state);
        assert_eq!(state.get_variable("X"), None, "cycle {cycle}: redo");
    }
}

/// Redo of `unset` when the variable is already not set (removed outside the
/// history after the undo restored it) is the state redo is asked for. It
/// succeeds and does not block the redo stack.
#[test]
fn unset_redo_succeeds_when_the_variable_is_already_not_set() {
    use vsh::executable::ExecutableCommand;
    use vsh::parser::parse_command;

    let (_temp, mut state) = setup();
    parse_command("X=1").unwrap().execute(&mut state).unwrap();
    parse_command("unset X")
        .unwrap()
        .execute(&mut state)
        .unwrap();
    undo(&mut state);
    assert_eq!(state.get_variable("X"), Some("1"));
    // Outside the history: this call records nothing.
    state.unset_variable("X");

    redo(&mut state);
    assert_eq!(state.get_variable("X"), None);
    assert!(state.get_redo_stack().is_empty());
    // Undo of that redo has nothing to restore: the variable was not set.
    undo(&mut state);
    assert_eq!(state.get_variable("X"), None);
}

/// Undo of an append cuts the file back to its earlier size. If the file is
/// already shorter than that (cut outside the history), undo must not grow
/// it with zero bytes, and redo must leave it as undo found it.
#[test]
fn append_undo_never_grows_a_file_that_was_cut_shorter() {
    use vsh::executable::ExecutableCommand;
    use vsh::parser::parse_command;

    let (temp, mut state) = setup();
    let f = temp.path().join("f");
    fs::write(&f, b"0123456789").unwrap();
    parse_command("/bin/echo hi >> f")
        .unwrap()
        .execute(&mut state)
        .unwrap();
    assert_eq!(read(&f), b"0123456789hi\n");
    // Outside the history.
    fs::write(&f, b"012").unwrap();

    undo(&mut state);
    assert_eq!(read(&f), b"012", "undo must not extend the file");
    redo(&mut state);
    assert_eq!(read(&f), b"012", "redo restores what undo found");
    undo(&mut state);
    assert_eq!(read(&f), b"012");
}

// ---------------------------------------------------------------------------
// The mode of a file that undo deletes
// ---------------------------------------------------------------------------

/// Undo of `touch` deletes the file. If its mode was changed outside the
/// history in the meantime, redo must bring the file back with that mode,
/// not with the default one: a private file must not return readable by all.
#[cfg(unix)]
#[test]
fn touch_redo_restores_the_mode_the_file_had_when_it_was_undone() {
    let (temp, mut state) = setup();
    let f = temp.path().join("f");

    commands::touch(&mut state, "f", false).unwrap();
    for mode in [0o600, 0o400, 0o4755, 0o666, 0o640] {
        set_mode(&f, mode);
        undo(&mut state);
        assert!(!f.exists());
        redo(&mut state);
        assert_eq!(mode_of(&f), mode, "redo after undo at mode {mode:o}");
    }
}

/// The same for a file a redirection created, with its content.
#[cfg(unix)]
#[test]
fn redirect_redo_restores_content_and_mode() {
    use vsh::executable::ExecutableCommand;
    let (temp, mut state) = setup();
    let f = temp.path().join("new");

    vsh::parser::parse_command("/bin/echo hi > new")
        .unwrap()
        .execute(&mut state)
        .unwrap();
    assert_eq!(read(&f), b"hi\n");
    set_mode(&f, 0o600);

    undo(&mut state);
    assert!(!f.exists());
    redo(&mut state);
    assert_eq!(read(&f), b"hi\n");
    assert_eq!(mode_of(&f), 0o600);
}

// ---------------------------------------------------------------------------
// Mixed sequence
// ---------------------------------------------------------------------------

/// All four operations in one history: undo everything, redo everything,
/// undo everything again. Every state is the one first observed.
#[cfg(unix)]
#[test]
fn mixed_sequence_undo_all_redo_all_undo_all() {
    let (temp, mut state) = setup();
    let root = temp.path();
    fs::write(root.join("a"), BINARY).unwrap();
    fs::write(root.join("gone"), b"hello").unwrap();
    set_mode(&root.join("a"), 0o644);

    commands::cp(&mut state, "a", "b", false).unwrap();
    commands::symlink(&mut state, "a", "l", false).unwrap();
    commands::chmod(&mut state, "400", "a", false).unwrap();
    commands::rm(&mut state, "gone", false).unwrap();

    let assert_after = |when: &str| {
        assert_eq!(read(&root.join("b")), BINARY, "{when}: copy");
        assert_eq!(
            fs::read_link(root.join("l")).unwrap(),
            Path::new("a"),
            "{when}: link"
        );
        assert_eq!(mode_of(&root.join("a")), 0o400, "{when}: mode");
        assert!(!root.join("gone").exists(), "{when}: rm");
    };
    let assert_before = |when: &str| {
        assert!(!root.join("b").exists(), "{when}: copy");
        assert!(
            fs::symlink_metadata(root.join("l")).is_err(),
            "{when}: link"
        );
        assert_eq!(mode_of(&root.join("a")), 0o644, "{when}: mode");
        assert_eq!(read(&root.join("gone")), b"hello", "{when}: rm");
        assert_eq!(read(&root.join("a")), BINARY, "{when}: source");
    };

    assert_after("applied");
    commands::undo(&mut state, 4, false).unwrap();
    assert_before("first undo");
    commands::redo(&mut state, 4, false).unwrap();
    assert_after("redo");
    commands::undo(&mut state, 4, false).unwrap();
    assert_before("second undo");
}

// ---------------------------------------------------------------------------
// The round-trip law, for every operation that can reach the history
// ---------------------------------------------------------------------------

/// Whole-sandbox comparison: every operation type is driven through the real
/// parse -> execute path, and the sandbox (kinds, bytes, modes, owners, link
/// targets) plus the tracked shell variable is compared after each step.
#[cfg(unix)]
mod laws {
    use std::collections::BTreeMap;
    use std::fs;
    use std::os::unix::fs::{MetadataExt, PermissionsExt};
    use std::path::Path;

    use proptest::prelude::*;
    use tempfile::TempDir;
    use vsh::commands;
    use vsh::executable::ExecutableCommand;
    use vsh::parser::parse_command;
    use vsh::state::ShellState;

    use super::BINARY;

    #[derive(Debug, Clone, PartialEq, Eq)]
    enum Entry {
        Dir {
            mode: u32,
            owner: (u32, u32),
        },
        File {
            bytes: Vec<u8>,
            mode: u32,
            owner: (u32, u32),
        },
        Link {
            target: String,
        },
    }

    /// Everything undo and redo are meant to preserve.
    #[derive(Debug, Clone, PartialEq, Eq)]
    struct Snapshot {
        fs: BTreeMap<String, Entry>,
        /// Value and exported flag of the shell variable `X`.
        x: (Option<String>, bool),
    }

    fn walk(root: &Path, dir: &Path, out: &mut BTreeMap<String, Entry>) {
        for entry in fs::read_dir(dir).expect("read_dir") {
            let entry = entry.expect("dir entry");
            // The shell's own state and audit files are not user data.
            if entry.file_name().to_string_lossy().starts_with(".vsh") {
                continue;
            }
            let path = entry.path();
            let rel = path
                .strip_prefix(root)
                .expect("under root")
                .to_string_lossy()
                .to_string();
            let meta = fs::symlink_metadata(&path).expect("stat");
            let owner = (meta.uid(), meta.gid());
            let mode = meta.permissions().mode() & 0o7777;
            if meta.file_type().is_symlink() {
                let target = fs::read_link(&path)
                    .expect("read_link")
                    .to_string_lossy()
                    .to_string();
                out.insert(rel, Entry::Link { target });
            } else if meta.is_dir() {
                out.insert(rel, Entry::Dir { mode, owner });
                walk(root, &path, out);
            } else {
                let bytes = fs::read(&path).expect("read");
                out.insert(rel, Entry::File { bytes, mode, owner });
            }
        }
    }

    fn snapshot(root: &Path, state: &ShellState) -> Snapshot {
        let mut fs_map = BTreeMap::new();
        walk(root, root, &mut fs_map);
        Snapshot {
            fs: fs_map,
            x: (
                state.get_variable("X").map(str::to_string),
                state.is_exported("X"),
            ),
        }
    }

    fn sandbox() -> (TempDir, ShellState) {
        let temp = TempDir::new().expect("tempdir");
        let state = ShellState::new(temp.path().to_str().expect("utf8")).expect("state");
        (temp, state)
    }

    fn run(state: &mut ShellState, line: &str) {
        parse_command(line)
            .unwrap_or_else(|e| panic!("parse {line:?}: {e}"))
            .execute(state)
            .unwrap_or_else(|e| panic!("execute {line:?}: {e}"));
    }

    fn put(root: &Path, name: &str, mode: u32) {
        let path = root.join(name);
        fs::write(&path, BINARY).expect("write");
        fs::set_permissions(&path, fs::Permissions::from_mode(mode)).expect("chmod");
    }

    fn is_root() -> bool {
        fs::metadata("/proc/self").map(|m| m.uid()).unwrap_or(1) == 0
    }

    struct Scenario {
        name: &'static str,
        setup: fn(&Path, &mut ShellState),
        /// The one command under test. Redirections use an external
        /// `/bin/echo`: the built-in `echo` writes through `println!`, which
        /// the test harness captures before it reaches the redirected file.
        line: &'static str,
        /// `false` where undo itself does not restore the original state.
        /// Those are defects in what the command records for undo, not in
        /// redo, and are out of scope here; the redo laws are still asserted.
        undo_is_exact: bool,
        needs_root: bool,
    }

    fn scenarios() -> Vec<Scenario> {
        let s = |name, setup, line| Scenario {
            name,
            setup,
            line,
            undo_is_exact: true,
            needs_root: false,
        };
        vec![
            s("mkdir", |_, _| {}, "mkdir d"),
            s(
                "rmdir",
                |r, _| fs::create_dir(r.join("d")).expect("mkdir"),
                "rmdir d",
            ),
            Scenario {
                // Known undo defect: rmdir does not record the directory's mode.
                undo_is_exact: false,
                ..s(
                    "rmdir of a 0700 directory",
                    |r, _| {
                        fs::create_dir(r.join("d")).expect("mkdir");
                        fs::set_permissions(r.join("d"), fs::Permissions::from_mode(0o700))
                            .expect("chmod");
                    },
                    "rmdir d",
                )
            },
            s("touch", |_, _| {}, "touch f"),
            s("rm", |r, _| put(r, "f", 0o644), "rm f"),
            Scenario {
                // Known undo defect: rm does not record the file's mode.
                undo_is_exact: false,
                ..s("rm of a 0600 file", |r, _| put(r, "f", 0o600), "rm f")
            },
            s("cp", |r, _| put(r, "a", 0o640), "cp a b"),
            s("mv", |r, _| put(r, "a", 0o640), "mv a b"),
            s("ln -s", |r, _| put(r, "a", 0o640), "ln -s a l"),
            s("chmod octal", |r, _| put(r, "f", 0o644), "chmod 600 f"),
            s("chmod symbolic", |r, _| put(r, "f", 0o1640), "chmod u+x f"),
            Scenario {
                needs_root: true,
                ..s("chown", |r, _| put(r, "f", 0o644), "chown 1000:1000 f")
            },
            // chmod and chown act on what a link points to, so the mode and
            // owner they record must be the target's, not the link's own.
            s(
                "chmod through a symlink",
                |r, _| {
                    put(r, "f", 0o600);
                    std::os::unix::fs::symlink("f", r.join("l")).expect("symlink");
                },
                "chmod 640 l",
            ),
            Scenario {
                needs_root: true,
                ..s(
                    "chown through a symlink",
                    |r, _| {
                        put(r, "f", 0o644);
                        std::os::unix::fs::symlink("f", r.join("l")).expect("symlink");
                    },
                    "chown 1000:1000 l",
                )
            },
            s("> creating a file", |_, _| {}, "/bin/echo hi > new"),
            s(
                "> replacing a file",
                |r, _| put(r, "f", 0o640),
                "/bin/echo hi > f",
            ),
            s(
                ">> appending to a file",
                |r, _| put(r, "f", 0o640),
                "/bin/echo hi >> f",
            ),
            s("assigning a new variable", |_, _| {}, "X=1"),
            s("reassigning a variable", |_, s| run(s, "X=1"), "X=2"),
            s("unset", |_, s| run(s, "X=1"), "unset X"),
            Scenario {
                // `export` is not a history operation, so undo reverses the
                // assignment before it and does not return to the unexported
                // state. Redo must bring back the value and the export.
                undo_is_exact: false,
                ..s(
                    "export after an assignment",
                    |_, s| run(s, "X=1"),
                    "export X",
                )
            },
            Scenario {
                // Known undo defect: unset does not record the exported flag.
                undo_is_exact: false,
                ..s(
                    "unset of an exported variable",
                    |_, s| {
                        run(s, "X=1");
                        run(s, "export X");
                    },
                    "unset X",
                )
            },
        ]
    }

    /// S0 -op-> S1 -undo-> A -redo-> B -undo-> C -redo-> D.
    /// Redo restores the state the operation produced (B == S1, D == S1), a
    /// second undo lands where the first did (C == A), and where the command
    /// records enough for undo, that is the original state (A == S0).
    #[test]
    fn every_operation_round_trips() {
        for sc in scenarios() {
            if sc.needs_root && !is_root() {
                eprintln!("skipping {:?}: needs root", sc.name);
                continue;
            }
            let (temp, mut state) = sandbox();
            let root = temp.path();
            (sc.setup)(root, &mut state);
            let s0 = snapshot(root, &state);
            run(&mut state, sc.line);
            let s1 = snapshot(root, &state);
            assert_ne!(s0, s1, "{}: the command changed nothing", sc.name);

            commands::undo(&mut state, 1, false)
                .unwrap_or_else(|e| panic!("{}: undo: {e}", sc.name));
            let a = snapshot(root, &state);
            assert_ne!(a, s1, "{}: undo changed nothing", sc.name);
            if sc.undo_is_exact {
                assert_eq!(a, s0, "{}: undo restores the original state", sc.name);
            }

            commands::redo(&mut state, 1, false)
                .unwrap_or_else(|e| panic!("{}: redo: {e}", sc.name));
            assert_eq!(
                snapshot(root, &state),
                s1,
                "{}: redo restores the state the command produced",
                sc.name
            );

            commands::undo(&mut state, 1, false)
                .unwrap_or_else(|e| panic!("{}: undo after redo: {e}", sc.name));
            assert_eq!(
                snapshot(root, &state),
                a,
                "{}: undo after redo lands where the first undo did",
                sc.name
            );

            commands::redo(&mut state, 1, false)
                .unwrap_or_else(|e| panic!("{}: second redo: {e}", sc.name));
            assert_eq!(
                snapshot(root, &state),
                s1,
                "{}: a second redo restores the state the command produced",
                sc.name
            );
        }
    }

    /// Undo of a redirection used to fail outright unless the sandbox root was
    /// `/`: the history held the resolved absolute path, which undo resolved
    /// under the root a second time.
    #[test]
    fn redirection_history_paths_are_relative_to_the_root() {
        let (temp, mut state) = sandbox();
        fs::create_dir(temp.path().join("sub")).expect("mkdir");
        run(&mut state, "/bin/echo hi > sub/out");
        assert_eq!(state.history.last().expect("recorded").path, "sub/out");

        commands::undo(&mut state, 1, false).expect("undo");
        assert!(!temp.path().join("sub/out").exists());
        commands::redo(&mut state, 1, false).expect("redo");
        assert_eq!(
            fs::read(temp.path().join("sub/out")).expect("read"),
            b"hi\n"
        );
    }

    // -- capture limit ------------------------------------------------------

    /// File content that undo keeps for redo is bounded. Over the limit, the
    /// undo still happens, redo of that entry fails with the reason, and the
    /// entry stays on the redo stack.
    #[test]
    fn content_over_the_capture_limit_is_not_kept_for_redo() {
        let (temp, mut state) = sandbox();
        let new = temp.path().join("new");
        state.set_variable(commands::REDO_CAPTURE_LIMIT_VAR, "2");
        run(&mut state, "/bin/echo hi > new");
        assert_eq!(fs::read(&new).expect("read"), b"hi\n");

        commands::undo(&mut state, 1, false).expect("undo is not limited");
        assert!(!new.exists());

        let err = commands::redo(&mut state, 1, false).expect_err("redo over the limit");
        let message = err.to_string();
        assert!(
            message.contains(commands::REDO_CAPTURE_LIMIT_VAR) && message.contains("3 bytes"),
            "the error names the limit and the size: {message}"
        );
        assert!(!new.exists(), "a refused redo creates nothing");
        assert_eq!(state.get_redo_stack().len(), 1, "the entry is kept");
    }

    /// `0` removes the limit; unset, the default applies.
    #[test]
    fn capture_limit_zero_is_unlimited_and_default_is_ten_mebibytes() {
        let size = commands::DEFAULT_REDO_CAPTURE_LIMIT as usize + 1;
        for (setting, redo_works) in [(None, false), (Some("0"), true)] {
            let (temp, mut state) = sandbox();
            let big = temp.path().join("big");
            fs::write(&big, vec![0xab_u8; size]).expect("write");
            if let Some(setting) = setting {
                state.set_variable(commands::REDO_CAPTURE_LIMIT_VAR, setting);
            }
            // External commands run in the process's directory, not the
            // sandbox root, so the source is named absolutely.
            run(&mut state, &format!("/bin/cat {} > new", big.display()));
            commands::undo(&mut state, 1, false).expect("undo");

            let redone = commands::redo(&mut state, 1, false);
            assert_eq!(redone.is_ok(), redo_works, "limit setting {setting:?}");
            if redo_works {
                let restored = fs::read(temp.path().join("new")).expect("read");
                assert!(restored == fs::read(&big).expect("read"), "bytes differ");
            }
        }
    }

    // -- random sequences ---------------------------------------------------

    /// One command line over a four-name namespace. Symbolic links are left
    /// out: `rm` and redirections follow them, and undo of those is a known,
    /// separate defect that would mask what is tested here.
    fn command_line() -> impl Strategy<Value = String> {
        let name = prop::sample::select(vec!["a", "b", "c", "d"]);
        let mode = prop::sample::select(vec!["600", "644", "640", "755", "700", "u+x"]);
        prop_oneof![
            name.clone().prop_map(|n| format!("mkdir {n}")),
            name.clone().prop_map(|n| format!("rmdir {n}")),
            name.clone().prop_map(|n| format!("touch {n}")),
            name.clone().prop_map(|n| format!("rm {n}")),
            (name.clone(), name.clone()).prop_map(|(n, m)| format!("cp {n} {m}")),
            (name.clone(), name.clone()).prop_map(|(n, m)| format!("mv {n} {m}")),
            (mode, name.clone()).prop_map(|(mode, n)| format!("chmod {mode} {n}")),
            (0..1000u32, name.clone()).prop_map(|(v, n)| format!("/bin/echo w{v} > {n}")),
            (0..1000u32, name).prop_map(|(v, n)| format!("/bin/echo a{v} >> {n}")),
            (0..5u32).prop_map(|v| format!("X={v}")),
            Just("unset X".to_string()),
            Just("export X".to_string()),
        ]
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(48))]

        /// Run a random sequence (commands whose preconditions fail record
        /// nothing), then undo everything, redo everything and undo
        /// everything again, one history entry at a time.
        ///
        /// * Redo inverts undo: redoing back up to k entries gives the state
        ///   undo left at k entries, and redoing all of them gives the state
        ///   the sequence ended in.
        /// * Undo is repeatable: the second pass of undos visits the same
        ///   states as the first.
        #[test]
        fn random_sequences_round_trip(lines in prop::collection::vec(command_line(), 1..12)) {
            let (temp, mut state) = sandbox();
            let root = temp.path();
            for line in &lines {
                if let Ok(command) = parse_command(line) {
                    let _ = command.execute(&mut state);
                }
            }
            let entries = state.history.len();
            let end = snapshot(root, &state);

            // after_undo[k] is the state with k entries still applied.
            let mut after_undo = vec![end.clone(); entries + 1];
            for k in (0..entries).rev() {
                commands::undo(&mut state, 1, false)
                    .map_err(|e| TestCaseError::fail(format!("undo to {k}: {e}")))?;
                after_undo[k] = snapshot(root, &state);
            }
            for (k, want) in after_undo.iter().enumerate().skip(1) {
                commands::redo(&mut state, 1, false)
                    .map_err(|e| TestCaseError::fail(format!("redo to {k}: {e}")))?;
                prop_assert_eq!(&snapshot(root, &state), want, "redo to {} entries", k);
            }
            prop_assert_eq!(&snapshot(root, &state), &end);
            for k in (0..entries).rev() {
                commands::undo(&mut state, 1, false)
                    .map_err(|e| TestCaseError::fail(format!("second undo to {k}: {e}")))?;
                prop_assert_eq!(
                    &snapshot(root, &state),
                    &after_undo[k],
                    "second undo to {} entries",
                    k
                );
            }
        }
    }
}

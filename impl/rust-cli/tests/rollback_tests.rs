// SPDX-License-Identifier: MPL-2.0
//! Transaction rollback: what it reverses, what it marks, and when it
//! refuses.
//!
//! The rules under test (owner rulings 2026-11-17, route plan section 14):
//!
//! * Rollback marks each operation it reverses as undone, so a later `undo`
//!   does not try to reverse it again, and `redo` can bring it back.
//! * Before reversing anything, rollback checks every operation's record.
//!   If one cannot be reversed, the rollback is refused and nothing changes.
//! * If a reversal fails on the disk, the transaction stays open, and the
//!   rollback can be run again.

mod fixtures;

use fixtures::tempfile::TempDir;
use std::fs;
use uuid::Uuid;
use vsh::commands;
use vsh::state::{Operation, OperationType, ShellState};

fn open(root: &TempDir) -> ShellState {
    ShellState::new(root.path().to_str().unwrap()).unwrap()
}

fn live(state: &ShellState) -> Vec<Uuid> {
    state
        .history
        .iter()
        .filter(|op| !op.undone)
        .map(|op| op.id)
        .collect()
}

#[test]
fn rollback_reverses_and_marks_every_operation() {
    let root = TempDir::new().unwrap();
    let mut state = open(&root);
    commands::touch(&mut state, "kept", false).unwrap();
    let kept = state.history[0].id;

    commands::begin_transaction(&mut state, "t").unwrap();
    let txn = state.active_transaction.as_ref().unwrap().id;
    commands::mkdir(&mut state, "dir", false).unwrap();
    commands::touch(&mut state, "dir/file", false).unwrap();
    commands::rollback_transaction(&mut state).unwrap();

    assert!(!root.path().join("dir").exists());
    assert!(root.path().join("kept").exists());
    assert!(state.active_transaction.is_none());
    assert_eq!(live(&state), vec![kept]);
    for op in &state.history[1..] {
        assert_eq!(op.undone_by, Some(txn));
    }

    // The reported bug: `undo` used to pick the rolled-back `touch` and fail
    // with "No such file or directory". It now undoes the operation before
    // the transaction.
    commands::undo(&mut state, 1, false).unwrap();
    assert!(!root.path().join("kept").exists());

    // The same after a restart.
    let reloaded = open(&root);
    assert!(reloaded.active_transaction.is_none());
    assert!(live(&reloaded).is_empty());
}

#[test]
fn redo_brings_rolled_back_operations_back_in_order() {
    let root = TempDir::new().unwrap();
    let mut state = open(&root);
    commands::begin_transaction(&mut state, "t").unwrap();
    commands::mkdir(&mut state, "dir", false).unwrap();
    commands::touch(&mut state, "dir/file", false).unwrap();
    commands::rollback_transaction(&mut state).unwrap();
    assert!(!root.path().join("dir").exists());

    commands::redo(&mut state, 1, false).unwrap();
    assert!(root.path().join("dir").is_dir());
    assert!(!root.path().join("dir/file").exists());
    commands::redo(&mut state, 1, false).unwrap();
    assert!(root.path().join("dir/file").is_file());
}

#[test]
fn rollback_is_refused_whole_when_an_operation_has_no_inverse() {
    let root = TempDir::new().unwrap();
    let mut state = open(&root);
    commands::begin_transaction(&mut state, "t").unwrap();
    commands::touch(&mut state, "a", false).unwrap();
    // An irreversible operation inside the transaction.
    state.record_operation(Operation::new(
        OperationType::Obliterate,
        "gone".to_string(),
        None,
    ));
    commands::touch(&mut state, "b", false).unwrap();
    let before = live(&state);

    let refused = commands::rollback_transaction(&mut state).unwrap_err();
    assert!(refused.to_string().contains("refused"), "{refused}");

    // Nothing was reversed, nothing was marked, and the transaction is open.
    assert!(root.path().join("a").exists());
    assert!(root.path().join("b").exists());
    assert_eq!(live(&state), before);
    assert!(state.active_transaction.is_some());

    // Commit is the way out.
    commands::commit_transaction(&mut state).unwrap();
    assert!(state.active_transaction.is_none());
    assert_eq!(live(&state), before);
}

#[test]
fn rollback_is_refused_when_undo_data_is_missing() {
    let root = TempDir::new().unwrap();
    let mut state = open(&root);
    commands::begin_transaction(&mut state, "t").unwrap();
    commands::touch(&mut state, "a", false).unwrap();
    // A chmod record without the previous mode cannot be reversed. Before
    // the check, this record made rollback panic on a short slice.
    state.record_operation(
        Operation::new(OperationType::Chmod, "a".to_string(), None).with_undo_data(vec![1, 2]),
    );

    assert!(commands::rollback_transaction(&mut state).is_err());
    assert!(root.path().join("a").exists());
    assert!(state.active_transaction.is_some());
}

#[test]
fn a_reversal_that_fails_on_disk_leaves_the_transaction_open_to_retry() {
    let root = TempDir::new().unwrap();
    let mut state = open(&root);
    commands::begin_transaction(&mut state, "t").unwrap();
    commands::touch(&mut state, "a", false).unwrap();
    commands::touch(&mut state, "b", false).unwrap();
    let (a, b) = (state.history[0].id, state.history[1].id);

    // Something outside the shell removes `a`, so its reversal will fail.
    fs::remove_file(root.path().join("a")).unwrap();
    assert!(commands::rollback_transaction(&mut state).is_err());

    // `b` was reversed and is marked; `a` is still live; the transaction
    // is still open.
    assert!(!root.path().join("b").exists());
    assert_eq!(live(&state), vec![a]);
    assert!(state.history.iter().any(|op| op.id == b && op.undone));
    assert!(state.active_transaction.is_some());

    // The same after a restart: the rollback is resumable.
    drop(state);
    let mut state = open(&root);
    assert!(state.active_transaction.is_some());
    assert_eq!(live(&state), vec![a]);

    // Once the cause is fixed, a second rollback finishes the job without
    // touching `b` again.
    fs::write(root.path().join("a"), b"").unwrap();
    commands::rollback_transaction(&mut state).unwrap();
    assert!(!root.path().join("a").exists());
    assert!(state.active_transaction.is_none());
    assert!(live(&state).is_empty());
}

#[test]
fn rollback_skips_operations_already_undone_inside_the_transaction() {
    let root = TempDir::new().unwrap();
    let mut state = open(&root);
    commands::begin_transaction(&mut state, "t").unwrap();
    commands::touch(&mut state, "a", false).unwrap();
    commands::touch(&mut state, "b", false).unwrap();
    commands::undo(&mut state, 1, false).unwrap();
    assert!(!root.path().join("b").exists());

    // Before, rollback tried to remove `b` a second time and failed.
    commands::rollback_transaction(&mut state).unwrap();
    assert!(!root.path().join("a").exists());
    assert!(state.active_transaction.is_none());
}

#[test]
fn rollback_of_an_empty_transaction_closes_it() {
    let root = TempDir::new().unwrap();
    let mut state = open(&root);
    commands::begin_transaction(&mut state, "t").unwrap();
    commands::rollback_transaction(&mut state).unwrap();
    assert!(state.active_transaction.is_none());

    // A new transaction can begin, also after a restart.
    drop(state);
    let mut state = open(&root);
    assert!(state.active_transaction.is_none());
    commands::begin_transaction(&mut state, "next").unwrap();
}

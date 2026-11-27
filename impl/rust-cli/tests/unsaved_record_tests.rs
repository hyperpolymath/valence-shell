// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! A command whose record cannot be saved returns an error (owner ruling
//! OD-49, route plan section 14.5).
//!
//! The shell does an operation and then writes its record. If the write
//! fails, the operation has happened and the saved history does not know.
//! Every command except rollback used to print a warning and report
//! success, so a script or an agent could not see it.
//!
//! The rules under test:
//!
//! * The command returns a [`NotRecorded`] error. The change was made, and
//!   this session's history holds its record.
//! * The next record that can be written saves the whole history again, so
//!   nothing is lost if the shell keeps running until then.
//! * Assigning a variable and `cd` change no file. For them a record that
//!   cannot be saved stays a warning.

mod fixtures;

use fixtures::tempfile::TempDir;
use std::fs;
use vsh::commands;
use vsh::journal::SimStorage;
use vsh::state::{NotRecorded, ShellState};

/// A state whose saved form goes to simulated storage, which can be made to
/// refuse writes.
fn open_on(root: &TempDir, storage: &SimStorage) -> ShellState {
    ShellState::with_storage(root.path().to_str().unwrap(), Box::new(storage.clone())).unwrap()
}

fn refuse_writes(storage: &SimStorage, refuse: bool) {
    storage.fail_append(refuse);
    storage.fail_replace(refuse);
}

/// Whether `outcome` is the error that says: done, but not recorded.
fn not_recorded<T>(outcome: anyhow::Result<T>) -> bool {
    match outcome {
        Ok(_) => false,
        Err(error) => error.downcast_ref::<NotRecorded>().is_some(),
    }
}

#[test]
fn a_command_whose_record_cannot_be_saved_returns_an_error() {
    let root = TempDir::new().unwrap();
    let storage = SimStorage::new();
    let mut state = open_on(&root, &storage);

    refuse_writes(&storage, true);
    let outcome = commands::mkdir(&mut state, "d", false);

    let error = outcome.unwrap_err();
    assert!(error.downcast_ref::<NotRecorded>().is_some(), "{error:#}");
    assert!(
        error.to_string().contains("the change was made"),
        "{error:#}"
    );
    // The change was made, and this session knows of it.
    assert!(root.path().join("d").is_dir());
    assert_eq!(state.history.len(), 1);
    assert!(!state.is_saved());
}

#[test]
fn the_next_record_that_can_be_written_saves_the_one_that_could_not() {
    let root = TempDir::new().unwrap();
    let storage = SimStorage::new();
    let mut state = open_on(&root, &storage);
    refuse_writes(&storage, true);
    assert!(not_recorded(commands::mkdir(&mut state, "d", false)));

    refuse_writes(&storage, false);
    commands::touch(&mut state, "f", false).unwrap();

    assert!(state.is_saved());
    let reloaded = open_on(&root, &storage);
    let recorded: Vec<&str> = reloaded.history.iter().map(|op| op.path.as_str()).collect();
    assert_eq!(recorded, ["d", "f"]);
}

#[test]
fn every_kind_of_change_reports_a_record_that_cannot_be_saved() {
    let root = TempDir::new().unwrap();
    let storage = SimStorage::new();
    let mut state = open_on(&root, &storage);
    fs::write(root.path().join("old"), "content").unwrap();
    commands::touch(&mut state, "made", false).unwrap();

    refuse_writes(&storage, true);

    // Each change is made, and each reports that it is not recorded.
    assert!(not_recorded(commands::touch(&mut state, "f", false)));
    assert!(root.path().join("f").exists());
    assert!(not_recorded(commands::rm(&mut state, "old", false)));
    assert!(!root.path().join("old").exists());
    assert!(not_recorded(commands::undo(&mut state, 1, false)));
    assert!(root.path().join("old").exists(), "the removal was undone");
    assert!(not_recorded(commands::redo(&mut state, 1, false)));
    assert!(!root.path().join("old").exists(), "the removal was redone");
    assert!(not_recorded(commands::begin_transaction(&mut state, "t")));
    assert!(state.active_transaction.is_some());
    assert!(not_recorded(commands::commit_transaction(&mut state)));
    assert!(state.active_transaction.is_none());
}

#[test]
fn a_variable_whose_record_cannot_be_saved_is_still_set() {
    let root = TempDir::new().unwrap();
    let storage = SimStorage::new();
    let mut state = open_on(&root, &storage);

    refuse_writes(&storage, true);
    state.set_variable_tracked("name".to_string(), "value".to_string());

    assert_eq!(state.get_variable("name"), Some("value"));
}

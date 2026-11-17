// SPDX-License-Identifier: MPL-2.0
//! Crash-point tests for shell-state persistence.
//!
//! The harness is black-box: it knows only that state lives in files named
//! `.vsh_state*` in the session root, so it applies unchanged to any on-disk
//! format.
//!
//! Method:
//!
//! 1. Run a scripted session. After every acknowledged mutation, capture the
//!    bytes of every state file and the observable state (history with undo
//!    marks, and whether a transaction is open).
//! 2. For each consecutive pair of captures, enumerate the disk states a
//!    crash could leave:
//!    * *clean*: every file old, or every file new;
//!    * *torn append*: a file that grew by appending, cut at every byte
//!      offset between its old and new length;
//!    * *torn create*: a file that did not exist before, cut at every length;
//!    * *mixed files*: files that changed independently at old or new, in
//!      every combination (what a crash between two writes, or a power loss
//!      without `fsync` ordering, can leave);
//!    * *stray temp*: the old state plus a half-written temporary copy of a
//!      rewritten file.
//! 3. For each crash state, reopen the shell and require:
//!    * **opens**: `ShellState::new` succeeds;
//!    * **atomic**: the recovered state equals the state before or after the
//!      interrupted mutation, never anything else;
//!    * **stable**: after recording one more operation and reopening, the
//!      state is the recovered state plus that operation.
//!
//! A format is crash-safe when no crash state violates a property. Until the
//! journal redesign lands (route plan Phase C), the current two-file format
//! is known to fail some of them; [`KNOWN_OPEN`] lists exactly which, and the
//! test fails if that list is wrong in either direction. It must become
//! empty.

mod fixtures;

use fixtures::tempfile::TempDir;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;
use uuid::Uuid;
use vsh::state::{Operation, OperationType, ShellState};

/// Failure classes the current format is known to exhibit, as
/// `"<crash kind>/<property>"`. Empty means crash-safe.
///
/// Measured 2026-11-17 on the two-file format (snapshot + journal), 2,075
/// crash states:
///
/// * `mixed-files/atomic` (3 states, at each transaction boundary): the
///   journal is already truncated but the old snapshot is still in place, so
///   everything journalled since that snapshot is gone. A power loss can
///   leave this, because the new snapshot is not synced before the journal
///   is truncated.
/// * `torn-create/atomic` (666 states, at the first snapshot): the snapshot
///   exists but is cut short. `ShellState::new` ignores the failed load
///   (`state.load().ok()`), so the shell starts with an empty history even
///   though the journal beside it is intact. A power loss can leave this,
///   because the snapshot is renamed into place without being synced first.
///
/// Torn appends to the journal (every byte offset), a stray temporary file,
/// and the clean states all recover correctly.
const KNOWN_OPEN: &[&str] = &["mixed-files/atomic", "torn-create/atomic"];

type Files = BTreeMap<String, Vec<u8>>;

/// What a user can observe of the persisted state.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Observed {
    history: Vec<(Uuid, bool, Option<Uuid>)>,
    in_transaction: bool,
}

fn observe(state: &ShellState) -> Observed {
    Observed {
        history: state
            .history
            .iter()
            .map(|op| (op.id, op.undone, op.undone_by))
            .collect(),
        in_transaction: state.active_transaction.is_some(),
    }
}

fn open(root: &Path) -> anyhow::Result<ShellState> {
    ShellState::new(root.to_str().unwrap())
}

fn state_files(root: &Path) -> Files {
    let mut files = Files::new();
    for entry in fs::read_dir(root).unwrap() {
        let entry = entry.unwrap();
        let name = entry.file_name().to_string_lossy().into_owned();
        if name.starts_with(".vsh_state") && entry.path().is_file() {
            files.insert(name, fs::read(entry.path()).unwrap());
        }
    }
    files
}

fn materialise(files: &Files) -> TempDir {
    let dir = TempDir::new().unwrap();
    for (name, bytes) in files {
        fs::write(dir.path().join(name), bytes).unwrap();
    }
    dir
}

fn record(state: &mut ShellState, path: &str) -> Uuid {
    let op = Operation::new(OperationType::CreateFile, path.to_string(), None);
    let id = op.id;
    state.record_operation(op);
    id
}

/// One acknowledged point of the session: what is on disk and what the user
/// was told.
struct Capture {
    label: &'static str,
    files: Files,
    observed: Observed,
}

/// A scripted session touching every kind of persisted mutation: plain
/// records, an undo mark, a transaction that commits, and one that is
/// rolled back.
fn run_session() -> Vec<Capture> {
    let root = TempDir::new().unwrap();
    let mut state = open(root.path()).unwrap();
    let mut captures = Vec::new();
    let mut capture = |label: &'static str, state: &ShellState| {
        captures.push(Capture {
            label,
            files: state_files(root.path()),
            observed: observe(state),
        });
    };

    capture("start", &state);
    record(&mut state, "a");
    capture("record a", &state);
    let b = record(&mut state, "b-with-non-ascii-é");
    capture("record b", &state);
    state.mark_undone(b, Uuid::new_v4());
    capture("undo b", &state);
    state.begin_transaction("t1").unwrap();
    capture("begin t1", &state);
    record(&mut state, "c");
    capture("record c in t1", &state);
    state.commit_transaction().unwrap();
    capture("commit t1", &state);
    record(&mut state, "d");
    capture("record d", &state);
    state.begin_transaction("t2").unwrap();
    capture("begin t2", &state);
    state.abort_transaction();
    capture("rollback t2", &state);
    record(&mut state, "e");
    capture("record e", &state);
    captures
}

/// Every disk state a crash between `old` and `new` could leave, tagged with
/// its kind.
fn crash_states(old: &Files, new: &Files) -> Vec<(&'static str, Files)> {
    let names: BTreeSet<&String> = old.keys().chain(new.keys()).collect();
    let changed: Vec<&String> = names
        .into_iter()
        .filter(|n| old.get(*n) != new.get(*n))
        .collect();

    let mut states = vec![("clean", old.clone()), ("clean", new.clone())];
    for name in &changed {
        states.extend(torn_states(old, new, name));
        states.extend(stray_temp_state(old, new, name));
    }
    states.extend(mixed_file_states(old, new, &changed));
    states
}

/// `old` with one file replaced by `bytes`.
fn with_file(old: &Files, name: &str, bytes: &[u8]) -> Files {
    let mut files = old.clone();
    files.insert(name.to_string(), bytes.to_vec());
    files
}

/// One file cut short, the rest old.
///
/// * *Torn append*: the file grew by appending; cut between its old and new
///   length.
/// * *Torn create*: the file did not exist; cut at every length. A process
///   crash leaves this if the file is created by writing in place; if it is
///   created by rename, only a power loss before the data was synced can.
fn torn_states(old: &Files, new: &Files, name: &str) -> Vec<(&'static str, Files)> {
    let Some(after) = new.get(name) else {
        return Vec::new();
    };
    let (kind, lengths) = match old.get(name) {
        None => ("torn-create", 0..after.len()),
        Some(before) if after.len() > before.len() && after.starts_with(before) => {
            ("torn-append", before.len() + 1..after.len())
        }
        Some(_) => return Vec::new(),
    };
    lengths
        .map(|len| (kind, with_file(old, name, &after[..len])))
        .collect()
}

/// Each changed file independently old or new: what a crash between two
/// writes, or a power loss without `fsync` ordering, can leave.
fn mixed_file_states(old: &Files, new: &Files, changed: &[&String]) -> Vec<(&'static str, Files)> {
    if changed.len() < 2 {
        return Vec::new();
    }
    (1..(1u32 << changed.len()) - 1)
        .map(|mask| {
            let mut files = old.clone();
            for (bit, name) in changed.iter().enumerate() {
                if mask & (1 << bit) == 0 {
                    continue;
                }
                match new.get(*name) {
                    Some(bytes) => files.insert((*name).clone(), bytes.clone()),
                    None => files.remove(*name),
                };
            }
            ("mixed-files", files)
        })
        .collect()
}

/// A rewritten (not appended) file half-copied beside the old state, as a
/// crash during write-then-rename leaves it.
fn stray_temp_state(old: &Files, new: &Files, name: &str) -> Option<(&'static str, Files)> {
    let after = new.get(name)?;
    let appended = old
        .get(name)
        .is_some_and(|before| after.starts_with(before));
    if appended || after.is_empty() {
        return None;
    }
    let temp = format!("{name}.0123456789abcdef.tmp");
    Some((
        "stray-temp",
        with_file(old, &temp, &after[..after.len() / 2]),
    ))
}

/// Check the three properties for one crash state. Returns the property that
/// failed, if any.
fn check(files: &Files, before: &Observed, after: &Observed) -> Option<&'static str> {
    let dir = materialise(files);
    let Ok(mut state) = open(dir.path()) else {
        return Some("opens");
    };
    let recovered = observe(&state);
    if recovered != *before && recovered != *after {
        return Some("atomic");
    }

    // The oracle is built from the recovered state alone, so a regression
    // that rewrites an existing entry while recording a new one is caught.
    let extra = record(&mut state, "after-crash");
    drop(state);
    let mut expected = recovered;
    expected.history.push((extra, false, None));
    match open(dir.path()) {
        Ok(reopened) if observe(&reopened) == expected => {}
        _ => return Some("stable"),
    }
    None
}

#[test]
fn crash_at_every_point_recovers_a_consistent_state() {
    let captures = run_session();
    let mut failures: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut checked = 0usize;

    for pair in captures.windows(2) {
        let (old, new) = (&pair[0], &pair[1]);
        for (kind, files) in crash_states(&old.files, &new.files) {
            checked += 1;
            if let Some(property) = check(&files, &old.observed, &new.observed) {
                let sizes: Vec<String> = files
                    .iter()
                    .map(|(name, bytes)| format!("{name}={}", bytes.len()))
                    .collect();
                failures
                    .entry(format!("{kind}/{property}"))
                    .or_default()
                    .push(format!("during '{}': {}", new.label, sizes.join(" ")));
            }
        }
    }

    println!("checked {checked} crash states");
    for (class, cases) in &failures {
        let steps: BTreeSet<&str> = cases.iter().filter_map(|c| c.split('\'').nth(1)).collect();
        println!(
            "FAIL {class}: {} case(s) during {steps:?}; first: {}",
            cases.len(),
            cases[0]
        );
    }

    let observed: BTreeSet<&str> = failures.keys().map(String::as_str).collect();
    let known: BTreeSet<&str> = KNOWN_OPEN.iter().copied().collect();
    assert_eq!(
        observed, known,
        "crash-safety failure classes differ from KNOWN_OPEN (see the FAIL lines above)"
    );
}

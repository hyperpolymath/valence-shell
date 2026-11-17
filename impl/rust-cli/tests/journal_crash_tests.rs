// SPDX-License-Identifier: MPL-2.0
//! Crash-point tests for shell-state persistence.
//!
//! Two tests, from two directions.
//!
//! # Black box, on real files
//!
//! [`crash_at_every_point_recovers_a_consistent_state`] knows only that state
//! lives in files named `.vsh_state*` in the session root, so it applies
//! unchanged to any on-disk format.
//!
//! 1. Run a scripted session. After every acknowledged mutation, capture the
//!    bytes of every state file and the observable state.
//! 2. For each consecutive pair of captures, enumerate the disk states a
//!    crash could leave:
//!    * *clean*: every file old, or every file new;
//!    * *torn append*: a file that grew by appending, cut at every byte
//!      offset between its old and new length;
//!    * *torn create*: a file that did not exist before, cut at every length;
//!    * *mixed files*: files that changed independently at old or new, in
//!      every combination;
//!    * *stray temp*: the old state plus a half-written temporary copy of a
//!      rewritten file.
//! 3. For each crash state, reopen the shell and require:
//!    * **opens**: `ShellState::new` succeeds;
//!    * **atomic**: the recovered state equals the state before or after the
//!      interrupted mutation, never anything else;
//!    * **stable**: after recording one more operation and reopening, the
//!      state is the recovered state plus that operation.
//!
//! # Model based, on simulated storage
//!
//! [`crash_at_every_storage_point_recovers_before_or_after`] runs the same
//! session on [`SimStorage`], which keeps synced bytes apart from unsynced
//! ones exactly as the Agda model's file does
//! (`proofs/agda/JournalModel.agda`). After every storage call it takes each
//! content the model says a crash could leave (the synced bytes and every
//! prefix of the unsynced ones) and requires the same three properties, plus
//! **durable**: once a mutation is acknowledged, every crash recovers the
//! state after it.
//!
//! The model's theorems (`crash-recovery`, `write-atomic`,
//! `compaction-safe`) say these properties hold for the model. This test is
//! evidence, not proof, that the Rust code behaves like it.
//!
//! No failure class is tolerated. The two-file format that preceded this
//! one failed two of them (measured 2026-11-17: a journal truncated while the
//! old snapshot was still in place, and a first snapshot cut short).

mod fixtures;

use fixtures::tempfile::TempDir;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use uuid::Uuid;
use vsh::journal::SimStorage;
use vsh::state::{Operation, OperationType, ShellState};

type Files = BTreeMap<String, Vec<u8>>;

/// What a user can observe of the persisted state.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Observed {
    history: Vec<(Uuid, bool, Option<Uuid>)>,
    /// The open transaction and the operations in it.
    active: Option<(Uuid, Vec<Uuid>)>,
    /// Committed transactions.
    committed: Vec<Uuid>,
    previous_dir: Option<PathBuf>,
}

fn observe(state: &ShellState) -> Observed {
    Observed {
        history: state
            .history
            .iter()
            .map(|op| (op.id, op.undone, op.undone_by))
            .collect(),
        active: state
            .active_transaction
            .as_ref()
            .map(|txn| (txn.id, txn.operations.clone())),
        committed: state.transactions.iter().map(|txn| txn.id).collect(),
        previous_dir: state.previous_dir.clone(),
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

/// A scripted session touching every kind of persisted mutation: plain
/// records, an undo mark, a transaction that commits, one that is rolled
/// back with operations in it, a journal rewrite, the previous directory,
/// and records that trim the history at its size limit. `after` is called
/// once at the start and once after each acknowledged step.
fn run_session(state: &mut ShellState, mut after: impl FnMut(&'static str, &ShellState)) {
    after("start", state);
    record(state, "a");
    after("record a", state);
    let b = record(state, "b-with-non-ascii-é");
    after("record b", state);
    state.mark_undone(b, Uuid::new_v4());
    after("undo b", state);
    state.begin_transaction("t1").unwrap();
    after("begin t1", state);
    record(state, "c");
    after("record c in t1", state);
    state.commit_transaction().unwrap();
    after("commit t1", state);
    record(state, "d");
    after("record d", state);
    state.begin_transaction("t2").unwrap();
    after("begin t2", state);
    record(state, "e");
    after("record e in t2", state);
    state.abort_transaction();
    after("rollback t2", state);
    state.compact_journal().unwrap();
    after("rewrite journal", state);
    record(state, "f");
    after("record f", state);
    state.set_previous_dir(PathBuf::from("/somewhere/else"));
    after("set previous dir", state);
    state.max_history_size = Some(state.history.len());
    record(state, "g");
    after("record g with trim", state);
    state.begin_transaction("t3").unwrap();
    after("begin t3", state);
    state.compact_journal().unwrap();
    after("rewrite journal in t3", state);
    record(state, "h");
    after("record h in t3 with trim", state);
}

/// One acknowledged point of the session: what is on disk and what the user
/// was told.
struct Capture {
    label: &'static str,
    files: Files,
    observed: Observed,
}

fn run_file_session() -> Vec<Capture> {
    let root = TempDir::new().unwrap();
    let mut state = open(root.path()).unwrap();
    let mut captures = Vec::new();
    run_session(&mut state, |label, state| {
        captures.push(Capture {
            label,
            files: state_files(root.path()),
            observed: observe(state),
        });
    });
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
    let expected = plus_operation(recovered, extra);
    match open(dir.path()) {
        Ok(reopened) if observe(&reopened) == expected => {}
        _ => return Some("stable"),
    }
    None
}

/// `observed` after one more operation has been recorded.
fn plus_operation(mut observed: Observed, id: Uuid) -> Observed {
    observed.history.push((id, false, None));
    if let Some((_, operations)) = observed.active.as_mut() {
        operations.push(id);
    }
    observed
}

#[test]
fn crash_at_every_point_recovers_a_consistent_state() {
    let captures = run_file_session();
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

    assert!(
        failures.is_empty(),
        "crash states that did not recover: see the FAIL lines above"
    );
}

/// Open a shell on simulated storage holding `bytes`, as after a restart.
fn open_sim(root: &Path, bytes: Vec<u8>) -> anyhow::Result<(ShellState, SimStorage)> {
    let storage = SimStorage::with_contents(bytes);
    let state = ShellState::with_storage(root.to_str().unwrap(), Box::new(storage.clone()))?;
    Ok((state, storage))
}

/// Check one crash image against the model's properties. Returns what
/// failed, if anything.
fn check_image(
    root: &Path,
    image: &[u8],
    before: &Observed,
    after: &Observed,
    acknowledged: bool,
) -> Option<&'static str> {
    let Ok((mut state, storage)) = open_sim(root, image.to_vec()) else {
        return Some("opens");
    };
    let recovered = observe(&state);
    if acknowledged && recovered != *after {
        return Some("durable");
    }
    if recovered != *before && recovered != *after {
        return Some("atomic");
    }

    let extra = record(&mut state, "after-crash");
    drop(state);
    let point = storage.point();
    if !point.pending.is_empty() {
        return Some("stable (the record was not synced)");
    }
    match open_sim(root, point.durable) {
        Ok((reopened, _)) if observe(&reopened) == plus_operation(recovered, extra) => None,
        _ => Some("stable"),
    }
}

#[test]
fn crash_at_every_storage_point_recovers_before_or_after() {
    let root = TempDir::new().unwrap();
    let storage = SimStorage::new();
    let mut state =
        ShellState::with_storage(root.path().to_str().unwrap(), Box::new(storage.clone())).unwrap();

    // After each step: its label, what was observed, and how many storage
    // calls had been made by then.
    let mut steps: Vec<(&'static str, Observed, usize)> = Vec::new();
    run_session(&mut state, |label, state| {
        steps.push((label, observe(state), storage.trace().len()));
    });
    let trace = storage.trace();

    let mut checked = 0usize;
    let mut failures: Vec<String> = Vec::new();
    for pair in steps.windows(2) {
        let (_, before, first_call) = &pair[0];
        let (label, after, end_call) = &pair[1];
        assert!(end_call > first_call, "step '{label}' wrote nothing");
        for (call, point) in trace.iter().enumerate().take(*end_call).skip(*first_call) {
            // The step is acknowledged once its last storage call returns.
            let acknowledged = call + 1 == *end_call;
            if acknowledged {
                assert!(
                    point.pending.is_empty(),
                    "step '{label}' was acknowledged with unsynced bytes"
                );
            }
            for image in point.crash_images() {
                checked += 1;
                if let Some(property) =
                    check_image(root.path(), &image, before, after, acknowledged)
                {
                    failures.push(format!(
                        "{property}: during '{label}', storage call {call}, {} of {} bytes",
                        image.len(),
                        point.durable.len() + point.pending.len()
                    ));
                }
            }
        }
    }

    println!(
        "checked {checked} crash images over {} storage calls",
        trace.len()
    );
    for failure in failures.iter().take(20) {
        println!("FAIL {failure}");
    }
    assert!(
        failures.is_empty(),
        "{} crash images did not recover",
        failures.len()
    );
}

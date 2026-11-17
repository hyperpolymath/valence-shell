// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! Shell State Management
//!
//! Manages the undo/redo stack, transaction groups, and operation history.
//! This is where reversibility guarantees are maintained at runtime.

use anyhow::{Context, Result};
use chrono::{DateTime, Utc};
use colored::Colorize;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::fs;
use std::path::{Path, PathBuf};
use uuid::Uuid;

use crate::functions::FunctionTable;
use crate::posix_builtins::{AliasTable, TrapTable};
use crate::proof_refs::ProofReference;

/// Value type for shell variables - can be scalar or array
///
/// # Examples
/// ```
/// use vsh::state::VariableValue;
/// use std::collections::BTreeMap;
///
/// // Scalar variable
/// let name = VariableValue::Scalar("Alice".to_string());
///
/// // Array variable
/// let mut elements = BTreeMap::new();
/// elements.insert(0, "first".to_string());
/// elements.insert(1, "second".to_string());
/// let arr = VariableValue::Array(elements);
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum VariableValue {
    /// Scalar string value
    Scalar(String),
    /// Indexed array with sparse indices (bash-style)
    /// Uses BTreeMap for ordered iteration of indices
    Array(BTreeMap<usize, String>),
}

/// Operation type enum matching formal proof definitions.
///
/// Each variant corresponds to a filesystem operation with a proven inverse.
/// The mapping to Lean 4 theorems is:
/// - `Mkdir`/`Rmdir`: mkdir_rmdir_reversible
/// - `CreateFile`/`DeleteFile`: createFile_deleteFile_reversible
/// - `WriteFile`: write_restore_reversible (self-inverse)
/// - `FileTruncated`/`FileAppended`: truncate_restore_reversible, append_truncate_reversible
///
/// # Examples
/// ```
/// use vsh::state::OperationType;
///
/// let op = OperationType::Mkdir;
/// assert_eq!(op.inverse(), Some(OperationType::Rmdir));
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum OperationType {
    Mkdir,
    Rmdir,
    CreateFile,
    DeleteFile,
    WriteFile,
    /// File was truncated by output redirection (> or 2>)
    /// undo_data contains original file content
    FileTruncated,
    /// File was appended to by append redirection (>> or 2>>)
    /// undo_data contains original file size (u64 encoded as bytes)
    FileAppended,
    /// Copy file: reversible via deleting the destination
    /// undo_data contains destination path (src stored in path field)
    CopyFile,
    /// Move/rename: reversible via moving back
    /// path stores "src\0dst" (null-separated pair)
    Move,
    /// Create a symbolic link: reversible via unlink
    /// undo_data contains symlink target
    Symlink,
    /// Remove a symbolic link (inverse of Symlink)
    Unlink,
    /// Set a shell variable: reversible by restoring previous value (or unsetting)
    /// path stores variable name, undo_data stores previous VariableValue as JSON (None = was unset)
    SetVariable,
    /// Unset a shell variable: reversible by restoring previous value
    /// path stores variable name, undo_data stores previous VariableValue as JSON
    UnsetVariable,
    /// Change file permissions: reversible by restoring previous mode
    /// path stores file path, undo_data stores previous mode as u32 LE bytes
    Chmod,
    /// Change file ownership: reversible by restoring previous uid/gid
    /// path stores file path, undo_data stores previous uid:gid as "uid:gid" bytes
    Chown,
    /// Hardware-level secure erase (NIST SP 800-88 Purge)
    /// NOT REVERSIBLE - destroys entire device
    HardwareErase,
    /// Obliterate: best-effort overwrite and unlink
    /// NOT REVERSIBLE in shell history; physical recovery is storage-dependent
    Obliterate,
}

impl OperationType {
    /// Get the inverse operation type
    pub fn inverse(&self) -> Option<OperationType> {
        match self {
            OperationType::Mkdir => Some(OperationType::Rmdir),
            OperationType::Rmdir => Some(OperationType::Mkdir),
            OperationType::CreateFile => Some(OperationType::DeleteFile),
            OperationType::DeleteFile => Some(OperationType::CreateFile),
            OperationType::WriteFile => Some(OperationType::WriteFile), // Self-inverse with old content
            OperationType::FileTruncated => Some(OperationType::WriteFile), // Restore original content
            OperationType::FileAppended => Some(OperationType::FileAppended), // Self-inverse (truncate to original size)
            OperationType::CopyFile => Some(OperationType::DeleteFile), // Undo copy = delete destination
            OperationType::Move => Some(OperationType::Move),           // Self-inverse (move back)
            OperationType::Symlink => Some(OperationType::Unlink),
            OperationType::Unlink => Some(OperationType::Symlink),
            OperationType::SetVariable => Some(OperationType::SetVariable), // Self-inverse (restore previous)
            OperationType::UnsetVariable => Some(OperationType::SetVariable), // Restore = set previous value
            OperationType::Chmod => Some(OperationType::Chmod), // Self-inverse (restore previous mode)
            OperationType::Chown => Some(OperationType::Chown), // Self-inverse (restore previous uid:gid)
            OperationType::HardwareErase => None,               // NOT REVERSIBLE
            OperationType::Obliterate => None,                  // NOT REVERSIBLE - GDPR deletion
        }
    }

    /// Get the proof reference for this operation
    pub fn proof_reference(&self) -> ProofReference {
        ProofReference::for_operation(*self)
    }
}

impl std::fmt::Display for OperationType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OperationType::Mkdir => write!(f, "mkdir"),
            OperationType::Rmdir => write!(f, "rmdir"),
            OperationType::CreateFile => write!(f, "touch"),
            OperationType::DeleteFile => write!(f, "rm"),
            OperationType::WriteFile => write!(f, "write"),
            OperationType::FileTruncated => write!(f, "truncate"),
            OperationType::FileAppended => write!(f, "append"),
            OperationType::CopyFile => write!(f, "cp"),
            OperationType::Move => write!(f, "mv"),
            OperationType::Symlink => write!(f, "ln -s"),
            OperationType::Unlink => write!(f, "unlink"),
            OperationType::SetVariable => write!(f, "set"),
            OperationType::UnsetVariable => write!(f, "unset"),
            OperationType::Chmod => write!(f, "chmod"),
            OperationType::Chown => write!(f, "chown"),
            OperationType::HardwareErase => write!(f, "hardware_erase"),
            OperationType::Obliterate => write!(f, "obliterate"),
        }
    }
}

/// A single filesystem operation with complete undo/redo information.
///
/// Each operation is assigned a unique UUID and records all data needed for reversal.
/// File deletion operations store the original file content in `undo_data` for restoration.
///
/// # Examples
/// ```
/// use vsh::state::{Operation, OperationType};
///
/// let op = Operation::new(OperationType::Mkdir, "project".to_string(), None);
/// assert_eq!(op.op_type, OperationType::Mkdir);
/// assert!(!op.undone);
/// ```
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Operation {
    /// Unique operation ID
    pub id: Uuid,

    /// Type of operation
    pub op_type: OperationType,

    /// Path operated on
    pub path: String,

    /// Timestamp
    pub timestamp: DateTime<Utc>,

    /// Transaction ID if part of a transaction
    pub transaction_id: Option<Uuid>,

    /// Data needed for undo (e.g., file contents before write)
    pub undo_data: Option<Vec<u8>>,

    /// Whether this operation has been undone
    pub undone: bool,

    /// The operation ID that undid this one (if any)
    pub undone_by: Option<Uuid>,
}

impl Operation {
    pub fn new(op_type: OperationType, path: String, transaction_id: Option<Uuid>) -> Self {
        Self {
            id: Uuid::new_v4(),
            op_type,
            path,
            timestamp: Utc::now(),
            transaction_id,
            undo_data: None,
            undone: false,
            undone_by: None,
        }
    }

    pub fn with_undo_data(mut self, data: Vec<u8>) -> Self {
        self.undo_data = Some(data);
        self
    }
}

/// Transaction group for atomic multi-operation rollback.
///
/// Groups multiple operations together so they can be committed or rolled back
/// atomically. If rollback fails partway through, reports which operations succeeded
/// and which failed.
///
/// # Examples
/// ```no_run
/// # use vsh::commands;
/// # use vsh::state::ShellState;
/// let mut state = ShellState::new("/tmp/test")?;
/// commands::begin_transaction(&mut state, "feature")?;
/// commands::mkdir(&mut state, "src", false)?;
/// commands::mkdir(&mut state, "tests", false)?;
/// commands::commit_transaction(&mut state)?;
/// # Ok::<(), anyhow::Error>(())
/// ```
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Transaction {
    pub id: Uuid,
    pub name: String,
    pub started: DateTime<Utc>,
    pub operations: Vec<Uuid>,
    pub committed: bool,
}

/// Main shell state managing operation history, undo/redo stacks, and transactions.
///
/// The state is persisted to `~/.cache/vsh/state.json` and restored on shell startup.
/// All filesystem operations are relative to the `root` path.
///
/// # Invariants
/// - All operations in `history` are recorded in execution order
/// - `redo_stack` contains only operations that were undone
/// - At most one `active_transaction` can be active
/// - State persists across shell sessions
///
/// # Examples
/// ```no_run
/// use vsh::state::ShellState;
///
/// let mut state = ShellState::new("/tmp/workspace")?;
/// // Perform operations...
/// # Ok::<(), anyhow::Error>(())
/// ```
pub struct ShellState {
    /// Sandbox root path
    pub root: PathBuf,

    /// Operation history (append-only)
    pub history: Vec<Operation>,

    /// Redo stack (operations that were undone and can be redone)
    pub redo_stack: VecDeque<Operation>,

    /// Active transaction (if any)
    pub active_transaction: Option<Transaction>,

    /// Completed transactions
    pub transactions: Vec<Transaction>,

    /// State file path for persistence (the snapshot)
    state_file: PathBuf,

    /// Append-only journal of the history mutations made since the last
    /// snapshot.
    ///
    /// Rewriting the whole snapshot on every operation made each operation
    /// cost O(history length), so a session of n operations cost O(n²) in
    /// serialisation and disk writes. Hot-path mutations (record, mark-undone,
    /// trim) are appended here in O(1); the snapshot is rewritten only when
    /// the journal outgrows it (amortised O(1) per operation) or at the rare
    /// transaction boundaries.
    journal_file: PathBuf,

    /// Sequence number of the last journal entry written or replayed.
    /// Each snapshot records it, so replay skips entries already folded in.
    journal_seq: u64,

    /// Journal entries written or replayed since the last snapshot.
    journal_entries: usize,

    /// Indices of a contiguous block of `history` known to be all undone.
    ///
    /// Repeated single-step undo used to rescan every already-undone
    /// operation at the end of the history (twice: to pick the next target
    /// and to mark it), so undoing n operations one at a time cost O(n²).
    /// Undo skips this block instead. It is a hint: it is checked before
    /// use and an empty range means "no hint".
    undone_run: std::ops::Range<usize>,

    /// A journal append failed (possibly leaving a torn line), so the next
    /// persist must write a full snapshot rather than append.
    snapshot_pending: bool,

    /// Last exit code from external command (for $? support)
    pub last_exit_code: i32,

    /// Previous directory for cd - support
    pub previous_dir: Option<PathBuf>,

    /// Shell variables (VAR=value for scalars, arr=(v1 v2 v3) for arrays)
    pub variables: HashMap<String, VariableValue>,

    /// Variables that are exported to child processes
    pub exported_vars: HashSet<String>,

    /// Maximum history size (None = unlimited, Some(n) = limit to n operations)
    /// When limit is reached, oldest operations are removed
    /// Default: 10,000 operations
    pub max_history_size: Option<usize>,

    /// Directory for archiving old history entries
    /// If set, entries removed from history are saved here
    pub history_archive_path: Option<PathBuf>,

    /// Positional parameters ($1, $2, ...) for script arguments
    pub positional_params: Vec<String>,

    /// Counter for generating unique FIFO IDs
    fifo_counter: std::sync::atomic::AtomicUsize,

    /// Job table for background job management
    pub jobs: crate::job::JobTable,

    /// Named checkpoints mapping name → history index at checkpoint time
    pub checkpoints: HashMap<String, (usize, DateTime<Utc>)>,

    /// Shell function definitions and call stack
    pub functions: FunctionTable,

    /// Signal trap handlers (EXIT, INT, TERM, HUP)
    pub traps: TrapTable,

    /// Command aliases
    pub aliases: AliasTable,
}

impl ShellState {
    /// Create new shell state with given root
    pub fn new(root: &str) -> Result<Self> {
        let root_path = PathBuf::from(root);

        // Ensure root exists
        if !root_path.exists() {
            fs::create_dir_all(&root_path).context("Failed to create sandbox root")?;
        }

        let root_path =
            fs::canonicalize(&root_path).context("Failed to canonicalize sandbox root")?;
        let state_file = root_path.join(".vsh_state.json");
        let journal_file = root_path.join(".vsh_state.journal");

        let mut state = Self {
            root: root_path,
            history: Vec::new(),
            redo_stack: VecDeque::new(),
            active_transaction: None,
            transactions: Vec::new(),
            state_file,
            journal_file,
            journal_seq: 0,
            journal_entries: 0,
            undone_run: 0..0,
            snapshot_pending: false,
            last_exit_code: 0,
            previous_dir: None,
            variables: HashMap::new(),
            exported_vars: HashSet::new(),
            max_history_size: Some(10_000), // Default: 10k operations
            history_archive_path: None,     // No archival by default
            positional_params: Vec::new(),
            fifo_counter: std::sync::atomic::AtomicUsize::new(0),
            jobs: crate::job::JobTable::new(),
            checkpoints: HashMap::new(),
            functions: FunctionTable::new(),
            traps: TrapTable::new(),
            aliases: AliasTable::new(),
        };

        // Try to load existing state
        state.load().ok();

        Ok(state)
    }

    /// Record an operation
    pub fn record_operation(&mut self, mut op: Operation) {
        // Associate with active transaction if any
        if let Some(ref mut txn) = self.active_transaction {
            op.transaction_id = Some(txn.id);
            txn.operations.push(op.id);
        }

        self.history.push(op);

        // Enforce history size limit
        let trimmed = self.enforce_history_limit();

        // Clear redo stack when new operation is performed
        self.redo_stack.clear();

        // Persist state - warn on failure but don't abort
        if let Err(e) = self.persist_recorded(trimmed) {
            eprintln!("{} Failed to save state: {}", "Warning:".bright_yellow(), e);
            eprintln!("Operation succeeded but may not persist across restarts");
        }
    }

    /// Record an operation from a redo without clearing the redo stack.
    ///
    /// Unlike [`Self::record_operation`], this preserves remaining redo entries
    /// so that multiple sequential redos work correctly.
    pub fn record_redo_operation(&mut self, mut op: Operation) {
        if let Some(ref mut txn) = self.active_transaction {
            op.transaction_id = Some(txn.id);
            txn.operations.push(op.id);
        }

        self.history.push(op);
        let trimmed = self.enforce_history_limit();

        // Persist state - warn on failure but don't abort
        if let Err(e) = self.persist_recorded(trimmed) {
            eprintln!("{} Failed to save state: {}", "Warning:".bright_yellow(), e);
            eprintln!("Redo succeeded but may not persist across restarts");
        }
    }

    /// Enforce history size limit by removing oldest operations
    ///
    /// When history exceeds max_history_size, removes the oldest operations.
    /// If history_archive_path is set, saves removed operations to archive.
    /// Returns the number of operations removed.
    fn enforce_history_limit(&mut self) -> usize {
        if let Some(limit) = self.max_history_size {
            if self.history.len() > limit {
                let excess = self.history.len() - limit;

                // Archive old operations if path is set
                if let Some(ref archive_path) = self.history_archive_path {
                    if let Err(e) = self.archive_operations(&self.history[0..excess], archive_path)
                    {
                        eprintln!(
                            "{} Failed to archive old history: {}",
                            "Warning:".bright_yellow(),
                            e
                        );
                    }
                }

                // Remove oldest operations
                self.history.drain(0..excess);
                self.shift_undone_run(excess);

                // Note: This means undo can only go back `limit` operations
                // Users should be aware via configuration
                return excess;
            }
        }
        0
    }

    /// Archive operations to disk for later reference
    ///
    /// Saves operations as JSON lines to the archive file
    fn archive_operations(&self, operations: &[Operation], archive_path: &PathBuf) -> Result<()> {
        use std::io::Write;

        // Create archive directory if it doesn't exist
        if let Some(parent) = archive_path.parent() {
            fs::create_dir_all(parent)?;
        }

        // Append operations to archive file
        let mut file = fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(archive_path)?;

        for op in operations {
            let json = serde_json::to_string(op)?;
            writeln!(file, "{}", json)?;
        }

        Ok(())
    }

    /// Get the last N undoable operations
    pub fn last_n_undoable(&self, n: usize) -> Vec<&Operation> {
        self.undoable_indices_rev()
            .take(n)
            .map(|i| &self.history[i])
            .collect()
    }

    /// Indices of operations not yet undone, newest first, skipping the
    /// known-undone block instead of rescanning it.
    fn undoable_indices_rev(&self) -> impl Iterator<Item = usize> + '_ {
        let run = self.checked_undone_run();
        let mut next = self.history.len();
        std::iter::from_fn(move || {
            while next > 0 {
                next -= 1;
                if next + 1 == run.end {
                    next = run.start;
                    continue;
                }
                if !self.history[next].undone {
                    return Some(next);
                }
            }
            None
        })
    }

    /// The undone-block hint, or an empty range if it does not hold.
    fn checked_undone_run(&self) -> std::ops::Range<usize> {
        let run = self.undone_run.clone();
        let holds = !run.is_empty()
            && run.end <= self.history.len()
            && self.history[run.start].undone
            && self.history[run.end - 1].undone;
        if holds {
            run
        } else {
            0..0
        }
    }

    /// Record that `history[index]` is now undone in the block hint.
    fn extend_undone_run(&mut self, index: usize) {
        let run = self.checked_undone_run();
        self.undone_run = if run.is_empty() {
            index..index + 1
        } else if index + 1 == run.start {
            index..run.end
        } else if index == run.end {
            run.start..index + 1
        } else if run.contains(&index) {
            run
        } else {
            index..index + 1
        };
    }

    /// Keep the block hint aligned after the oldest `removed` operations
    /// were dropped from the front of the history.
    fn shift_undone_run(&mut self, removed: usize) {
        let start = self.undone_run.start.saturating_sub(removed);
        let end = self.undone_run.end.saturating_sub(removed);
        self.undone_run = start..end;
    }

    /// Mark an operation as undone
    pub fn mark_undone(&mut self, op_id: Uuid, undone_by: Uuid) {
        // Undo targets the newest operations that are not yet undone, so look
        // there first; fall back to a full scan for any other id.
        let index = self
            .undoable_indices_rev()
            .find(|&i| self.history[i].id == op_id)
            .or_else(|| self.history.iter().rposition(|o| o.id == op_id));

        let found = match index {
            Some(i) => {
                let op = &mut self.history[i];
                op.undone = true;
                op.undone_by = Some(undone_by);

                // Push to redo stack
                self.redo_stack.push_front(op.clone());
                self.extend_undone_run(i);
                true
            }
            None => false,
        };

        // Persist state - warn on failure
        let persisted = if found {
            self.persist_entries(&[JournalEntryRef::Undone {
                id: op_id,
                undone_by,
            }])
        } else {
            Ok(())
        };
        if let Err(e) = persisted {
            eprintln!(
                "{} Failed to save undo state: {}",
                "Warning:".bright_yellow(),
                e
            );
        }
    }

    /// Begin a new transaction
    pub fn begin_transaction(&mut self, name: &str) -> Result<Uuid> {
        if self.active_transaction.is_some() {
            anyhow::bail!("Transaction already in progress");
        }

        let txn = Transaction {
            id: Uuid::new_v4(),
            name: name.to_string(),
            started: Utc::now(),
            operations: Vec::new(),
            committed: false,
        };

        let id = txn.id;
        self.active_transaction = Some(txn);

        // Persist state - warn on failure
        if let Err(e) = self.save() {
            eprintln!(
                "{} Failed to save transaction start: {}",
                "Warning:".bright_yellow(),
                e
            );
        }

        Ok(id)
    }

    /// Commit current transaction
    pub fn commit_transaction(&mut self) -> Result<()> {
        let txn = self
            .active_transaction
            .take()
            .context("No active transaction")?;

        let mut committed = txn;
        committed.committed = true;
        self.transactions.push(committed);

        // Persist state - warn on failure
        if let Err(e) = self.save() {
            eprintln!(
                "{} Failed to save transaction commit: {}",
                "Warning:".bright_yellow(),
                e
            );
        }

        Ok(())
    }

    /// Set the directory `cd -` returns to, and journal it so it survives a
    /// restart without waiting for the next snapshot.
    pub fn set_previous_dir(&mut self, dir: PathBuf) {
        self.previous_dir = Some(dir);
        let persisted =
            self.persist_entries(&[JournalEntryRef::PreviousDir(self.previous_dir.clone())]);
        if let Err(e) = persisted {
            eprintln!(
                "{} Failed to save previous directory: {}",
                "Warning:".bright_yellow(),
                e
            );
        }
    }

    /// Drop the active transaction without committing it (after a rollback)
    /// and persist that, so a restart does not resurrect it.
    pub fn abort_transaction(&mut self) {
        self.active_transaction = None;

        // Persist state - warn on failure
        if let Err(e) = self.save() {
            eprintln!(
                "{} Failed to save transaction rollback: {}",
                "Warning:".bright_yellow(),
                e
            );
        }
    }

    /// Get operations in current transaction
    pub fn current_transaction_ops(&self) -> Vec<&Operation> {
        match &self.active_transaction {
            Some(txn) => self
                .history
                .iter()
                .filter(|op| txn.operations.contains(&op.id))
                .collect(),
            None => Vec::new(),
        }
    }

    /// Resolve a path relative to sandbox root
    /// Prevents path traversal attacks via `..` components
    pub fn resolve_path(&self, path: &str) -> PathBuf {
        resolve_under_root(&self.root, path)
    }

    /// Get root path as string (for Lean FFI)
    pub fn root(&self) -> &str {
        self.root.to_str().unwrap_or("/")
    }

    /// Get history for display
    pub fn get_history(&self, count: usize) -> Vec<&Operation> {
        self.history.iter().rev().take(count).collect()
    }

    /// Get redo stack
    pub fn get_redo_stack(&self) -> &VecDeque<Operation> {
        &self.redo_stack
    }

    /// Pop from redo stack
    pub fn pop_redo(&mut self) -> Option<Operation> {
        self.redo_stack.pop_front()
    }

    /// Persist the operation just pushed by `record_operation` or
    /// `record_redo_operation`, plus the history trim it caused.
    fn persist_recorded(&mut self, trimmed: usize) -> Result<()> {
        if self.journal_due_for_snapshot() {
            return self.save();
        }
        // With `max_history_size == Some(0)` the operation is trimmed at once
        // and there is nothing to journal; fall back to a snapshot.
        let Some(op) = self.history.last() else {
            return self.save();
        };
        let mut entries = vec![JournalEntryRef::Record(op)];
        if trimmed > 0 {
            entries.push(JournalEntryRef::Trim(trimmed));
        }
        let appended = append_journal(&self.journal_file, self.journal_seq, &entries);
        let count = entries.len();
        self.after_append(appended, count)
    }

    /// Persist journal entries that do not borrow from `self`.
    fn persist_entries(&mut self, entries: &[JournalEntryRef<'_>]) -> Result<()> {
        if self.journal_due_for_snapshot() {
            return self.save();
        }
        let appended = append_journal(&self.journal_file, self.journal_seq, entries);
        self.after_append(appended, entries.len())
    }

    /// Account for a journal append of `count` entries. A failed append may
    /// have left a torn line, which ends replay, so the next persist writes a
    /// full snapshot (and empties the journal) instead of appending after it.
    fn after_append(&mut self, appended: Result<()>, count: usize) -> Result<()> {
        if appended.is_err() {
            self.snapshot_pending = true;
        } else {
            self.journal_seq += count as u64;
            self.journal_entries += count;
        }
        appended
    }

    /// The journal is folded into a fresh snapshot once it holds at least
    /// half as many entries as the history has operations (and at least
    /// `JOURNAL_MIN_ENTRIES`). A snapshot costs O(history length), which is
    /// then at most twice the number of entries it absorbs, so persistence
    /// stays amortised O(1) per operation.
    fn journal_due_for_snapshot(&self) -> bool {
        self.snapshot_pending
            || (self.journal_entries >= JOURNAL_MIN_ENTRIES
                && 2 * self.journal_entries >= self.history.len())
    }

    /// Write a full snapshot and empty the journal.
    ///
    /// The snapshot is written to a temporary file and renamed over the old
    /// one, so a crash leaves either the old or the new snapshot. It records
    /// the journal sequence number it includes, so a crash between the rename
    /// and the journal truncation cannot replay entries twice.
    fn save(&mut self) -> Result<()> {
        use std::io::Write;

        let state = SerializableStateRef {
            history: &self.history,
            transactions: &self.transactions,
            active_transaction: self.active_transaction.as_ref(),
            previous_dir: self.previous_dir.as_ref(),
            journal_seq: self.journal_seq,
        };

        let file_name = format!(".vsh_state.json.{}.tmp", Uuid::new_v4().simple());
        let tmp = self.state_file.with_file_name(file_name);
        let written = (|| -> Result<()> {
            let mut out = std::io::BufWriter::new(fs::File::create(&tmp)?);
            serde_json::to_writer(&mut out, &state)?;
            out.flush()?;
            fs::rename(&tmp, &self.state_file)?;
            Ok(())
        })();
        if written.is_err() {
            let _ = fs::remove_file(&tmp);
        }
        written?;

        // Everything journalled so far is now in the snapshot.
        if self.journal_file.exists() {
            fs::OpenOptions::new()
                .write(true)
                .open(&self.journal_file)?
                .set_len(0)?;
        }
        self.journal_entries = 0;
        self.snapshot_pending = false;

        Ok(())
    }

    /// Load state from the snapshot, then replay the journal on top of it.
    fn load(&mut self) -> Result<()> {
        if self.state_file.exists() {
            let json = crate::fs_pure::read_to_string(&self.state_file)?;
            let state: SerializableState = serde_json::from_str(&json)?;

            self.history = state.history;
            self.transactions = state.transactions;
            self.active_transaction = state.active_transaction;
            self.previous_dir = state.previous_dir;
            self.journal_seq = state.journal_seq;
        }

        if self.journal_file.exists() {
            // Read bytes, not a string: a crash can tear the last line inside
            // a multi-byte character, and that must count as a torn line
            // rather than make the whole file unreadable.
            let journal = crate::fs_pure::read_to_end(&self.journal_file)?;
            let body = journal.strip_suffix(b"\n").unwrap_or(&journal);
            let mut replayed_all = true;
            for line in body.split(|&b| b == b'\n').filter(|_| !body.is_empty()) {
                // A torn line (crash mid-append) ends the replay, and so does
                // a sequence gap: replay keeps the longest consistent prefix.
                let Ok(JournalLine { seq, entry }) = serde_json::from_slice::<JournalLine>(line)
                else {
                    replayed_all = false;
                    break;
                };
                if seq <= self.journal_seq {
                    continue; // already folded into the snapshot
                }
                if seq != self.journal_seq + 1 {
                    replayed_all = false;
                    break;
                }
                self.replay(entry);
                self.journal_seq = seq;
                self.journal_entries += 1;
            }
            // Entries appended after a torn line or gap would be skipped by
            // every later reload. Make the next persist write a full snapshot,
            // which also truncates the journal, instead of appending.
            if !replayed_all {
                self.snapshot_pending = true;
            }
        }

        // The history was replaced wholesale; drop the undone-block hint.
        self.undone_run = 0..0;

        Ok(())
    }

    /// Apply one journal entry to the in-memory history. Mirrors what the
    /// live mutation did, minus side effects (archiving, redo stack, I/O);
    /// the redo stack is not persisted, as before.
    fn replay(&mut self, entry: JournalEntry) {
        match entry {
            JournalEntry::Record(op) => {
                if let Some(txn) = self.active_transaction.as_mut() {
                    if op.transaction_id == Some(txn.id) {
                        txn.operations.push(op.id);
                    }
                }
                self.history.push(op);
            }
            JournalEntry::Undone { id, undone_by } => {
                if let Some(op) = self.history.iter_mut().rev().find(|o| o.id == id) {
                    op.undone = true;
                    op.undone_by = Some(undone_by);
                }
            }
            JournalEntry::Trim(n) => {
                let n = n.min(self.history.len());
                self.history.drain(0..n);
            }
            JournalEntry::PreviousDir(dir) => {
                self.previous_dir = dir;
            }
        }
    }

    // =========================================================================
    // Variable Management
    // =========================================================================

    /// Set a shell variable (no undo tracking — use set_variable_tracked for reversibility)
    pub fn set_variable(&mut self, name: impl Into<String>, value: impl Into<String>) {
        self.variables
            .insert(name.into(), VariableValue::Scalar(value.into()));
    }

    /// Set a shell variable with undo tracking.
    ///
    /// Records the previous value (or absence) so the operation can be reversed.
    pub fn set_variable_tracked(&mut self, name: impl Into<String>, value: impl Into<String>) {
        let name = name.into();
        let value = value.into();

        // Capture previous state for undo
        let previous = self.variables.get(&name).cloned();
        let undo_data = serde_json::to_vec(&previous).unwrap_or_default();

        // Perform the set
        self.variables
            .insert(name.clone(), VariableValue::Scalar(value));

        // Record operation
        let op = Operation::new(OperationType::SetVariable, name, None).with_undo_data(undo_data);
        self.record_operation(op);
    }

    /// Unset a shell variable with undo tracking.
    pub fn unset_variable_tracked(&mut self, name: &str) {
        // Capture previous state for undo
        let previous = self.variables.get(name).cloned();
        if previous.is_none() {
            // Nothing to unset — no-op, no record
            return;
        }
        let undo_data = serde_json::to_vec(&previous).unwrap_or_default();

        // Perform the unset
        self.variables.remove(name);
        self.exported_vars.remove(name);

        // Record operation
        let op = Operation::new(OperationType::UnsetVariable, name.to_string(), None)
            .with_undo_data(undo_data);
        self.record_operation(op);
    }

    /// Get a shell variable value (scalar only)
    /// Returns None if variable doesn't exist or is an array
    pub fn get_variable(&self, name: &str) -> Option<&str> {
        self.variables.get(name).and_then(|v| match v {
            VariableValue::Scalar(s) => Some(s.as_str()),
            VariableValue::Array(_) => None,
        })
    }

    /// Unset a shell variable
    pub fn unset_variable(&mut self, name: &str) {
        self.variables.remove(name);
        self.exported_vars.remove(name);
    }

    /// Get all scalar variables as (name, value) pairs
    pub fn get_all_variables(&self) -> Vec<(&str, String)> {
        self.variables
            .iter()
            .filter_map(|(k, v)| match v {
                VariableValue::Scalar(s) => Some((k.as_str(), s.clone())),
                VariableValue::Array(_) => None,
            })
            .collect()
    }

    /// Export a variable (make it available to child processes)
    pub fn export_variable(&mut self, name: impl Into<String>) {
        self.exported_vars.insert(name.into());
    }

    // ========================================================================
    // Array variable methods
    // ========================================================================

    /// Set an entire array variable
    pub fn set_array(&mut self, name: impl Into<String>, elements: Vec<String>) {
        let mut array = BTreeMap::new();
        for (index, value) in elements.into_iter().enumerate() {
            array.insert(index, value);
        }
        self.variables
            .insert(name.into(), VariableValue::Array(array));
    }

    /// Get a single array element by index
    /// Returns None if variable doesn't exist, is not an array, or index doesn't exist
    pub fn get_array_element(&self, name: &str, index: usize) -> Option<&str> {
        self.variables.get(name).and_then(|v| match v {
            VariableValue::Array(arr) => arr.get(&index).map(|s| s.as_str()),
            VariableValue::Scalar(_) => None,
        })
    }

    /// Get all array elements as a vector
    /// Returns None if variable doesn't exist or is not an array
    pub fn get_array_all(&self, name: &str) -> Option<Vec<&str>> {
        self.variables.get(name).and_then(|v| match v {
            VariableValue::Array(arr) => Some(arr.values().map(|s| s.as_str()).collect()),
            VariableValue::Scalar(_) => None,
        })
    }

    /// Set a single array element by index
    /// If the variable doesn't exist, creates a sparse array with just this element
    /// If the variable is a scalar, converts it to an array
    pub fn set_array_element(&mut self, name: impl Into<String>, index: usize, value: String) {
        let name = name.into();
        let mut array = match self.variables.get(&name) {
            Some(VariableValue::Array(arr)) => arr.clone(),
            Some(VariableValue::Scalar(_)) | None => BTreeMap::new(),
        };
        array.insert(index, value);
        self.variables.insert(name, VariableValue::Array(array));
    }

    /// Get the length of an array (number of elements)
    /// Returns 0 if variable doesn't exist or is a scalar
    pub fn get_array_length(&self, name: &str) -> usize {
        self.variables.get(name).map_or(0, |v| match v {
            VariableValue::Array(arr) => arr.len(),
            VariableValue::Scalar(_) => 0,
        })
    }

    /// Get all array indices
    /// Returns empty vector if variable doesn't exist or is a scalar
    pub fn get_array_indices(&self, name: &str) -> Vec<usize> {
        self.variables.get(name).map_or(Vec::new(), |v| match v {
            VariableValue::Array(arr) => arr.keys().copied().collect(),
            VariableValue::Scalar(_) => Vec::new(),
        })
    }

    /// Append elements to an array
    /// If variable doesn't exist, creates new array
    /// If variable is scalar, converts to array with scalar as index 0
    pub fn append_to_array(&mut self, name: impl Into<String>, elements: Vec<String>) {
        let name = name.into();
        let mut array = match self.variables.get(&name) {
            Some(VariableValue::Array(arr)) => arr.clone(),
            Some(VariableValue::Scalar(s)) => {
                // Convert scalar to array with value at index 0
                let mut map = BTreeMap::new();
                map.insert(0, s.clone());
                map
            }
            None => BTreeMap::new(),
        };

        // Find the next index (max index + 1, or 0 if empty)
        let next_index = array.keys().max().map(|&i| i + 1).unwrap_or(0);

        for (offset, value) in elements.into_iter().enumerate() {
            array.insert(next_index + offset, value);
        }

        self.variables.insert(name, VariableValue::Array(array));
    }

    /// Check if a variable is an array
    pub fn is_array(&self, name: &str) -> bool {
        self.variables
            .get(name)
            .is_some_and(|v| matches!(v, VariableValue::Array(_)))
    }

    // ========================================================================
    // End of array variable methods
    // ========================================================================

    /// Check if a variable is exported
    pub fn is_exported(&self, name: &str) -> bool {
        self.exported_vars.contains(name)
    }

    /// Get all exported variables as environment key-value pairs
    /// Arrays are exported as space-separated values (bash behavior)
    pub fn get_exported_env(&self) -> Vec<(String, String)> {
        self.exported_vars
            .iter()
            .filter_map(|name| {
                self.variables.get(name).map(|value| {
                    let string_value = match value {
                        VariableValue::Scalar(s) => s.clone(),
                        VariableValue::Array(arr) => {
                            // Join array elements with spaces (bash behavior)
                            arr.values().cloned().collect::<Vec<_>>().join(" ")
                        }
                    };
                    (name.clone(), string_value)
                })
            })
            .collect()
    }

    /// Set positional parameters ($1, $2, ...)
    pub fn set_positional_params(&mut self, params: Vec<String>) {
        self.positional_params = params;
    }

    /// Get a positional parameter by index (1-based: $1, $2, ...)
    pub fn get_positional_param(&self, index: usize) -> Option<&str> {
        if index == 0 {
            Some("vsh") // $0 is the shell name
        } else if index > 0 && index <= self.positional_params.len() {
            Some(&self.positional_params[index - 1])
        } else {
            None
        }
    }

    /// Get all positional parameters as separate words ($@)
    pub fn get_all_params_separate(&self) -> String {
        self.positional_params.join(" ")
    }

    /// Get all positional parameters as single word ($*)
    pub fn get_all_params_joined(&self) -> String {
        self.positional_params.join(" ")
    }

    /// Get count of positional parameters ($#)
    pub fn get_param_count(&self) -> usize {
        self.positional_params.len()
    }

    /// Get next unique FIFO ID for process substitution.
    ///
    /// Uses a process-wide atomic so that FIFO paths are unique across all
    /// `ShellState` instances in the same process (e.g. parallel test threads
    /// that share a PID). A per-state counter would collide under
    /// `cargo test`, since each test creates a fresh state whose counter
    /// starts at 0 while they all share the same PID in the FIFO path
    /// template `/tmp/vsh-fifo-<pid>-<id>`.
    pub fn next_fifo_id(&self) -> usize {
        use std::sync::atomic::{AtomicUsize, Ordering};
        static GLOBAL_FIFO_COUNTER: AtomicUsize = AtomicUsize::new(0);
        // Keep the per-state counter too so its semantics (monotonic per
        // state) are preserved for any caller that reads it directly.
        let _ = self.fifo_counter.fetch_add(1, Ordering::SeqCst);
        GLOBAL_FIFO_COUNTER.fetch_add(1, Ordering::SeqCst)
    }

    /// Get special variable value ($$, $?, $HOME, etc.)
    pub fn get_special_variable(&self, name: &str) -> Option<String> {
        match name {
            "?" => Some(self.last_exit_code.to_string()),
            "$" => Some(std::process::id().to_string()),
            "#" => Some(self.positional_params.len().to_string()),
            "@" => Some(self.get_all_params_separate()),
            "*" => Some(self.get_all_params_joined()),
            "0" => Some("vsh".to_string()),
            "HOME" => std::env::var("HOME").ok(),
            "PWD" => std::env::current_dir()
                .ok()
                .and_then(|p| p.to_str().map(String::from)),
            "USER" => std::env::var("USER").ok(),
            "PATH" => std::env::var("PATH").ok(),
            "SHELL" => Some("vsh".to_string()),
            _ => {
                // Check for positional parameter ($1, $2, ...)
                if let Ok(index) = name.parse::<usize>() {
                    self.get_positional_param(index).map(String::from)
                } else {
                    None
                }
            }
        }
    }

    /// Expand a variable reference ($VAR or ${VAR})
    pub fn expand_variable(&self, name: &str) -> String {
        // Try special variables first
        if let Some(value) = self.get_special_variable(name) {
            return value;
        }

        // Then user-defined variables
        self.get_variable(name).unwrap_or("").to_string()
    }
}

#[derive(Deserialize)]
struct SerializableState {
    history: Vec<Operation>,
    transactions: Vec<Transaction>,
    active_transaction: Option<Transaction>,
    #[serde(default)]
    previous_dir: Option<PathBuf>,
    /// Last journal sequence number folded into this snapshot (0 for
    /// snapshots written before the journal existed).
    #[serde(default)]
    journal_seq: u64,
}

/// Borrowing twin of [`SerializableState`], so a snapshot does not clone the
/// whole history first.
#[derive(Serialize)]
struct SerializableStateRef<'a> {
    history: &'a [Operation],
    transactions: &'a [Transaction],
    active_transaction: Option<&'a Transaction>,
    previous_dir: Option<&'a PathBuf>,
    journal_seq: u64,
}

/// Minimum journal length before it is folded into a snapshot.
const JOURNAL_MIN_ENTRIES: usize = 1024;

/// One history mutation in the journal (`.vsh_state.journal`, JSON lines).
#[derive(Deserialize)]
enum JournalEntry {
    /// An operation appended to the history.
    Record(Operation),
    /// An operation marked undone.
    Undone { id: Uuid, undone_by: Uuid },
    /// The oldest `n` operations dropped by the history size limit.
    Trim(usize),
    /// The directory `cd -` returns to, as set by `cd`.
    PreviousDir(Option<PathBuf>),
}

/// Borrowing twin of [`JournalEntry`]; serialises to the same shape.
#[derive(Serialize)]
enum JournalEntryRef<'a> {
    Record(&'a Operation),
    Undone { id: Uuid, undone_by: Uuid },
    Trim(usize),
    PreviousDir(Option<PathBuf>),
}

#[derive(Deserialize)]
struct JournalLine {
    seq: u64,
    entry: JournalEntry,
}

#[derive(Serialize)]
struct JournalLineRef<'a, 'b> {
    seq: u64,
    entry: &'b JournalEntryRef<'a>,
}

/// Append `entries` to the journal as JSON lines numbered from
/// `last_seq + 1`. Lines are streamed to the file rather than built in memory
/// first, since a `Record` can carry a large `undo_data` payload; small
/// entries still reach the file in a single write.
fn append_journal(path: &Path, last_seq: u64, entries: &[JournalEntryRef<'_>]) -> Result<()> {
    use std::io::Write;
    let file = fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)?;
    let mut out = std::io::BufWriter::with_capacity(64 * 1024, file);
    for (seq, entry) in (last_seq + 1..).zip(entries) {
        serde_json::to_writer(&mut out, &JournalLineRef { seq, entry })?;
        out.write_all(b"\n")?;
    }
    out.flush()?;
    Ok(())
}

/// Resolve `path` against the sandbox `root`, clamping any `..` traversal so
/// the result never escapes `root`.
///
/// A leading `/` is treated as relative to `root`; `.` components are dropped.
/// This is the single path-resolution rule shared by [`ShellState::resolve_path`]
/// and the precondition checks in [`crate::verification`].
pub fn resolve_under_root(root: &Path, path: &str) -> PathBuf {
    let raw = if let Some(stripped) = path.strip_prefix('/') {
        root.join(stripped)
    } else {
        root.join(path)
    };

    // Normalize path components to prevent traversal via ..
    let mut normalized = PathBuf::new();
    for component in raw.components() {
        match component {
            std::path::Component::ParentDir => {
                // Only pop if we're still within the sandbox root
                if normalized.starts_with(root) && normalized != root {
                    normalized.pop();
                }
                // If popping would escape root, silently clamp to root
            }
            std::path::Component::CurDir => {
                // Skip . components
            }
            other => {
                normalized.push(other);
            }
        }
    }

    // Final safety check: ensure result is within sandbox
    if !normalized.starts_with(root) {
        root.to_path_buf()
    } else {
        normalized
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_operation_inverse() {
        assert_eq!(OperationType::Mkdir.inverse(), Some(OperationType::Rmdir));
        assert_eq!(OperationType::Rmdir.inverse(), Some(OperationType::Mkdir));
    }

    #[test]
    fn test_state_new() {
        let state = ShellState::new("/tmp/vsh_test").unwrap();
        assert!(state.root.exists());
    }

    // ========================================================================
    // Array variable tests
    // ========================================================================

    #[test]
    fn test_set_array() {
        let mut state = ShellState::new("/tmp/vsh_array_test_1").unwrap();
        let elements = vec!["one".to_string(), "two".to_string(), "three".to_string()];
        state.set_array("arr", elements);

        assert!(state.is_array("arr"));
        assert_eq!(state.get_array_length("arr"), 3);
    }

    #[test]
    fn test_get_array_element() {
        let mut state = ShellState::new("/tmp/vsh_array_test_2").unwrap();
        state.set_array("arr", vec!["first".to_string(), "second".to_string()]);

        assert_eq!(state.get_array_element("arr", 0), Some("first"));
        assert_eq!(state.get_array_element("arr", 1), Some("second"));
        assert_eq!(state.get_array_element("arr", 2), None);
    }

    #[test]
    fn test_get_array_all() {
        let mut state = ShellState::new("/tmp/vsh_array_test_3").unwrap();
        state.set_array(
            "arr",
            vec!["a".to_string(), "b".to_string(), "c".to_string()],
        );

        let all = state.get_array_all("arr").unwrap();
        assert_eq!(all, vec!["a", "b", "c"]);
    }

    #[test]
    fn test_set_array_element_new() {
        let mut state = ShellState::new("/tmp/vsh_array_test_4").unwrap();
        state.set_array_element("arr", 0, "first".to_string());
        state.set_array_element("arr", 1, "second".to_string());

        assert_eq!(state.get_array_element("arr", 0), Some("first"));
        assert_eq!(state.get_array_element("arr", 1), Some("second"));
        assert_eq!(state.get_array_length("arr"), 2);
    }

    #[test]
    fn test_set_array_element_sparse() {
        let mut state = ShellState::new("/tmp/vsh_array_test_5").unwrap();
        state.set_array_element("arr", 0, "zero".to_string());
        state.set_array_element("arr", 100, "hundred".to_string());

        assert_eq!(state.get_array_element("arr", 0), Some("zero"));
        assert_eq!(state.get_array_element("arr", 100), Some("hundred"));
        assert_eq!(state.get_array_element("arr", 50), None);
        assert_eq!(state.get_array_length("arr"), 2); // Only 2 elements, not 101
    }

    #[test]
    fn test_set_array_element_overwrite() {
        let mut state = ShellState::new("/tmp/vsh_array_test_6").unwrap();
        state.set_array("arr", vec!["old".to_string()]);
        state.set_array_element("arr", 0, "new".to_string());

        assert_eq!(state.get_array_element("arr", 0), Some("new"));
    }

    #[test]
    fn test_get_array_indices() {
        let mut state = ShellState::new("/tmp/vsh_array_test_7").unwrap();
        state.set_array_element("arr", 0, "a".to_string());
        state.set_array_element("arr", 2, "c".to_string());
        state.set_array_element("arr", 5, "f".to_string());

        let indices = state.get_array_indices("arr");
        assert_eq!(indices, vec![0, 2, 5]);
    }

    #[test]
    fn test_append_to_array() {
        let mut state = ShellState::new("/tmp/vsh_array_test_8").unwrap();
        state.set_array("arr", vec!["one".to_string(), "two".to_string()]);
        state.append_to_array("arr", vec!["three".to_string(), "four".to_string()]);

        assert_eq!(state.get_array_length("arr"), 4);
        assert_eq!(state.get_array_element("arr", 2), Some("three"));
        assert_eq!(state.get_array_element("arr", 3), Some("four"));
    }

    #[test]
    fn test_append_to_empty_array() {
        let mut state = ShellState::new("/tmp/vsh_array_test_9").unwrap();
        state.append_to_array("arr", vec!["first".to_string()]);

        assert_eq!(state.get_array_element("arr", 0), Some("first"));
        assert_eq!(state.get_array_length("arr"), 1);
    }

    #[test]
    fn test_append_to_scalar_converts() {
        let mut state = ShellState::new("/tmp/vsh_array_test_10").unwrap();
        state.set_variable("var", "scalar");
        state.append_to_array("var", vec!["new".to_string()]);

        assert!(state.is_array("var"));
        assert_eq!(state.get_array_element("var", 0), Some("scalar"));
        assert_eq!(state.get_array_element("var", 1), Some("new"));
    }

    #[test]
    fn test_scalar_and_array_separation() {
        let mut state = ShellState::new("/tmp/vsh_array_test_11").unwrap();
        state.set_variable("scalar", "value");
        state.set_array("arr", vec!["elem".to_string()]);

        // Scalar returns Some
        assert_eq!(state.get_variable("scalar"), Some("value"));
        // Array returns None for get_variable
        assert_eq!(state.get_variable("arr"), None);
        // Scalar returns None for get_array_element
        assert_eq!(state.get_array_element("scalar", 0), None);
    }

    #[test]
    fn test_unset_array() {
        let mut state = ShellState::new("/tmp/vsh_array_test_12").unwrap();
        state.set_array("arr", vec!["elem".to_string()]);
        assert!(state.is_array("arr"));

        state.unset_variable("arr");
        assert!(!state.is_array("arr"));
        assert_eq!(state.get_array_length("arr"), 0);
    }

    #[test]
    fn test_export_array() {
        let mut state = ShellState::new("/tmp/vsh_array_test_13").unwrap();
        state.set_array(
            "arr",
            vec!["one".to_string(), "two".to_string(), "three".to_string()],
        );
        state.export_variable("arr");

        let exported = state.get_exported_env();
        let arr_export = exported.iter().find(|(k, _)| k == "arr");
        assert!(arr_export.is_some());
        assert_eq!(arr_export.unwrap().1, "one two three");
    }

    #[test]
    fn test_is_array() {
        let mut state = ShellState::new("/tmp/vsh_array_test_14").unwrap();
        state.set_variable("scalar", "value");
        state.set_array("arr", vec!["elem".to_string()]);

        assert!(!state.is_array("scalar"));
        assert!(state.is_array("arr"));
        assert!(!state.is_array("nonexistent"));
    }

    #[test]
    fn test_get_array_length_scalar() {
        let mut state = ShellState::new("/tmp/vsh_array_test_15").unwrap();
        state.set_variable("scalar", "value");

        assert_eq!(state.get_array_length("scalar"), 0);
        assert_eq!(state.get_array_length("nonexistent"), 0);
    }

    #[test]
    fn test_get_array_all_nonexistent() {
        let state = ShellState::new("/tmp/vsh_array_test_16").unwrap();
        assert_eq!(state.get_array_all("nonexistent"), None);
    }

    #[test]
    fn test_get_array_all_scalar() {
        let mut state = ShellState::new("/tmp/vsh_array_test_17").unwrap();
        state.set_variable("scalar", "value");
        assert_eq!(state.get_array_all("scalar"), None);
    }

    #[test]
    fn test_empty_array() {
        let mut state = ShellState::new("/tmp/vsh_array_test_18").unwrap();
        state.set_array("arr", vec![]);

        assert!(state.is_array("arr"));
        assert_eq!(state.get_array_length("arr"), 0);
        assert_eq!(state.get_array_all("arr").unwrap(), Vec::<&str>::new());
        assert_eq!(state.get_array_indices("arr"), Vec::<usize>::new());
    }

    #[test]
    fn test_array_with_empty_strings() {
        let mut state = ShellState::new("/tmp/vsh_array_test_19").unwrap();
        state.set_array(
            "arr",
            vec!["".to_string(), "nonempty".to_string(), "".to_string()],
        );

        assert_eq!(state.get_array_length("arr"), 3);
        assert_eq!(state.get_array_element("arr", 0), Some(""));
        assert_eq!(state.get_array_element("arr", 1), Some("nonempty"));
        assert_eq!(state.get_array_element("arr", 2), Some(""));
    }

    #[test]
    fn test_variable_value_scalar() {
        let val = VariableValue::Scalar("test".to_string());
        match val {
            VariableValue::Scalar(s) => assert_eq!(s, "test"),
            _ => panic!("Expected Scalar variant"),
        }
    }

    #[test]
    fn test_variable_value_array() {
        let mut map = BTreeMap::new();
        map.insert(0, "first".to_string());
        map.insert(1, "second".to_string());
        let val = VariableValue::Array(map.clone());

        match val {
            VariableValue::Array(arr) => assert_eq!(arr, map),
            _ => panic!("Expected Array variant"),
        }
    }

    #[test]
    fn test_backward_compatibility() {
        // Test that old scalar variable usage still works
        let mut state = ShellState::new("/tmp/vsh_array_test_20").unwrap();

        // set_variable should create scalar
        state.set_variable("name", "value");
        assert_eq!(state.get_variable("name"), Some("value"));
        assert!(!state.is_array("name"));

        // expand_variable should work
        assert_eq!(state.expand_variable("name"), "value");
    }

    // ========================================================================
    // Tracked variable operation tests (undo/redo)
    // ========================================================================

    #[test]
    fn test_set_variable_tracked_records_operation() {
        let mut state = ShellState::new("/tmp/vsh_tracked_var_1").unwrap();
        state.set_variable_tracked("FOO", "bar");

        assert_eq!(state.get_variable("FOO"), Some("bar"));
        // Should have recorded a SetVariable operation
        assert!(!state.history.is_empty());
        let last_op = state.history.last().unwrap();
        assert_eq!(last_op.op_type, OperationType::SetVariable);
        assert_eq!(last_op.path, "FOO");
    }

    #[test]
    fn test_set_variable_tracked_captures_previous() {
        let mut state = ShellState::new("/tmp/vsh_tracked_var_2").unwrap();
        // Set initial value
        state.set_variable("FOO", "old_value");
        // Now track-set a new value
        state.set_variable_tracked("FOO", "new_value");

        assert_eq!(state.get_variable("FOO"), Some("new_value"));
        // undo_data should contain the previous value
        let last_op = state.history.last().unwrap();
        let previous: Option<VariableValue> =
            serde_json::from_slice(last_op.undo_data.as_ref().unwrap()).unwrap();
        assert_eq!(
            previous,
            Some(VariableValue::Scalar("old_value".to_string()))
        );
    }

    #[test]
    fn test_set_variable_tracked_new_var_captures_none() {
        let mut state = ShellState::new("/tmp/vsh_tracked_var_3").unwrap();
        state.set_variable_tracked("NEW_VAR", "value");

        let last_op = state.history.last().unwrap();
        let previous: Option<VariableValue> =
            serde_json::from_slice(last_op.undo_data.as_ref().unwrap()).unwrap();
        assert_eq!(previous, None);
    }

    #[test]
    fn test_unset_variable_tracked_records_operation() {
        let mut state = ShellState::new("/tmp/vsh_tracked_var_4").unwrap();
        state.set_variable("FOO", "bar");
        state.unset_variable_tracked("FOO");

        assert_eq!(state.get_variable("FOO"), None);
        let last_op = state.history.last().unwrap();
        assert_eq!(last_op.op_type, OperationType::UnsetVariable);
        assert_eq!(last_op.path, "FOO");
    }

    #[test]
    fn test_unset_variable_tracked_noop_for_nonexistent() {
        let mut state = ShellState::new("/tmp/vsh_tracked_var_5").unwrap();
        let history_len = state.history.len();
        state.unset_variable_tracked("NONEXISTENT");

        // Should not record anything
        assert_eq!(state.history.len(), history_len);
    }

    #[test]
    fn test_operation_type_set_variable_inverse() {
        assert_eq!(
            OperationType::SetVariable.inverse(),
            Some(OperationType::SetVariable)
        );
        assert_eq!(
            OperationType::UnsetVariable.inverse(),
            Some(OperationType::SetVariable)
        );
    }

    // ========================================================================
    // chmod/chown operation type tests
    // ========================================================================

    #[test]
    fn test_chmod_inverse() {
        assert_eq!(OperationType::Chmod.inverse(), Some(OperationType::Chmod));
    }

    #[test]
    fn test_chown_inverse() {
        assert_eq!(OperationType::Chown.inverse(), Some(OperationType::Chown));
    }

    #[test]
    fn test_chmod_display() {
        assert_eq!(format!("{}", OperationType::Chmod), "chmod");
    }

    #[test]
    fn test_chown_display() {
        assert_eq!(format!("{}", OperationType::Chown), "chown");
    }

    // ========================================================================
    // Persistence: snapshot + journal
    // ========================================================================

    fn persisted_root() -> tempfile::TempDir {
        tempfile::TempDir::new().unwrap()
    }

    fn reopen(root: &tempfile::TempDir) -> ShellState {
        ShellState::new(root.path().to_str().unwrap()).unwrap()
    }

    fn record(state: &mut ShellState, path: &str) -> Uuid {
        let op = Operation::new(OperationType::CreateFile, path.to_string(), None);
        let id = op.id;
        state.record_operation(op);
        id
    }

    fn summary(state: &ShellState) -> Vec<(Uuid, bool, Option<Uuid>)> {
        state
            .history
            .iter()
            .map(|op| (op.id, op.undone, op.undone_by))
            .collect()
    }

    #[test]
    fn test_journal_replay_restores_history_and_undo_marks() {
        let root = persisted_root();
        let mut state = reopen(&root);
        record(&mut state, "a");
        let b = record(&mut state, "b");
        record(&mut state, "c");
        state.mark_undone(b, Uuid::new_v4());

        // Hot-path operations only append to the journal.
        assert!(state.journal_file.exists());
        assert!(!state.state_file.exists());

        let reloaded = reopen(&root);
        assert_eq!(summary(&reloaded), summary(&state));
    }

    #[test]
    fn test_journal_folds_into_snapshot_and_reloads() {
        let root = persisted_root();
        let mut state = reopen(&root);
        for i in 0..(JOURNAL_MIN_ENTRIES + 10) {
            record(&mut state, &format!("f{i}"));
        }
        assert!(state.state_file.exists(), "journal should have compacted");
        assert!(state.journal_entries < JOURNAL_MIN_ENTRIES);

        let reloaded = reopen(&root);
        assert_eq!(summary(&reloaded), summary(&state));
    }

    #[test]
    fn test_journal_replays_history_trim() {
        let root = persisted_root();
        let mut state = reopen(&root);
        state.max_history_size = Some(3);
        for i in 0..5 {
            record(&mut state, &format!("f{i}"));
        }
        assert_eq!(state.history.len(), 3);

        // The reopened state has the default (larger) limit, so the trim must
        // come from the journal, not from re-applying a limit.
        let reloaded = reopen(&root);
        assert_eq!(summary(&reloaded), summary(&state));
    }

    #[test]
    fn test_journal_torn_tail_is_ignored() {
        let root = persisted_root();
        let mut state = reopen(&root);
        record(&mut state, "a");
        record(&mut state, "b");
        {
            use std::io::Write;
            let mut journal = fs::OpenOptions::new()
                .append(true)
                .open(&state.journal_file)
                .unwrap();
            journal.write_all(b"{\"seq\":3,\"entry\":{\"Rec").unwrap();
        }

        let reloaded = reopen(&root);
        assert_eq!(summary(&reloaded), summary(&state));
    }

    #[test]
    fn test_operations_after_torn_tail_survive_reload() {
        let root = persisted_root();
        let mut state = reopen(&root);
        record(&mut state, "a");
        {
            use std::io::Write;
            let mut journal = fs::OpenOptions::new()
                .append(true)
                .open(&state.journal_file)
                .unwrap();
            journal.write_all(b"{\"seq\":2,\"entry\":{\"Rec").unwrap();
        }

        // The restarted shell keeps working after the crash...
        let mut restarted = reopen(&root);
        record(&mut restarted, "b");
        record(&mut restarted, "c");

        // ...and those later operations must not hide behind the torn line.
        let reloaded = reopen(&root);
        assert_eq!(reloaded.history.len(), 3);
        assert_eq!(summary(&reloaded), summary(&restarted));
    }

    #[test]
    fn test_journal_torn_inside_multibyte_char_reopens() {
        let root = persisted_root();
        let mut state = reopen(&root);
        record(&mut state, "a");
        {
            use std::io::Write;
            let mut journal = fs::OpenOptions::new()
                .append(true)
                .open(&state.journal_file)
                .unwrap();
            // "é" is 0xC3 0xA9; stop after the first byte.
            journal
                .write_all(b"{\"seq\":2,\"entry\":{\"Record\":{\"path\":\"caf\xC3")
                .unwrap();
        }

        let mut reopened = reopen(&root);
        assert_eq!(summary(&reopened), summary(&state));
        record(&mut reopened, "b");
        let reloaded = reopen(&root);
        assert_eq!(reloaded.history.len(), 2);
    }

    #[test]
    fn test_previous_dir_survives_reload_without_snapshot() {
        let root = persisted_root();
        let mut state = reopen(&root);
        record(&mut state, "a");
        state.set_previous_dir(PathBuf::from("/tmp/elsewhere"));
        assert!(!state.state_file.exists(), "no snapshot should be needed");

        let reloaded = reopen(&root);
        assert_eq!(
            reloaded.previous_dir.as_deref(),
            Some(Path::new("/tmp/elsewhere"))
        );
    }

    #[test]
    fn test_snapshot_skips_already_folded_journal_entries() {
        let root = persisted_root();
        let mut state = reopen(&root);
        record(&mut state, "a");
        record(&mut state, "b");
        let stale_journal = fs::read(&state.journal_file).unwrap();

        // Simulate a crash after the snapshot rename but before the journal
        // was truncated: the journal still holds entries the snapshot has.
        state.save().unwrap();
        fs::write(&state.journal_file, stale_journal).unwrap();

        let reloaded = reopen(&root);
        assert_eq!(summary(&reloaded), summary(&state));
    }

    #[test]
    fn test_rolled_back_transaction_does_not_survive_reload() {
        let root = persisted_root();
        let mut state = reopen(&root);
        state.begin_transaction("t").unwrap();
        record(&mut state, "a");
        state.abort_transaction();

        let reloaded = reopen(&root);
        assert!(reloaded.active_transaction.is_none());
        assert_eq!(summary(&reloaded), summary(&state));
    }

    /// `last_n_undoable` must agree with a plain newest-first scan for
    /// non-undone operations, whatever the undone-block hint holds.
    fn assert_undoable_matches_scan(state: &ShellState) {
        let naive: Vec<Uuid> = state
            .history
            .iter()
            .rev()
            .filter(|op| !op.undone)
            .map(|op| op.id)
            .collect();
        let fast: Vec<Uuid> = state
            .last_n_undoable(usize::MAX)
            .iter()
            .map(|op| op.id)
            .collect();
        assert_eq!(fast, naive);
    }

    fn undo_one(state: &mut ShellState) {
        let id = state.last_n_undoable(1)[0].id;
        state.mark_undone(id, Uuid::new_v4());
    }

    #[test]
    fn test_undone_block_hint_agrees_with_full_scan() {
        let root = persisted_root();
        let mut state = reopen(&root);
        state.max_history_size = Some(12);
        for i in 0..10 {
            record(&mut state, &format!("a{i}"));
        }
        for _ in 0..3 {
            undo_one(&mut state);
            assert_undoable_matches_scan(&state);
        }
        // New operations after an undone block, then undo across it.
        for i in 0..4 {
            record(&mut state, &format!("b{i}"));
            assert_undoable_matches_scan(&state);
        }
        for _ in 0..6 {
            undo_one(&mut state);
            assert_undoable_matches_scan(&state);
        }
        // Out-of-order mark of an older operation.
        let oldest_live = state.last_n_undoable(usize::MAX).last().unwrap().id;
        state.mark_undone(oldest_live, Uuid::new_v4());
        assert_undoable_matches_scan(&state);
        // Trims from the front shift the block.
        for i in 0..8 {
            record(&mut state, &format!("c{i}"));
            assert_undoable_matches_scan(&state);
        }
        while !state.last_n_undoable(1).is_empty() {
            undo_one(&mut state);
            assert_undoable_matches_scan(&state);
        }
    }

    #[test]
    fn test_transaction_membership_survives_journal_replay() {
        let root = persisted_root();
        let mut state = reopen(&root);
        state.begin_transaction("t").unwrap();
        let a = record(&mut state, "a");

        let reloaded = reopen(&root);
        let txn = reloaded.active_transaction.as_ref().unwrap();
        assert_eq!(txn.operations, vec![a]);
    }
}

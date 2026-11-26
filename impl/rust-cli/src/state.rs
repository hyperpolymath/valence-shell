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

/// What a file was, apart from its content: permission bits, owner and
/// modification time.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct FileMeta {
    /// Permission and set-ID bits (the low 12 bits of the mode).
    pub mode: u32,
    pub uid: u32,
    pub gid: u32,
    /// Modification time: seconds and nanoseconds since the Unix epoch.
    pub mtime: i64,
    pub mtime_nsec: i64,
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

    /// The removed file's permissions, owner and modification time, so
    /// that undo restores the file as it was and not merely its content.
    /// Absent on operations that removed nothing and on records written
    /// before this field existed.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub undo_meta: Option<FileMeta>,

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
            undo_meta: None,
            undone: false,
            undone_by: None,
        }
    }

    pub fn with_undo_data(mut self, data: Vec<u8>) -> Self {
        self.undo_data = Some(data);
        self
    }

    pub fn with_undo_meta(mut self, meta: FileMeta) -> Self {
        self.undo_meta = Some(meta);
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

/// What [`ShellState::scrub_obliterated`] changed: the operations as they
/// were, with their places in the history, and the redo stack as it was if
/// anything was taken off it.
#[derive(Debug)]
pub struct Scrubbed {
    operations: Vec<(usize, Operation)>,
    redo_stack: Option<VecDeque<Operation>>,
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
    /// The session root: the directory the shell was started on. It is
    /// fixed for the life of the session, and nothing the shell does may
    /// reach outside it. `cd` moves [`Self::cwd`], not this.
    pub root: PathBuf,

    /// The working directory. Always the session root or a directory
    /// beneath it. Paths a user types are relative to it; paths in the
    /// history are relative to the session root, so they mean the same
    /// thing after a `cd`.
    cwd: PathBuf,

    /// An open handle on the session root. Paths given to it are relative
    /// and are resolved beneath it by the operating system, so no symlink
    /// and no `..` can make them name anything outside the session root.
    root_dir: cap_std::fs::Dir,

    /// Operation history (append-only)
    pub history: Vec<Operation>,

    /// Redo stack (operations that were undone and can be redone)
    pub redo_stack: VecDeque<Operation>,

    /// Active transaction (if any)
    pub active_transaction: Option<Transaction>,

    /// Completed transactions
    pub transactions: Vec<Transaction>,

    /// State file path for persistence
    state_file: PathBuf,

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

        let root_dir = cap_std::fs::Dir::open_ambient_dir(&root_path, cap_std::ambient_authority())
            .context("Failed to open sandbox root")?;

        let mut state = Self {
            cwd: root_path.clone(),
            root_dir,
            root: root_path,
            history: Vec::new(),
            redo_stack: VecDeque::new(),
            active_transaction: None,
            transactions: Vec::new(),
            state_file,
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
        self.root_operation_path(&mut op);
        self.record_rooted_operation(op);
    }

    /// Record an operation whose path is already relative to the session
    /// root.
    ///
    /// [`Self::record_operation`] takes a path as it was typed and makes it
    /// relative to the root, reading it against the working directory. A
    /// path that is relative to the root already must not go through that
    /// again: from `sub`, `sub/f` would become `sub/sub/f`.
    pub fn record_rooted_operation(&mut self, mut op: Operation) {
        // Associate with active transaction if any
        if let Some(ref mut txn) = self.active_transaction {
            op.transaction_id = Some(txn.id);
            txn.operations.push(op.id);
        }

        self.history.push(op);

        // Enforce history size limit
        self.enforce_history_limit();

        // Clear redo stack when new operation is performed
        self.redo_stack.clear();

        // Persist state - warn on failure but don't abort
        if let Err(e) = self.save() {
            eprintln!("{} Failed to save state: {}", "Warning:".bright_yellow(), e);
            eprintln!("Operation succeeded but may not persist across restarts");
        }
    }

    /// Record an operation from a redo without clearing the redo stack.
    ///
    /// Unlike [`Self::record_operation`], this preserves remaining redo entries
    /// so that multiple sequential redos work correctly.
    ///
    /// The path of a redone operation comes from the history, so it is
    /// relative to the session root already and is recorded as it is.
    /// Reading it against the working directory again recorded `sub/f` for
    /// `f` when the redo was done from `sub`.
    pub fn record_redo_operation(&mut self, mut op: Operation) {
        if let Some(ref mut txn) = self.active_transaction {
            op.transaction_id = Some(txn.id);
            txn.operations.push(op.id);
        }

        self.history.push(op);
        self.enforce_history_limit();

        // Persist state - warn on failure but don't abort
        if let Err(e) = self.save() {
            eprintln!("{} Failed to save state: {}", "Warning:".bright_yellow(), e);
            eprintln!("Redo succeeded but may not persist across restarts");
        }
    }

    /// Enforce history size limit by removing oldest operations
    ///
    /// When history exceeds max_history_size, removes the oldest operations.
    /// If history_archive_path is set, saves removed operations to archive.
    fn enforce_history_limit(&mut self) {
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

                // Note: This means undo can only go back `limit` operations
                // Users should be aware via configuration
            }
        }
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
        self.history
            .iter()
            .rev()
            .filter(|op| !op.undone)
            .take(n)
            .collect()
    }

    /// Mark an operation as undone
    pub fn mark_undone(&mut self, op_id: Uuid, undone_by: Uuid) {
        if let Some(op) = self.history.iter_mut().find(|o| o.id == op_id) {
            op.undone = true;
            op.undone_by = Some(undone_by);

            // Push to redo stack
            self.redo_stack.push_front(op.clone());
        }

        // Persist state - warn on failure
        if let Err(e) = self.save() {
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

    /// The directory the session was started on. It does not move with
    /// `cd`.
    pub fn session_root(&self) -> &Path {
        &self.root
    }

    /// The working directory: the session root or a directory beneath it.
    pub fn cwd(&self) -> &Path {
        &self.cwd
    }

    /// Change the working directory to `target`, which must be a directory
    /// inside the session root once every symbolic link in it is resolved.
    ///
    /// # Errors
    ///
    /// Fails if `target` is not a directory or lies outside the session
    /// root. The working directory is then unchanged.
    pub fn set_cwd(&mut self, target: &Path) -> Result<()> {
        let resolved = fs::canonicalize(target)
            .with_context(|| format!("cd: {}: No such file or directory", target.display()))?;
        if !resolved.is_dir() {
            anyhow::bail!("cd: {}: Not a directory", target.display());
        }
        if !resolved.starts_with(&self.root) {
            anyhow::bail!(
                "cd: {}: outside the session root {}",
                target.display(),
                self.root.display()
            );
        }
        // The history stores paths as text. In a directory whose name is not
        // text, every operation would be recorded under a different path,
        // and undo would act on that one. The shell does not enter a
        // directory it could not name in its history. (A name typed at the
        // prompt is always text; this is reached through a symbolic link.)
        if resolved.to_str().is_none() {
            anyhow::bail!(
                "cd: {}: the directory's name is not valid UTF-8, so operations there \
                 could not be recorded for undo",
                target.display()
            );
        }
        self.cwd = resolved;
        Ok(())
    }

    /// `typed`, a path relative to the working directory, as a path
    /// relative to the session root. This is the form the history stores.
    /// A path that does not lie inside the session root is returned as it
    /// was typed.
    pub fn rooted(&self, typed: &str) -> String {
        match self.contained(typed) {
            Ok(relative) if relative.as_os_str() == "." => String::new(),
            Ok(relative) => relative.to_string_lossy().into_owned(),
            Err(_) => typed.to_string(),
        }
    }

    /// The location of a path recorded in the history. Recorded paths are
    /// relative to the session root, whatever the working directory is now.
    pub fn resolve_op_path(&self, recorded: &str) -> PathBuf {
        resolve_under_root(&self.root, recorded)
    }

    /// Forget what the history holds about a path that has been
    /// obliterated: `rooted` itself, or anything beneath it if it was a
    /// directory.
    ///
    /// Earlier operations on the path keep their place in the history, but
    /// lose their undo data (which may be the very content that was
    /// obliterated) and are marked undone by the obliteration `by`, so that
    /// no later `undo` or `redo` can bring any of it back. The caller
    /// records the obliteration next, which saves the scrubbed history.
    ///
    /// A recorded path concerns the obliterated one if it is that path or
    /// lies beneath it, as written or once the symbolic links in its
    /// directories are resolved. The same file can be reached under two
    /// names when a link inside the session root points at its directory;
    /// comparing the names as written left the other name's records, and
    /// the content in them, in place.
    ///
    /// Returns what was changed, so that [`Self::restore_scrubbed`] can put
    /// it back if the scrubbed history then cannot be saved.
    pub fn scrub_obliterated(&mut self, rooted: &str, by: Uuid) -> Scrubbed {
        let mut scrubbed = Scrubbed {
            operations: Vec::new(),
            redo_stack: None,
        };
        if rooted.is_empty() {
            return scrubbed;
        }
        let target = self.real_location(rooted);
        // By path component, so that it holds whatever separator the
        // platform writes: `dir` contains `dir/f`, and not `directory`.
        let concerned: Vec<bool> = self
            .history
            .iter()
            .map(|op| self.concerns(op, rooted, &target))
            .collect();
        for (index, op) in self.history.iter_mut().enumerate() {
            if !concerned[index] {
                continue;
            }
            scrubbed.operations.push((index, op.clone()));
            op.undo_data = None;
            op.undo_meta = None;
            if !op.undone {
                op.undone = true;
                op.undone_by = Some(by);
            }
        }
        let kept: VecDeque<Operation> = self
            .redo_stack
            .iter()
            .filter(|op| !self.concerns(op, rooted, &target))
            .cloned()
            .collect();
        if kept.len() != self.redo_stack.len() {
            scrubbed.redo_stack = Some(std::mem::replace(&mut self.redo_stack, kept));
        }
        scrubbed
    }

    /// Put back what [`Self::scrub_obliterated`] changed. For an
    /// obliteration that did not go ahead: the file is still there, so the
    /// history must still be able to undo what was done to it.
    pub fn restore_scrubbed(&mut self, scrubbed: Scrubbed) {
        for (index, op) in scrubbed.operations {
            if let Some(slot) = self.history.get_mut(index) {
                *slot = op;
            }
        }
        if let Some(redo_stack) = scrubbed.redo_stack {
            self.redo_stack = redo_stack;
        }
    }

    /// Whether a recorded operation is about `rooted`, whose real location
    /// is `target`, or about something beneath it.
    fn concerns(&self, op: &Operation, rooted: &str, target: &Path) -> bool {
        if matches!(
            op.op_type,
            OperationType::SetVariable
                | OperationType::UnsetVariable
                | OperationType::HardwareErase
        ) {
            return false;
        }
        // An operation on a link itself (making it, removing it, moving
        // it) is about the link. Any other operation went through the link
        // to the file it points at: `echo x > alias` saved the bytes of the
        // target under the name `alias`. Such a record is also compared by
        // where its path leads now, with the last link followed too.
        let on_the_link = matches!(
            op.op_type,
            OperationType::Symlink | OperationType::Unlink | OperationType::Move
        );
        op.path.split('\0').any(|recorded| {
            Path::new(recorded).starts_with(Path::new(rooted))
                || self.real_location(recorded).starts_with(target)
                || (!on_the_link
                    && fs::canonicalize(self.resolve_op_path(recorded))
                        .is_ok_and(|real| real.starts_with(target)))
        })
    }

    /// Take out of the history archive what it holds about a path that is
    /// about to be obliterated: the undo data of every archived operation
    /// that [`Self::scrub_obliterated`] would have scrubbed in the history.
    ///
    /// Operations that age out of the history are written to the archive
    /// with their undo data, which can be the content that is being
    /// obliterated. Scrubbing only the history left that copy on disk.
    ///
    /// The archive is rewritten through a temporary file and renamed into
    /// place, so it is either the old archive or the scrubbed one. A line
    /// that cannot be read as an operation is kept as it is. Nothing is
    /// done when no archive is configured or none has been written yet.
    ///
    /// # Errors
    ///
    /// Fails if the archive cannot be read or rewritten. The caller must
    /// then not obliterate.
    pub(crate) fn scrub_archive(&self, rooted: &str) -> Result<Option<String>> {
        let Some(archive_path) = self.history_archive_path.as_ref() else {
            return Ok(None);
        };
        if rooted.is_empty() {
            return Ok(None);
        }
        let archived = match fs::read_to_string(archive_path) {
            Ok(text) => text,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(e) => {
                return Err(e).with_context(|| {
                    format!("Failed to read history archive {}", archive_path.display())
                })
            }
        };

        let target = self.real_location(rooted);
        let mut changed = false;
        let mut scrubbed = String::with_capacity(archived.len());
        for line in archived.lines() {
            match serde_json::from_str::<Operation>(line) {
                Ok(mut op)
                    if (op.undo_data.is_some() || op.undo_meta.is_some())
                        && self.concerns(&op, rooted, &target) =>
                {
                    op.undo_data = None;
                    op.undo_meta = None;
                    scrubbed.push_str(&serde_json::to_string(&op)?);
                    changed = true;
                }
                _ => scrubbed.push_str(line),
            }
            scrubbed.push('\n');
        }
        if !changed {
            return Ok(None);
        }
        self.write_archive(&scrubbed)?;
        Ok(Some(archived))
    }

    /// Put back the archive text that [`Self::scrub_archive`] returned, when
    /// what was to follow the scrub failed and nothing was obliterated.
    pub(crate) fn restore_archive(&self, original: &str) -> Result<()> {
        self.write_archive(original)
    }

    /// Replace the history archive with `text`, durably and atomically.
    fn write_archive(&self, text: &str) -> Result<()> {
        use std::io::Write;

        let Some(archive_path) = self.history_archive_path.as_ref() else {
            return Ok(());
        };
        let mut temporary = archive_path.clone().into_os_string();
        temporary.push(".scrub");
        let temporary = PathBuf::from(temporary);
        let written = (|| -> std::io::Result<()> {
            let mut file = fs::File::create(&temporary)?;
            file.write_all(text.as_bytes())?;
            file.sync_all()?;
            fs::rename(&temporary, archive_path)?;
            if let Some(parent) = archive_path.parent().filter(|p| !p.as_os_str().is_empty()) {
                fs::File::open(parent)?.sync_all()?;
            }
            Ok(())
        })();
        written.with_context(|| {
            format!(
                "Failed to rewrite history archive {}",
                archive_path.display()
            )
        })
    }

    /// Where a recorded path is now, with the symbolic links in its
    /// directories resolved as far as they still exist. The last component
    /// is kept as written: a record about a link is about the link, not
    /// about what it points to.
    fn real_location(&self, recorded: &str) -> PathBuf {
        let path = self.resolve_op_path(recorded);
        let Some(name) = path.file_name().map(std::ffi::OsStr::to_os_string) else {
            return path;
        };
        let mut missing = Vec::new();
        let mut directory = path.parent();
        while let Some(current) = directory {
            if let Ok(real) = fs::canonicalize(current) {
                let mut location = real;
                location.extend(missing.iter().rev());
                location.push(&name);
                return location;
            }
            match current.file_name() {
                Some(part) => missing.push(part.to_os_string()),
                None => break,
            }
            directory = current.parent();
        }
        path
    }

    /// Rewrite the path of an operation about to be recorded so that it is
    /// relative to the session root. Variable operations carry a name, not
    /// a path, and are left alone. A move carries two paths.
    fn root_operation_path(&self, op: &mut Operation) {
        match op.op_type {
            OperationType::SetVariable | OperationType::UnsetVariable => {}
            // A hardware erase names a device (`/dev/nvme0n1`), not a file
            // in the session root. The record must keep that name.
            OperationType::HardwareErase => {}
            OperationType::Move => {
                let rooted: Vec<String> =
                    op.path.split('\0').map(|part| self.rooted(part)).collect();
                op.path = rooted.join("\0");
            }
            _ => op.path = self.rooted(&op.path),
        }
    }

    /// The handle on the session root. Use it, with a path from
    /// [`Self::contained`], for anything that creates, changes or removes a
    /// file.
    pub fn root_dir(&self) -> &cap_std::fs::Dir {
        &self.root_dir
    }

    /// `path`, as typed relative to the working directory, as a path
    /// relative to the session root, for use with [`Self::root_dir`].
    ///
    /// # Errors
    ///
    /// Fails if the path lies outside the session root.
    pub fn contained(&self, path: &str) -> Result<PathBuf> {
        self.contained_abs(&self.resolve_path(path))
    }

    /// As [`Self::contained`], for a path already resolved by
    /// [`Self::resolve_path`].
    ///
    /// # Errors
    ///
    /// Fails if the path lies outside the session root, or is not valid
    /// UTF-8. The history stores paths as text. A path that is not text
    /// would be stored as a different path, and undo would then act on
    /// that one, so the operation is refused before anything is done.
    pub fn contained_abs(&self, full: &Path) -> Result<PathBuf> {
        let relative = full
            .strip_prefix(&self.root)
            .map_err(|_| anyhow::anyhow!("{} is outside the session root", full.display()))?;
        if relative.to_str().is_none() {
            anyhow::bail!(
                "{} is not valid UTF-8, so it could not be recorded for undo; nothing was done",
                full.display()
            );
        }
        Ok(if relative.as_os_str().is_empty() {
            PathBuf::from(".")
        } else {
            relative.to_path_buf()
        })
    }

    /// Resolve a path relative to sandbox root
    /// Prevents path traversal attacks via `..` components
    ///
    /// A path that starts with `/` is read from the session root, with one
    /// exception: a real path that lies inside the session root is that
    /// path. `pwd`, `$PWD`, `~+` and `~-` all give real paths, and reading
    /// them from the session root added the root a second time, so
    /// `touch ~+/f` failed in every directory. `cd` already read them this
    /// way. The result is inside the session root either way.
    pub fn resolve_path(&self, path: &str) -> PathBuf {
        if path.starts_with('/') && Path::new(path).starts_with(&self.root) {
            return normalise_within(&self.root, Path::new(path));
        }
        if path.starts_with('/') || self.cwd == self.root {
            return resolve_under_root(&self.root, path);
        }
        // Relative to the working directory, which is inside the root. The
        // working directory is used as the path it is: its name may hold
        // bytes that are not text, and writing it out as text and reading
        // it back would name another directory.
        resolve_under_base(&self.root, &self.cwd, path)
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

    /// Save state to file
    /// Save the history now, and report a failure. The recording functions
    /// only warn when a save fails; a caller that must not go on without
    /// the save uses this.
    pub(crate) fn save_history(&self) -> Result<()> {
        self.save()
    }

    fn save(&self) -> Result<()> {
        let state = SerializableState {
            version: STATE_FORMAT,
            history: self.history.clone(),
            transactions: self.transactions.clone(),
            active_transaction: self.active_transaction.clone(),
            previous_dir: self.previous_dir.clone(),
        };

        let json = serde_json::to_string_pretty(&state)?;
        fs::write(&self.state_file, json)?;

        Ok(())
    }

    /// Load state from file
    fn load(&mut self) -> Result<()> {
        if !self.state_file.exists() {
            return Ok(());
        }

        let json = crate::fs_pure::read_to_string(&self.state_file)?;
        let state: SerializableState = serde_json::from_str(&json)?;

        if state.version < STATE_FORMAT {
            // Before this format, a record made after `cd sub` held a path
            // relative to `sub`. Read against the session root it would
            // name a different file, and `undo` would act on that one.
            // Which records are affected cannot be told, so none are
            // applied; the old file is kept beside the new one.
            let mut legacy = self.state_file.clone().into_os_string();
            legacy.push(".legacy");
            fs::rename(&self.state_file, &legacy).with_context(|| {
                format!(
                    "Failed to set aside the old history {}",
                    self.state_file.display()
                )
            })?;
            eprintln!(
                "warning: {} was written by an older version, whose paths cannot be \
                 placed safely; starting with an empty history (old file kept as {})",
                self.state_file.display(),
                PathBuf::from(&legacy).display()
            );
            return Ok(());
        }

        self.history = state.history;
        self.transactions = state.transactions;
        self.active_transaction = state.active_transaction;
        self.previous_dir = state.previous_dir;

        Ok(())
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

/// Current state-file format: recorded paths are relative to the session root.
const STATE_FORMAT: u32 = 1;

#[derive(Serialize, Deserialize)]
struct SerializableState {
    /// Format of `history`. Absent (0) in files written before recorded
    /// paths were relative to the session root; see [`STATE_FORMAT`].
    #[serde(default)]
    version: u32,
    history: Vec<Operation>,
    transactions: Vec<Transaction>,
    active_transaction: Option<Transaction>,
    #[serde(default)]
    previous_dir: Option<PathBuf>,
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
    normalise_within(root, &raw)
}

/// Resolve the relative `path` against `base`, a directory inside the
/// sandbox `root`, under the same rule as [`resolve_under_root`].
///
/// `base` is joined as the path it is. Its name may hold bytes that are not
/// text, which writing it out as text and reading it back would change.
pub fn resolve_under_base(root: &Path, base: &Path, path: &str) -> PathBuf {
    normalise_within(root, &base.join(path))
}

/// Drop `.` components and apply `..` components of `raw`, never going above
/// `root`.
fn normalise_within(root: &Path, raw: &Path) -> PathBuf {
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

    /// A hardware erase names a device, not a file under the session root.
    /// Its record keeps that name. It used to be rewritten as `dev/nvme0n1`.
    #[test]
    fn test_a_hardware_erase_record_keeps_its_device_name() {
        let root = tempfile::tempdir().unwrap();
        let mut state = ShellState::new(root.path().to_str().unwrap()).unwrap();

        state.record_operation(Operation::new(
            OperationType::HardwareErase,
            "/dev/nvme0n1".to_string(),
            None,
        ));

        assert_eq!(state.history.last().unwrap().path, "/dev/nvme0n1");
    }

    /// Scrubbing an obliterated directory reaches what is inside it and
    /// nothing else: not a neighbour whose name only starts the same way.
    #[test]
    fn test_scrub_reaches_what_is_inside_the_directory_and_nothing_else() {
        let root = tempfile::tempdir().unwrap();
        let mut state = ShellState::new(root.path().to_str().unwrap()).unwrap();
        for path in ["dir", "dir/f", "dir/deep/g", "directory/h", "dir2"] {
            state.record_rooted_operation(
                Operation::new(OperationType::DeleteFile, path.to_string(), None)
                    .with_undo_data(b"content".to_vec()),
            );
        }

        state.scrub_obliterated("dir", Uuid::new_v4());

        let kept: Vec<&str> = state
            .history
            .iter()
            .filter(|op| op.undo_data.is_some())
            .map(|op| op.path.as_str())
            .collect();
        assert_eq!(kept, ["directory/h", "dir2"]);
    }

    /// A record of a write made through a link holds the bytes of the
    /// link's target, under the link's name. Obliterating the target must
    /// reach it. A record about the link itself (making it, removing it)
    /// is about the link, and stays.
    #[cfg(unix)]
    #[test]
    fn test_scrub_reaches_content_recorded_under_a_link_to_the_file() {
        let root = tempfile::tempdir().unwrap();
        let mut state = ShellState::new(root.path().to_str().unwrap()).unwrap();
        fs::write(root.path().join("real"), "now").unwrap();
        std::os::unix::fs::symlink("real", root.path().join("alias")).unwrap();
        for op_type in [
            OperationType::FileTruncated,
            OperationType::Symlink,
            OperationType::Unlink,
        ] {
            state.record_rooted_operation(
                Operation::new(op_type, "alias".to_string(), None).with_undo_data(b"data".to_vec()),
            );
        }

        state.scrub_obliterated("real", Uuid::new_v4());

        let kept: Vec<OperationType> = state
            .history
            .iter()
            .filter(|op| op.undo_data.is_some())
            .map(|op| op.op_type)
            .collect();
        assert_eq!(kept, [OperationType::Symlink, OperationType::Unlink]);
    }

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
}

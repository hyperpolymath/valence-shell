// SPDX-License-Identifier: PLMP-1.0-or-later
//! Shell State Management
//!
//! Manages the undo/redo stack, transaction groups, and operation history.
//! This is where reversibility guarantees are maintained at runtime.

use anyhow::{Context, Result};
use chrono::{DateTime, Utc};
use colored::Colorize;
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet, VecDeque};
use std::fs;
use std::path::PathBuf;
use uuid::Uuid;

use crate::proof_refs::ProofReference;

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

    /// State file path for persistence
    state_file: PathBuf,

    /// Last exit code from external command (for $? support)
    pub last_exit_code: i32,

    /// Previous directory for cd - support
    pub previous_dir: Option<PathBuf>,

    /// Shell variables (VAR=value)
    pub variables: HashMap<String, String>,

    /// Variables that are exported to child processes
    pub exported_vars: HashSet<String>,

    /// Positional parameters ($1, $2, ...) for script arguments
    pub positional_params: Vec<String>,
}

impl ShellState {
    /// Create new shell state with given root
    pub fn new(root: &str) -> Result<Self> {
        let root_path = PathBuf::from(root);

        // Ensure root exists
        if !root_path.exists() {
            fs::create_dir_all(&root_path).context("Failed to create sandbox root")?;
        }

        let state_file = root_path.join(".vsh_state.json");

        let mut state = Self {
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
            positional_params: Vec::new(),
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

        // Clear redo stack when new operation is performed
        self.redo_stack.clear();

        // Persist state - warn on failure but don't abort
        if let Err(e) = self.save() {
            eprintln!(
                "{} Failed to save state: {}",
                "Warning:".bright_yellow(),
                e
            );
            eprintln!("Operation succeeded but may not persist across restarts");
        }
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

    /// Resolve a path relative to sandbox root
    pub fn resolve_path(&self, path: &str) -> PathBuf {
        if path.starts_with('/') {
            self.root.join(&path[1..])
        } else {
            self.root.join(path)
        }
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
    fn save(&self) -> Result<()> {
        let state = SerializableState {
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

        let json = fs::read_to_string(&self.state_file)?;
        let state: SerializableState = serde_json::from_str(&json)?;

        self.history = state.history;
        self.transactions = state.transactions;
        self.active_transaction = state.active_transaction;
        self.previous_dir = state.previous_dir;

        Ok(())
    }

    // =========================================================================
    // Variable Management
    // =========================================================================

    /// Set a shell variable
    pub fn set_variable(&mut self, name: impl Into<String>, value: impl Into<String>) {
        self.variables.insert(name.into(), value.into());
    }

    /// Get a shell variable value
    pub fn get_variable(&self, name: &str) -> Option<&str> {
        self.variables.get(name).map(|s| s.as_str())
    }

    /// Export a variable (make it available to child processes)
    pub fn export_variable(&mut self, name: impl Into<String>) {
        self.exported_vars.insert(name.into());
    }

    /// Check if a variable is exported
    pub fn is_exported(&self, name: &str) -> bool {
        self.exported_vars.contains(name)
    }

    /// Get all exported variables as environment key-value pairs
    pub fn get_exported_env(&self) -> Vec<(String, String)> {
        self.exported_vars
            .iter()
            .filter_map(|name| {
                self.variables
                    .get(name)
                    .map(|value| (name.clone(), value.clone()))
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

#[derive(Serialize, Deserialize)]
struct SerializableState {
    history: Vec<Operation>,
    transactions: Vec<Transaction>,
    active_transaction: Option<Transaction>,
    #[serde(default)]
    previous_dir: Option<PathBuf>,
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
}

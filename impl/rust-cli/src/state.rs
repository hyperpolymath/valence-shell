// SPDX-License-Identifier: PLMP-1.0-or-later
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
use std::path::PathBuf;
use uuid::Uuid;

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
    /// Hardware-level secure erase (NIST SP 800-88 Purge)
    /// NOT REVERSIBLE - destroys entire device
    HardwareErase,
    /// Obliterate: GDPR-compliant irreversible deletion
    /// NOT REVERSIBLE - secure file deletion with no recovery
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
            OperationType::HardwareErase => None, // NOT REVERSIBLE
            OperationType::Obliterate => None, // NOT REVERSIBLE - GDPR deletion
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
            max_history_size: Some(10_000), // Default: 10k operations
            history_archive_path: None,     // No archival by default
            positional_params: Vec::new(),
            fifo_counter: std::sync::atomic::AtomicUsize::new(0),
            jobs: crate::job::JobTable::new(),
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
        self.enforce_history_limit();

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
                    if let Err(e) = self.archive_operations(&self.history[0..excess], archive_path) {
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

    /// Resolve a path relative to sandbox root
    pub fn resolve_path(&self, path: &str) -> PathBuf {
        if path.starts_with('/') {
            self.root.join(&path[1..])
        } else {
            self.root.join(path)
        }
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
        self.variables.insert(name.into(), VariableValue::Scalar(value.into()));
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
        self.variables.insert(name.into(), VariableValue::Array(array));
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
            VariableValue::Array(arr) => {
                Some(arr.values().map(|s| s.as_str()).collect())
            }
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
        self.variables.get(name).map_or(false, |v| matches!(v, VariableValue::Array(_)))
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
                            arr.values()
                                .cloned()
                                .collect::<Vec<_>>()
                                .join(" ")
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

    /// Get next unique FIFO ID for process substitution
    pub fn next_fifo_id(&self) -> usize {
        self.fifo_counter.fetch_add(1, std::sync::atomic::Ordering::SeqCst)
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
        state.set_array("arr", vec!["a".to_string(), "b".to_string(), "c".to_string()]);

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
        state.set_array("arr", vec!["one".to_string(), "two".to_string(), "three".to_string()]);
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
        state.set_array("arr", vec!["".to_string(), "nonempty".to_string(), "".to_string()]);

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
}

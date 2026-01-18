// SPDX-License-Identifier: AGPL-3.0-or-later
//! Shell State Management
//!
//! Manages the undo/redo stack, transaction groups, and operation history.
//! This is where reversibility guarantees are maintained at runtime.

use anyhow::{Context, Result};
use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use std::collections::VecDeque;
use std::fs;
use std::path::PathBuf;
use uuid::Uuid;

use crate::proof_refs::ProofReference;

/// Operation type enum matching Coq definitions
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum OperationType {
    Mkdir,
    Rmdir,
    CreateFile,
    DeleteFile,
    WriteFile,
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
        }
    }
}

/// A single filesystem operation with undo information
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

/// Transaction group for atomic multi-operation rollback
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Transaction {
    pub id: Uuid,
    pub name: String,
    pub started: DateTime<Utc>,
    pub operations: Vec<Uuid>,
    pub committed: bool,
}

/// Main shell state
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

        // Persist state
        self.save().ok();
    }

    /// Get the last undoable operation
    pub fn last_undoable(&self) -> Option<&Operation> {
        self.history
            .iter()
            .rev()
            .find(|op| !op.undone)
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
        self.save().ok();
    }

    /// Get operation by ID
    pub fn get_operation(&self, id: Uuid) -> Option<&Operation> {
        self.history.iter().find(|o| o.id == id)
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
        self.save().ok();

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
        self.save().ok();

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

        Ok(())
    }
}

#[derive(Serialize, Deserialize)]
struct SerializableState {
    history: Vec<Operation>,
    transactions: Vec<Transaction>,
    active_transaction: Option<Transaction>,
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

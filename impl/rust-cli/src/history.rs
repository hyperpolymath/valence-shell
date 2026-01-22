// SPDX-License-Identifier: PLMP-1.0-or-later
//! History management utilities
//!
//! Provides additional history analysis and export functionality.

use crate::state::{Operation, ShellState};
use serde::Serialize;

/// Export format for operation history
#[derive(Serialize)]
pub struct HistoryExport {
    pub version: &'static str,
    pub operations: Vec<OperationExport>,
    pub metadata: ExportMetadata,
}

#[derive(Serialize)]
pub struct OperationExport {
    pub id: String,
    pub operation: String,
    pub path: String,
    pub timestamp: String,
    pub undone: bool,
    pub proof_theorem: String,
    pub proof_file: String,
}

#[derive(Serialize)]
pub struct ExportMetadata {
    pub total_operations: usize,
    pub undone_operations: usize,
    pub active_transaction: Option<String>,
}

impl HistoryExport {
    /// Create export from shell state
    pub fn from_state(state: &ShellState) -> Self {
        let operations: Vec<OperationExport> = state
            .history
            .iter()
            .map(|op| {
                let proof = op.op_type.proof_reference();
                OperationExport {
                    id: op.id.to_string(),
                    operation: op.op_type.to_string(),
                    path: op.path.clone(),
                    timestamp: op.timestamp.to_rfc3339(),
                    undone: op.undone,
                    proof_theorem: proof.theorem.to_string(),
                    proof_file: proof.coq_location.to_string(),
                }
            })
            .collect();

        Self {
            version: "1.0",
            operations,
            metadata: ExportMetadata {
                total_operations: state.history.len(),
                undone_operations: state.history.iter().filter(|o| o.undone).count(),
                active_transaction: state
                    .active_transaction
                    .as_ref()
                    .map(|t| t.name.clone()),
            },
        }
    }

    /// Export as JSON
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }
}

/// Compute undo path from current state to initial state
pub fn compute_undo_path(state: &ShellState) -> Vec<UndoStep> {
    state
        .history
        .iter()
        .filter(|op| !op.undone)
        .rev()
        .filter_map(|op| {
            op.op_type.inverse().map(|inv| UndoStep {
                original_op: op.id.to_string()[..8].to_string(),
                inverse_operation: inv.to_string(),
                path: op.path.clone(),
            })
        })
        .collect()
}

#[derive(Debug)]
pub struct UndoStep {
    pub original_op: String,
    pub inverse_operation: String,
    pub path: String,
}

/// Statistics about shell usage
pub struct HistoryStats {
    pub total_operations: usize,
    pub mkdir_count: usize,
    pub rmdir_count: usize,
    pub create_count: usize,
    pub delete_count: usize,
    pub undo_count: usize,
    pub transaction_count: usize,
}

impl HistoryStats {
    pub fn from_state(state: &ShellState) -> Self {
        use crate::state::OperationType::*;

        let mut stats = Self {
            total_operations: state.history.len(),
            mkdir_count: 0,
            rmdir_count: 0,
            create_count: 0,
            delete_count: 0,
            undo_count: state.history.iter().filter(|o| o.undone).count(),
            transaction_count: state.transactions.len(),
        };

        for op in &state.history {
            match op.op_type {
                Mkdir => stats.mkdir_count += 1,
                Rmdir => stats.rmdir_count += 1,
                CreateFile => stats.create_count += 1,
                DeleteFile => stats.delete_count += 1,
                WriteFile => {}
            }
        }

        stats
    }
}

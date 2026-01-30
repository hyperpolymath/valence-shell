// SPDX-License-Identifier: PLMP-1.0-or-later
//! Command Implementations
//!
//! Each command performs the operation, records it in history,
//! and shows proof references if verbose mode is enabled.

use anyhow::{Context, Result};
use colored::Colorize;
use std::fs;

use crate::proof_refs;
use crate::state::{Operation, OperationType, ShellState};
use crate::verification;

// Secure deletion (RMO - Remove-Match-Obliterate)
pub mod secure_deletion;

/// Create a directory at the specified path.
///
/// This operation is reversible via [`undo`] and corresponds to the Lean 4 theorem
/// `mkdir_rmdir_reversible` in FilesystemModel.lean.
///
/// # Arguments
/// * `state` - Mutable shell state for recording the operation
/// * `path` - Path relative to shell root or absolute path
/// * `verbose` - Whether to show proof references
///
/// # Errors
/// Returns error if:
/// - Path already exists (EEXIST)
/// - Parent directory doesn't exist (ENOENT)
/// - Insufficient permissions
///
/// # Examples
/// ```no_run
/// use vsh::commands;
/// use vsh::state::ShellState;
///
/// let mut state = ShellState::new("/tmp/test")?;
/// commands::mkdir(&mut state, "project", false)?;
/// # Ok::<(), anyhow::Error>(())
/// ```
pub fn mkdir(state: &mut ShellState, path: &str, verbose: bool) -> Result<()> {
    let full_path = state.resolve_path(path);

    // Optional Lean 4 verification (compile-time feature flag)
    // Provides mathematical guarantee that preconditions are satisfied
    verification::verify_mkdir(state.root(), path)?;

    // Check preconditions (matching Coq)
    if full_path.exists() {
        anyhow::bail!("Path already exists (EEXIST)");
    }

    let parent = full_path.parent().context("Invalid path")?;
    if !parent.exists() {
        anyhow::bail!("Parent directory does not exist (ENOENT)");
    }

    // Execute operation
    fs::create_dir(&full_path).context("mkdir failed")?;

    // Record in history
    let op = Operation::new(OperationType::Mkdir, path.to_string(), None);
    let op_id = op.id;
    state.record_operation(op);

    // Output
    println!(
        "{} {} {}",
        format!("[op:{}]", &op_id.to_string()[..8]).bright_black(),
        "mkdir".bright_green(),
        path
    );

    if verbose {
        let proof = OperationType::Mkdir.proof_reference();
        println!("    {} {}", "Proof:".bright_black(), proof.format_short());
        println!(
            "    {} rmdir {}",
            "Undo:".bright_black(),
            path
        );
    }

    Ok(())
}

/// Remove an empty directory at the specified path.
///
/// This operation is reversible via [`undo`] and corresponds to the Lean 4 theorem
/// `rmdir_mkdir_reversible` in FilesystemModel.lean.
///
/// # Arguments
/// * `state` - Mutable shell state for recording the operation
/// * `path` - Path relative to shell root or absolute path
/// * `verbose` - Whether to show proof references
///
/// # Errors
/// Returns error if:
/// - Path does not exist (ENOENT)
/// - Path is not a directory (ENOTDIR)
/// - Directory is not empty (ENOTEMPTY)
/// - Insufficient permissions
///
/// # Examples
/// ```no_run
/// # use vsh::commands;
/// # use vsh::state::ShellState;
/// let mut state = ShellState::new("/tmp/test")?;
/// commands::mkdir(&mut state, "old_dir", false)?;
/// commands::rmdir(&mut state, "old_dir", false)?;
/// # Ok::<(), anyhow::Error>(())
/// ```
pub fn rmdir(state: &mut ShellState, path: &str, verbose: bool) -> Result<()> {
    let full_path = state.resolve_path(path);

    // Optional Lean 4 verification
    verification::verify_rmdir(state.root(), path)?;

    // Check preconditions
    if !full_path.exists() {
        anyhow::bail!("Path does not exist (ENOENT)");
    }
    if !full_path.is_dir() {
        anyhow::bail!("Path is not a directory (ENOTDIR)");
    }
    if fs::read_dir(&full_path)?.next().is_some() {
        anyhow::bail!("Directory is not empty (ENOTEMPTY)");
    }

    // Execute
    fs::remove_dir(&full_path).context("rmdir failed")?;

    // Record
    let op = Operation::new(OperationType::Rmdir, path.to_string(), None);
    let op_id = op.id;
    state.record_operation(op);

    println!(
        "{} {} {}",
        format!("[op:{}]", &op_id.to_string()[..8]).bright_black(),
        "rmdir".bright_yellow(),
        path
    );

    if verbose {
        let proof = OperationType::Rmdir.proof_reference();
        println!("    {} {}", "Proof:".bright_black(), proof.format_short());
    }

    Ok(())
}

/// Create an empty file at the specified path.
///
/// This operation is reversible via [`undo`] and corresponds to the Lean 4 theorem
/// `createFile_deleteFile_reversible` in FileOperations.lean.
///
/// # Arguments
/// * `state` - Mutable shell state for recording the operation
/// * `path` - Path relative to shell root or absolute path
/// * `verbose` - Whether to show proof references
///
/// # Errors
/// Returns error if:
/// - Path already exists (EEXIST)
/// - Parent directory doesn't exist (ENOENT)
/// - Insufficient permissions
///
/// # Examples
/// ```no_run
/// # use vsh::commands;
/// # use vsh::state::ShellState;
/// let mut state = ShellState::new("/tmp/test")?;
/// commands::touch(&mut state, "README.md", false)?;
/// # Ok::<(), anyhow::Error>(())
/// ```
pub fn touch(state: &mut ShellState, path: &str, verbose: bool) -> Result<()> {
    let full_path = state.resolve_path(path);

    // Optional Lean 4 verification
    verification::verify_create_file(state.root(), path)?;

    if full_path.exists() {
        anyhow::bail!("Path already exists (EEXIST)");
    }

    let parent = full_path.parent().context("Invalid path")?;
    if !parent.exists() {
        anyhow::bail!("Parent directory does not exist (ENOENT)");
    }

    fs::write(&full_path, "").context("touch failed")?;

    let op = Operation::new(OperationType::CreateFile, path.to_string(), None);
    let op_id = op.id;
    state.record_operation(op);

    println!(
        "{} {} {}",
        format!("[op:{}]", &op_id.to_string()[..8]).bright_black(),
        "touch".bright_green(),
        path
    );

    if verbose {
        let proof = OperationType::CreateFile.proof_reference();
        println!("    {} {}", "Proof:".bright_black(), proof.format_short());
        println!("    {} rm {}", "Undo:".bright_black(), path);
    }

    Ok(())
}

/// Remove a file at the specified path.
///
/// The file's content is preserved for undo. This operation is reversible via [`undo`]
/// and corresponds to the Lean 4 theorem `deleteFile_createFile_reversible`.
///
/// # Arguments
/// * `state` - Mutable shell state for recording the operation
/// * `path` - Path relative to shell root or absolute path
/// * `verbose` - Whether to show proof references
///
/// # Errors
/// Returns error if:
/// - Path does not exist (ENOENT)
/// - Path is a directory (EISDIR) - use [`rmdir`] instead
/// - Insufficient permissions
///
/// # Examples
/// ```no_run
/// # use vsh::commands;
/// # use vsh::state::ShellState;
/// let mut state = ShellState::new("/tmp/test")?;
/// commands::touch(&mut state, "temp.txt", false)?;
/// commands::rm(&mut state, "temp.txt", false)?;
/// commands::undo(&mut state, 1, false)?;  // File restored
/// # Ok::<(), anyhow::Error>(())
/// ```
pub fn rm(state: &mut ShellState, path: &str, verbose: bool) -> Result<()> {
    let full_path = state.resolve_path(path);

    // Optional Lean 4 verification
    verification::verify_delete_file(state.root(), path)?;

    if !full_path.exists() {
        anyhow::bail!("Path does not exist (ENOENT)");
    }
    if full_path.is_dir() {
        anyhow::bail!("Path is a directory - use rmdir (EISDIR)");
    }

    // Store content for undo
    let content = fs::read(&full_path).unwrap_or_default();

    fs::remove_file(&full_path).context("rm failed")?;

    let op = Operation::new(OperationType::DeleteFile, path.to_string(), None)
        .with_undo_data(content);
    let op_id = op.id;
    state.record_operation(op);

    println!(
        "{} {} {}",
        format!("[op:{}]", &op_id.to_string()[..8]).bright_black(),
        "rm".bright_red(),
        path
    );

    if verbose {
        let proof = OperationType::DeleteFile.proof_reference();
        println!("    {} {}", "Proof:".bright_black(), proof.format_short());
    }

    Ok(())
}

/// Undo the last N operations.
///
/// Reverses operations in reverse order, executing their inverse operations.
/// Each undo is itself a new operation and can be undone with [`redo`].
///
/// # Arguments
/// * `state` - Mutable shell state for accessing history
/// * `count` - Number of operations to undo (default: 1)
/// * `verbose` - Whether to show proof references
///
/// # Errors
/// Returns error if:
/// - No operations to undo
/// - Inverse operation fails (filesystem inconsistency)
/// - Missing undo data for file operations
///
/// # Examples
/// ```no_run
/// # use vsh::commands;
/// # use vsh::state::ShellState;
/// let mut state = ShellState::new("/tmp/test")?;
/// commands::mkdir(&mut state, "test", false)?;
/// commands::undo(&mut state, 1, false)?;  // Removes test/
/// # Ok::<(), anyhow::Error>(())
/// ```
pub fn undo(state: &mut ShellState, count: usize, verbose: bool) -> Result<()> {
    // Clone operations to avoid borrowing state
    let ops_to_undo: Vec<Operation> = state.last_n_undoable(count).into_iter().cloned().collect();

    if ops_to_undo.is_empty() {
        println!("{}", "Nothing to undo".bright_yellow());
        return Ok(());
    }

    for op in &ops_to_undo {
        // Check if operation is reversible
        let Some(inverse_type) = op.op_type.inverse() else {
            println!(
                "{} {} (irreversible: {})",
                "Cannot undo".bright_red(),
                op.path,
                op.op_type
            );
            continue;
        };

        let path = state.resolve_path(&op.path);

        // Execute inverse operation
        match inverse_type {
            OperationType::Rmdir => {
                fs::remove_dir(&path).context("Undo mkdir failed")?;
            }
            OperationType::Mkdir => {
                fs::create_dir(&path).context("Undo rmdir failed")?;
            }
            OperationType::DeleteFile => {
                fs::remove_file(&path).context("Undo touch failed")?;
            }
            OperationType::CreateFile => {
                let content = op.undo_data.as_ref().cloned().unwrap_or_default();
                fs::write(&path, content).context("Undo rm failed")?;
            }
            OperationType::WriteFile => {
                let content = op.undo_data.as_ref().cloned().unwrap_or_default();
                fs::write(&path, content).context("Undo write failed")?;
            }
            OperationType::FileAppended => {
                // Undo append: truncate file to original size
                let size_bytes = op.undo_data.as_ref().context("Missing original size for undo")?;
                let original_size = u64::from_le_bytes(
                    size_bytes[..8]
                        .try_into()
                        .context("Invalid size data")?,
                );

                use std::fs::OpenOptions;
                let file = OpenOptions::new()
                    .write(true)
                    .open(&path)
                    .context("Failed to open file for truncation")?;
                file.set_len(original_size)
                    .context("Undo append (truncate) failed")?;
            }
            OperationType::FileTruncated => {
                // Handled by WriteFile inverse (restore original content)
                unreachable!("FileTruncated inverse is WriteFile, handled above");
            }
            OperationType::HardwareErase | OperationType::Obliterate => {
                // These have no inverse (inverse() returns None), so we never get here
                unreachable!("Irreversible operations filtered out above");
            }
        }

        // Record the undo operation
        let undo_op = Operation::new(inverse_type, op.path.clone(), None);
        let undo_id = undo_op.id;
        let orig_id = op.id;

        state.mark_undone(orig_id, undo_id);

        println!(
            "{} {} {} {} {}",
            format!("[op:{}]", &undo_id.to_string()[..8]).bright_black(),
            "undo".bright_magenta(),
            format!("[op:{}]", &orig_id.to_string()[..8]).bright_black(),
            inverse_type.to_string().bright_yellow(),
            op.path
        );

        if verbose {
            let proof = proof_refs::COMPOSITION_REVERSIBLE;
            println!("    {} {}", "Proof:".bright_black(), proof.format_short());
        }
    }

    Ok(())
}

/// Redo the last N undone operations.
///
/// Re-applies operations that were reversed with [`undo`]. Redo moves forward
/// in the operation history, restoring the previous state.
///
/// # Arguments
/// * `state` - Mutable shell state for accessing redo stack
/// * `count` - Number of operations to redo (default: 1)
/// * `verbose` - Whether to show proof references
///
/// # Errors
/// Returns error if:
/// - No operations to redo
/// - Re-executing operation fails (filesystem changed externally)
///
/// # Examples
/// ```no_run
/// # use vsh::commands;
/// # use vsh::state::ShellState;
/// let mut state = ShellState::new("/tmp/test")?;
/// commands::mkdir(&mut state, "test", false)?;
/// commands::undo(&mut state, 1, false)?;   // Removes test/
/// commands::redo(&mut state, 1, false)?;   // Recreates test/
/// # Ok::<(), anyhow::Error>(())
/// ```
pub fn redo(state: &mut ShellState, count: usize, verbose: bool) -> Result<()> {
    for _ in 0..count {
        let op = match state.pop_redo() {
            Some(op) => op,
            None => {
                println!("{}", "Nothing to redo".bright_yellow());
                break;
            }
        };

        let path = state.resolve_path(&op.path);

        // Re-execute the original operation
        match op.op_type {
            OperationType::Mkdir => {
                fs::create_dir(&path).context("Redo mkdir failed")?;
            }
            OperationType::Rmdir => {
                fs::remove_dir(&path).context("Redo rmdir failed")?;
            }
            OperationType::CreateFile => {
                fs::write(&path, "").context("Redo touch failed")?;
            }
            OperationType::DeleteFile => {
                fs::remove_file(&path).context("Redo rm failed")?;
            }
            OperationType::WriteFile => {
                // Would need new content
                anyhow::bail!("WriteFile redo not yet implemented");
            }
            OperationType::FileTruncated => {
                // Redo truncate: truncate file (original undo_data was the old content)
                fs::write(&path, "").context("Redo truncate failed")?;
            }
            OperationType::FileAppended => {
                // Cannot redo append without knowing what was appended
                anyhow::bail!("FileAppended redo not yet implemented (would need appended content)");
            }
            OperationType::HardwareErase | OperationType::Obliterate => {
                // Cannot redo - irreversible operations
                anyhow::bail!("{:?} cannot be redone - operation is irreversible", op.op_type);
            }
        }

        let new_op = Operation::new(op.op_type, op.path.clone(), None);
        let new_id = new_op.id;
        state.record_operation(new_op);

        println!(
            "{} {} {}",
            format!("[op:{}]", &new_id.to_string()[..8]).bright_black(),
            "redo".bright_cyan(),
            op.path
        );

        if verbose {
            let proof = op.op_type.proof_reference();
            println!("    {} {}", "Proof:".bright_black(), proof.format_short());
        }
    }

    Ok(())
}

/// Show operation history with optional proof references.
///
/// Displays the last N operations in reverse chronological order, showing operation
/// IDs, timestamps, types, and paths. With `show_proofs`, includes theorem references.
///
/// # Arguments
/// * `state` - Shell state for accessing history
/// * `count` - Number of operations to show (default: 10)
/// * `show_proofs` - Whether to show Lean 4 theorem references
///
/// # Examples
/// ```no_run
/// # use vsh::commands;
/// # use vsh::state::ShellState;
/// let state = ShellState::new("/tmp/test")?;
/// commands::history(&state, 10, false)?;  // Show last 10 operations
/// commands::history(&state, 5, true)?;    // Show last 5 with proofs
/// # Ok::<(), anyhow::Error>(())
/// ```
pub fn history(state: &ShellState, count: usize, show_proofs: bool) -> Result<()> {
    let history = state.get_history(count);

    if history.is_empty() {
        println!("{}", "No operations in history".bright_yellow());
        return Ok(());
    }

    println!("{}", "═══ Operation History ═══".bright_blue().bold());
    println!();

    for op in history.iter().rev() {
        let status = if op.undone {
            format!("[undone by {}]", op.undone_by.map(|u| u.to_string()[..8].to_string()).unwrap_or_default())
                .bright_red()
        } else {
            "".normal()
        };

        println!(
            "{} {} {} {} {}",
            format!("[{}]", &op.id.to_string()[..8]).bright_black(),
            op.timestamp.format("%H:%M:%S").to_string().bright_black(),
            op.op_type.to_string().bright_green(),
            op.path,
            status
        );

        if show_proofs {
            let proof = op.op_type.proof_reference();
            println!("    {} {}", "Theorem:".bright_black(), proof.format_short());
        }
    }

    println!();
    println!(
        "{} {} operations shown",
        "Total:".bright_black(),
        history.len()
    );

    Ok(())
}

/// Begin a new transaction group.
///
/// All subsequent operations are grouped under this transaction until
/// [`commit_transaction`] or [`rollback_transaction`] is called.
///
/// # Arguments
/// * `state` - Mutable shell state for transaction management
/// * `name` - Transaction name for identification
///
/// # Errors
/// Returns error if:
/// - A transaction is already active
/// - State persistence fails
///
/// # Examples
/// ```no_run
/// # use vsh::commands;
/// # use vsh::state::ShellState;
/// let mut state = ShellState::new("/tmp/test")?;
/// commands::begin_transaction(&mut state, "setup")?;
/// commands::mkdir(&mut state, "src", false)?;
/// commands::touch(&mut state, "src/main.rs", false)?;
/// commands::commit_transaction(&mut state)?;
/// # Ok::<(), anyhow::Error>(())
/// ```
pub fn begin_transaction(state: &mut ShellState, name: &str) -> Result<()> {
    let id = state.begin_transaction(name)?;
    println!(
        "{} {} {}",
        format!("[txn:{}]", &id.to_string()[..8]).bright_black(),
        "begin".bright_cyan(),
        name.bright_white()
    );
    Ok(())
}

/// Commit the current transaction, making all operations permanent.
///
/// Finalizes the active transaction started with [`begin_transaction`].
/// All operations in the transaction become part of the permanent history.
///
/// # Arguments
/// * `state` - Mutable shell state for transaction management
///
/// # Errors
/// Returns error if:
/// - No active transaction
/// - State persistence fails
///
/// # Examples
/// ```no_run
/// # use vsh::commands;
/// # use vsh::state::ShellState;
/// let mut state = ShellState::new("/tmp/test")?;
/// commands::begin_transaction(&mut state, "feature")?;
/// commands::mkdir(&mut state, "new_feature", false)?;
/// commands::commit_transaction(&mut state)?;  // Makes changes permanent
/// # Ok::<(), anyhow::Error>(())
/// ```
pub fn commit_transaction(state: &mut ShellState) -> Result<()> {
    let ops = state.current_transaction_ops();
    let op_count = ops.len();

    state.commit_transaction()?;

    println!(
        "{} {} operations",
        "Transaction committed:".bright_green(),
        op_count
    );
    Ok(())
}

/// Rollback the current transaction, reversing all operations atomically.
///
/// Undoes all operations in the active transaction started with [`begin_transaction`].
/// Operations are reversed in LIFO order. Reports partial failures if any rollback fails.
///
/// # Arguments
/// * `state` - Mutable shell state for transaction management
///
/// # Errors
/// Returns error if:
/// - No active transaction
/// - Rollback operations fail (reports which operations failed)
///
/// # Examples
/// ```no_run
/// # use vsh::commands;
/// # use vsh::state::ShellState;
/// let mut state = ShellState::new("/tmp/test")?;
/// commands::begin_transaction(&mut state, "experiment")?;
/// commands::mkdir(&mut state, "temp", false)?;
/// commands::touch(&mut state, "temp/file.txt", false)?;
/// commands::rollback_transaction(&mut state)?;  // Removes temp/ and file
/// # Ok::<(), anyhow::Error>(())
/// ```
pub fn rollback_transaction(state: &mut ShellState) -> Result<()> {
    let ops: Vec<_> = state.current_transaction_ops().iter().map(|o| (*o).clone()).collect();

    if ops.is_empty() {
        println!("{}", "Nothing to rollback".bright_yellow());
        return Ok(());
    }

    // Collect rollback failures
    let mut failed_rollbacks: Vec<(String, String)> = Vec::new();

    // Undo all operations in reverse order
    for op in ops.iter().rev() {
        if let Some(inverse_type) = op.op_type.inverse() {
            let path = state.resolve_path(&op.path);

            let result = match inverse_type {
                OperationType::Rmdir => {
                    fs::remove_dir(&path).context("Failed to remove directory")
                }
                OperationType::Mkdir => {
                    fs::create_dir(&path).context("Failed to create directory")
                }
                OperationType::DeleteFile => {
                    fs::remove_file(&path).context("Failed to remove file")
                }
                OperationType::CreateFile => {
                    let content = op.undo_data.as_ref().cloned().unwrap_or_default();
                    fs::write(&path, content).context("Failed to restore file")
                }
                OperationType::WriteFile => {
                    let content = op.undo_data.as_ref().cloned().unwrap_or_default();
                    fs::write(&path, content).context("Failed to restore file content")
                }
                OperationType::FileAppended => {
                    // Rollback append: truncate file to original size
                    if let Some(size_bytes) = op.undo_data.as_ref() {
                        if let Ok(size_array) = size_bytes[..8].try_into() {
                            let original_size = u64::from_le_bytes(size_array);
                            use std::fs::OpenOptions;
                            OpenOptions::new()
                                .write(true)
                                .open(&path)
                                .and_then(|file| file.set_len(original_size))
                                .context("Failed to truncate file")
                        } else {
                            Err(anyhow::anyhow!("Invalid size data in undo_data"))
                        }
                    } else {
                        Err(anyhow::anyhow!("Missing size data for append rollback"))
                    }
                }
                OperationType::FileTruncated => {
                    // Handled by WriteFile inverse (restore original content)
                    unreachable!("FileTruncated inverse is WriteFile, handled above");
                }
                OperationType::HardwareErase | OperationType::Obliterate => {
                    // This should never happen - these have no inverse (inverse() returns None)
                    unreachable!("Irreversible operations should not reach here");
                }
            };

            // Collect failures
            if let Err(e) = result {
                failed_rollbacks.push((op.path.clone(), e.to_string()));
            }
        }
    }

    // Clear the transaction
    state.active_transaction = None;

    // Report results
    if failed_rollbacks.is_empty() {
        println!(
            "{} {} operations",
            "Transaction rolled back:".bright_green(),
            ops.len()
        );
        Ok(())
    } else {
        let succeeded = ops.len() - failed_rollbacks.len();
        eprintln!(
            "{} {} succeeded, {} failed",
            "Partial rollback:".bright_yellow(),
            succeeded,
            failed_rollbacks.len()
        );

        for (path, err) in &failed_rollbacks {
            eprintln!("  {} {}: {}", "Failed:".bright_red(), path, err);
        }

        anyhow::bail!(
            "Transaction rollback incomplete: {}/{} operations failed",
            failed_rollbacks.len(),
            ops.len()
        )
    }
}

/// Display the operation dependency graph (DAG).
///
/// Shows the current state in the operation history as a directed acyclic graph.
/// Illustrates how operations build upon each other and the undo path.
///
/// # Arguments
/// * `state` - Shell state for accessing operation history
///
/// # Examples
/// ```no_run
/// # use vsh::commands;
/// # use vsh::state::ShellState;
/// let state = ShellState::new("/tmp/test")?;
/// commands::show_graph(&state)?;  // Displays ASCII DAG
/// # Ok::<(), anyhow::Error>(())
/// ```
pub fn show_graph(state: &ShellState) -> Result<()> {
    let history = state.get_history(20);

    println!("{}", "═══ Operation DAG ═══".bright_blue().bold());
    println!();
    println!("┌─────────────────────────────────────┐");
    println!("│ {} │", "[initial state]".bright_black());
    println!("└───────────────┬─────────────────────┘");

    for (i, op) in history.iter().rev().enumerate() {
        let is_last = i == history.len() - 1;
        let status_marker = if op.undone { "✗" } else { "○" };

        println!("                │");
        println!(
            "                │ {} {} {}",
            format!("op:{}", i + 1).bright_black(),
            op.op_type,
            op.path
        );
        println!("                ▼");

        if is_last {
            println!("┌─────────────────────────────────────┐");
            println!(
                "│ {} state_{} {} │",
                status_marker.bright_green(),
                i + 1,
                "◄── YOU ARE HERE".bright_yellow()
            );
            println!("└─────────────────────────────────────┘");
        } else {
            println!("┌─────────────────────────────────────┐");
            println!("│ {} state_{} │", status_marker, i + 1);
            println!("└───────────────┬─────────────────────┘");
        }
    }

    if history.is_empty() {
        println!("                │");
        println!("                │ (no operations)");
        println!("                ▼");
        println!("┌─────────────────────────────────────┐");
        println!(
            "│ {} │",
            "[current state] ◄── YOU ARE HERE".bright_yellow()
        );
        println!("└─────────────────────────────────────┘");
    }

    println!();

    // Show undo path
    let undoable: Vec<_> = history.iter().filter(|o| !o.undone).collect();
    if !undoable.is_empty() {
        print!("{} ", "Undo path:".bright_black());
        for (i, op) in undoable.iter().enumerate() {
            if i > 0 {
                print!(" → ");
            }
            // Defensive: handle operations without inverses (shouldn't happen currently)
            let inverse_str = op.op_type.inverse()
                .map(|inv| format!("{} {}", inv, op.path))
                .unwrap_or_else(|| format!("[non-reversible: {}]", op.path));
            print!("{}", inverse_str.bright_yellow());
        }
        print!(" → [initial]\n");
    }

    Ok(())
}

/// Display formal verification status and proof system coverage.
///
/// Shows all proof references with their locations in Coq, Lean 4, Agda,
/// Isabelle, and other verification systems. Provides verification statistics.
///
/// # Examples
/// ```no_run
/// use vsh::commands;
/// commands::show_proofs()?;  // Displays proof verification summary
/// # Ok::<(), anyhow::Error>(())
/// ```
pub fn show_proofs() -> Result<()> {
    proof_refs::print_verification_summary();
    Ok(())
}

/// List all jobs with their status.
///
/// Displays job ID, state (Running/Stopped/Done), and command string.
/// The current job is marked with `+`, the previous job with `-`.
///
/// # Arguments
/// * `state` - Shell state containing job table
/// * `long` - If true, show process IDs (not yet implemented)
///
/// # Examples
/// ```no_run
/// use vsh::commands;
/// use vsh::state::ShellState;
///
/// let state = ShellState::new("/tmp")?;
/// commands::jobs(&state, false)?;
/// # Ok::<(), anyhow::Error>(())
/// ```
pub fn jobs(state: &ShellState, _long: bool) -> Result<()> {
    let lines = state.jobs.list_jobs();

    if lines.is_empty() {
        // No jobs to display
        return Ok(());
    }

    for line in lines {
        println!("{}", line);
    }

    Ok(())
}

/// Bring a job to the foreground.
///
/// Moves the specified job (or current job if none specified) to foreground,
/// giving it terminal control. If the job was stopped, sends SIGCONT to resume it.
///
/// # Arguments
/// * `state` - Shell state containing job table
/// * `job_spec` - Job specification (%1, %+, etc.) or None for current job
///
/// # Errors
/// Returns error if job does not exist or terminal control fails.
pub fn fg(state: &mut ShellState, job_spec: Option<&str>) -> Result<()> {
    let spec = job_spec.unwrap_or("%+");

    // Find the job
    let job = state.jobs.get_job(spec)
        .ok_or_else(|| anyhow::anyhow!("fg: no such job: {}", spec))?;

    let pgid = job.pgid;
    let job_id = job.id;
    let job_state = job.state;

    println!("{}", job.command.trim_end_matches(" &"));

    #[cfg(unix)]
    {
        use crate::job::JobState;

        // Give terminal control to job
        unsafe {
            libc::tcsetpgrp(libc::STDIN_FILENO, pgid);
        }

        // If job is stopped, send SIGCONT to resume
        if job_state == JobState::Stopped {
            unsafe {
                libc::kill(-pgid, libc::SIGCONT);
            }
        }

        // Update job state to running
        state.jobs.update_job_state(pgid, JobState::Running);

        // Wait for job to complete or stop
        let mut status: i32 = 0;
        unsafe {
            libc::waitpid(-pgid, &mut status, libc::WUNTRACED);
        }

        // Return terminal control to shell
        let shell_pgid = unsafe { libc::getpgrp() };
        unsafe {
            libc::tcsetpgrp(libc::STDIN_FILENO, shell_pgid);
        }

        // Update job state based on wait result
        if unsafe { libc::WIFSTOPPED(status) } {
            state.jobs.update_job_state(pgid, JobState::Stopped);
            println!("\n[{}]+  Stopped              {}", job_id, state.jobs.get_job(spec).unwrap().command.trim_end_matches(" &"));
        } else {
            // Job completed - remove from table
            state.jobs.remove_job(job_id);
        }
    }

    #[cfg(not(unix))]
    {
        anyhow::bail!("fg: job control not supported on this platform");
    }

    Ok(())
}

/// Continue a stopped job in the background.
///
/// Sends SIGCONT to the specified job (or current job if none specified)
/// to resume execution in the background.
///
/// # Arguments
/// * `state` - Shell state containing job table
/// * `job_spec` - Job specification (%1, %+, etc.) or None for current job
///
/// # Errors
/// Returns error if job does not exist or is not stopped.
pub fn bg(state: &mut ShellState, job_spec: Option<&str>) -> Result<()> {
    let spec = job_spec.unwrap_or("%+");

    // Find the job
    let job = state.jobs.get_job(spec)
        .ok_or_else(|| anyhow::anyhow!("bg: no such job: {}", spec))?;

    let pgid = job.pgid;
    let job_id = job.id;
    let job_state = job.state;

    #[cfg(unix)]
    {
        use crate::job::JobState;

        if job_state != JobState::Stopped {
            anyhow::bail!("bg: job is already running");
        }

        // Send SIGCONT to resume job in background
        unsafe {
            libc::kill(-pgid, libc::SIGCONT);
        }

        // Update job state
        state.jobs.update_job_state(pgid, JobState::Running);

        // Print job info (bash-style)
        let job = state.jobs.get_job(spec).unwrap();
        println!("[{}]+ {}", job_id, job.command);
    }

    #[cfg(not(unix))]
    {
        anyhow::bail!("bg: job control not supported on this platform");
    }

    Ok(())
}

/// Send a signal to a job.
///
/// Sends the specified signal (or SIGTERM if none specified) to all processes
/// in the job's process group.
///
/// # Arguments
/// * `state` - Shell state containing job table
/// * `signal` - Signal to send (-9, -SIGTERM, etc.) or None for SIGTERM
/// * `job_spec` - Job specification (%1, %+, etc.)
///
/// # Errors
/// Returns error if job does not exist or signal sending fails.
pub fn kill_job(state: &mut ShellState, signal: Option<&str>, job_spec: &str) -> Result<()> {
    // Find the job
    let job = state.jobs.get_job(job_spec)
        .ok_or_else(|| anyhow::anyhow!("kill: no such job: {}", job_spec))?;

    let pgid = job.pgid;

    #[cfg(unix)]
    {
        // Parse signal (default SIGTERM)
        let sig = if let Some(sig_str) = signal {
            parse_signal(sig_str)?
        } else {
            libc::SIGTERM
        };

        // Send signal to process group
        let result = unsafe { libc::kill(-pgid, sig) };

        if result == -1 {
            anyhow::bail!("kill: failed to send signal to job {}", job_spec);
        }

        // Mark job as done if we sent SIGKILL or SIGTERM
        if sig == libc::SIGKILL || sig == libc::SIGTERM {
            use crate::job::JobState;
            state.jobs.update_job_state(pgid, JobState::Done);
        }
    }

    #[cfg(not(unix))]
    {
        anyhow::bail!("kill: job control not supported on this platform");
    }

    Ok(())
}

/// Parse a signal specification (-9, -SIGTERM, etc.) into a signal number
#[cfg(unix)]
fn parse_signal(sig_str: &str) -> Result<i32> {
    let sig_str = sig_str.trim_start_matches('-');

    // Try to parse as number first
    if let Ok(num) = sig_str.parse::<i32>() {
        return Ok(num);
    }

    // Parse signal names
    match sig_str {
        "HUP" | "SIGHUP" => Ok(libc::SIGHUP),
        "INT" | "SIGINT" => Ok(libc::SIGINT),
        "QUIT" | "SIGQUIT" => Ok(libc::SIGQUIT),
        "KILL" | "SIGKILL" => Ok(libc::SIGKILL),
        "TERM" | "SIGTERM" => Ok(libc::SIGTERM),
        "STOP" | "SIGSTOP" => Ok(libc::SIGSTOP),
        "CONT" | "SIGCONT" => Ok(libc::SIGCONT),
        "TSTP" | "SIGTSTP" => Ok(libc::SIGTSTP),
        _ => anyhow::bail!("kill: unknown signal: {}", sig_str),
    }
}

/// Perform hardware-level secure erase on an entire device (SSD/HDD).
///
/// **CRITICAL WARNING:** This operation erases the **ENTIRE DEVICE**, not individual files!
/// All data on the device will be permanently destroyed.
///
/// This operation is **NOT REVERSIBLE** and includes comprehensive safety confirmations.
///
/// # Methods
/// - `ata-secure-erase` - ATA Secure Erase for SATA SSDs (NIST Purge)
/// - `nvme-format` - NVMe Format with crypto erase (NIST Purge, fast)
/// - `nvme-sanitize` - NVMe Sanitize with block erase (NIST Purge, thorough)
/// - `auto` - Auto-detect drive type and use appropriate method (default)
///
/// # Safety Features
/// - System drive detection (ABORTS if system drive)
/// - Mount point checking (offers to unmount)
/// - Device info display (type, size, mounts)
/// - Typed challenge (must type exact device name)
/// - Final yes/no confirmation
///
/// # Arguments
/// * `state` - Mutable shell state for recording the operation
/// * `device` - Device path (e.g., `/dev/sda`, `/dev/nvme0n1`)
/// * `method` - Secure erase method (default: auto)
///
/// # Examples
/// ```no_run
/// use vsh::commands;
/// use vsh::state::ShellState;
///
/// let mut state = ShellState::new("/tmp/test")?;
///
/// // Auto-detect and erase
/// commands::hardware_erase(&mut state, "/dev/sdb", None)?;
///
/// // Specific method
/// commands::hardware_erase(&mut state, "/dev/nvme0n1", Some("nvme-format"))?;
/// # Ok::<(), anyhow::Error>(())
/// ```
pub fn hardware_erase(
    state: &mut ShellState,
    device: &str,
    method: Option<&str>,
) -> Result<()> {
    use crate::confirmation::{confirm_destructive_operation, ConfirmationLevel};
    use crate::secure_erase::{
        ata_secure_erase, check_ata_secure_erase_support, check_nvme_sanitize_support,
        detect_drive_type, nvme_format_crypto, nvme_sanitize, DriveType,
    };

    // Detect drive type
    let drive_type = detect_drive_type(device)
        .context("Failed to detect drive type")?;

    // Determine method
    let erase_method = match (drive_type, method) {
        (DriveType::SataSSD, None) | (DriveType::SataSSD, Some("auto")) => "ata-secure-erase",
        (DriveType::SataSSD, Some("ata-secure-erase")) => "ata-secure-erase",
        (DriveType::NVMeSSD, None) | (DriveType::NVMeSSD, Some("auto")) => "nvme-format",
        (DriveType::NVMeSSD, Some("nvme-format")) => "nvme-format",
        (DriveType::NVMeSSD, Some("nvme-sanitize")) => "nvme-sanitize",
        (DriveType::HDD, _) => {
            anyhow::bail!(
                "Hardware secure erase not supported for HDDs - use file-level obliterate instead"
            );
        }
        (DriveType::Unknown, _) => {
            anyhow::bail!("Unknown drive type - cannot determine secure erase method");
        }
        (_, Some(m)) => {
            anyhow::bail!("Invalid method '{}' for drive type {:?}", m, drive_type);
        }
    };

    // CRITICAL: Get user confirmation with device-level warnings
    let confirmed = confirm_destructive_operation(
        ConfirmationLevel::Device,
        device,
        erase_method,
    )?;

    if !confirmed {
        println!();
        println!("{}", "Operation cancelled by user".yellow());
        return Ok(());
    }

    // Execute the appropriate secure erase method
    match erase_method {
        "ata-secure-erase" => {
            // Check support first
            if !check_ata_secure_erase_support(device)? {
                anyhow::bail!("ATA Secure Erase not supported on this device");
            }

            println!();
            println!("{}", "🔥 Executing ATA Secure Erase...".bright_cyan());
            ata_secure_erase(device, true)?;
            println!();
            println!("{}", "✓ Device securely erased".bright_green().bold());
        }

        "nvme-format" => {
            println!();
            println!("{}", "🔥 Executing NVMe Format (Crypto Erase)...".bright_cyan());
            nvme_format_crypto(device)?;
            println!();
            println!("{}", "✓ Device securely erased".bright_green().bold());
        }

        "nvme-sanitize" => {
            // Check support first
            if !check_nvme_sanitize_support(device)? {
                anyhow::bail!("NVMe Sanitize not supported on this device");
            }

            println!();
            println!("{}", "🔥 Executing NVMe Sanitize (this may take hours)...".bright_cyan());
            nvme_sanitize(device, true)?;
            println!();
            println!("{}", "✓ Device securely erased".bright_green().bold());
        }

        _ => unreachable!(),
    }

    // Record operation (NOT reversible)
    let op = Operation::new(
        OperationType::HardwareErase,
        device.to_string(),
        None, // Not part of a transaction
    );
    let op_id = op.id;
    state.record_operation(op);

    println!(
        "{} {} {} (method: {}, type: {:?})",
        format!("[op:{}]", &op_id.to_string()[..8]).bright_black(),
        "hardware_erase".bright_red().bold(),
        device,
        erase_method,
        drive_type
    );
    println!(
        "    {} {}",
        "Standard:".bright_black(),
        "NIST SP 800-88 Purge".bright_cyan()
    );
    println!(
        "    {} {}",
        "Warning:".bright_black(),
        "IRREVERSIBLE - All data permanently destroyed".bright_red()
    );

    Ok(())
}

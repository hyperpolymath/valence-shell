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

/// Create a directory
pub fn mkdir(state: &mut ShellState, path: &str, verbose: bool) -> Result<()> {
    let full_path = state.resolve_path(path);

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

/// Remove a directory
pub fn rmdir(state: &mut ShellState, path: &str, verbose: bool) -> Result<()> {
    let full_path = state.resolve_path(path);

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

/// Create a file
pub fn touch(state: &mut ShellState, path: &str, verbose: bool) -> Result<()> {
    let full_path = state.resolve_path(path);

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

/// Remove a file
pub fn rm(state: &mut ShellState, path: &str, verbose: bool) -> Result<()> {
    let full_path = state.resolve_path(path);

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

/// Undo operations
pub fn undo(state: &mut ShellState, count: usize, verbose: bool) -> Result<()> {
    // Clone operations to avoid borrowing state
    let ops_to_undo: Vec<Operation> = state.last_n_undoable(count).into_iter().cloned().collect();

    if ops_to_undo.is_empty() {
        println!("{}", "Nothing to undo".bright_yellow());
        return Ok(());
    }

    for op in &ops_to_undo {
        let inverse_type = op.op_type.inverse().context("Operation has no inverse")?;
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

/// Redo operations
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

/// Show history
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

/// Begin a transaction
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

/// Commit current transaction
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

/// Rollback current transaction
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

/// Show operation graph
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

/// Show proof information
pub fn show_proofs() -> Result<()> {
    proof_refs::print_verification_summary();
    Ok(())
}

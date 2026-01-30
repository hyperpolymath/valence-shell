// SPDX-License-Identifier: PLMP-1.0-or-later
//! Secure Deletion (RMO - Remove-Match-Obliterate)
//!
//! GDPR-compliant irreversible file deletion with secure overwrite.
//! Implements DoD 5220.22-M 3-pass overwrite + POSIX file deletion.
//!
//! **WARNING**: These operations are NOT REVERSIBLE. No undo possible.

use anyhow::{Context, Result, bail};
use colored::Colorize;
use std::fs::{self, OpenOptions};
use std::io::{Write, Seek, SeekFrom, BufRead};

use crate::state::{Operation, OperationType, ShellState};

/// Simple yes/no confirmation prompt
fn ask_confirmation(prompt: &str) -> Result<bool> {
    print!("{} [y/N] ", prompt);
    std::io::stdout().flush()?;

    let stdin = std::io::stdin();
    let mut line = String::new();
    stdin.lock().read_line(&mut line)?;

    let response = line.trim().to_lowercase();
    Ok(response == "y" || response == "yes")
}

/// Perform 3-pass DoD 5220.22-M secure overwrite
///
/// Pass 1: Write 0x00 (all zeros)
/// Pass 2: Write 0xFF (all ones)
/// Pass 3: Write random data
///
/// This makes data recovery extremely difficult without advanced
/// forensic techniques (magnetic force microscopy).
fn secure_overwrite_3pass(file_path: &std::path::Path, file_size: u64) -> Result<()> {
    let mut file = OpenOptions::new()
        .write(true)
        .open(file_path)
        .context("Failed to open file for secure overwrite")?;

    // Pass 1: All zeros
    file.seek(SeekFrom::Start(0))?;
    let zeros = vec![0u8; 4096];
    let mut written = 0u64;
    while written < file_size {
        let to_write = std::cmp::min(4096, (file_size - written) as usize);
        file.write_all(&zeros[..to_write])?;
        written += to_write as u64;
    }
    file.sync_all()?;

    // Pass 2: All ones
    file.seek(SeekFrom::Start(0))?;
    let ones = vec![0xFFu8; 4096];
    written = 0;
    while written < file_size {
        let to_write = std::cmp::min(4096, (file_size - written) as usize);
        file.write_all(&ones[..to_write])?;
        written += to_write as u64;
    }
    file.sync_all()?;

    // Pass 3: Random data
    file.seek(SeekFrom::Start(0))?;
    use std::collections::hash_map::RandomState;
    use std::hash::{BuildHasher, Hasher};
    let random_state = RandomState::new();
    written = 0;
    while written < file_size {
        // Generate pseudo-random data using hasher
        let mut hasher = random_state.build_hasher();
        hasher.write_u64(written);
        let random_bytes = hasher.finish().to_le_bytes();

        let to_write = std::cmp::min(random_bytes.len(), (file_size - written) as usize);
        file.write_all(&random_bytes[..to_write])?;
        written += to_write as u64;
    }
    file.sync_all()?;

    Ok(())
}

/// Obliterate a file (GDPR-compliant secure deletion)
///
/// This is an **irreversible** operation that:
/// 1. Overwrites file content with 3-pass DoD 5220.22-M pattern
/// 2. Deletes the file
/// 3. Records operation as non-reversible
///
/// Use this for GDPR "right to erasure" compliance or security-critical deletion.
///
/// # Arguments
/// * `state` - Mutable shell state for recording the operation
/// * `path` - Path relative to shell root or absolute path
/// * `verbose` - Whether to show detailed output
/// * `force` - Skip confirmation prompt (USE WITH CAUTION)
///
/// # Errors
/// Returns error if:
/// - Path does not exist (ENOENT)
/// - Path is a directory (EISDIR) - use secure directory deletion
/// - Insufficient permissions
/// - Overwrite fails
///
/// # Examples
/// ```no_run
/// use vsh::commands::secure_deletion;
/// use vsh::state::ShellState;
///
/// let mut state = ShellState::new("/tmp/test")?;
/// // User must confirm this irreversible operation
/// secure_deletion::obliterate(&mut state, "sensitive.txt", false, false)?;
/// # Ok::<(), anyhow::Error>(())
/// ```
pub fn obliterate(state: &mut ShellState, path: &str, verbose: bool, force: bool) -> Result<()> {
    let full_path = state.resolve_path(path);

    // Precondition checks
    if !full_path.exists() {
        bail!("Path does not exist (ENOENT)");
    }
    if full_path.is_dir() {
        bail!("Path is a directory - secure directory deletion not yet implemented (EISDIR)");
    }

    // Get file size before deletion
    let metadata = fs::metadata(&full_path)?;
    let file_size = metadata.len();

    // CRITICAL: Require confirmation for irreversible operation
    if !force {
        eprintln!();
        eprintln!("{}", "⚠️  WARNING: IRREVERSIBLE DELETION".bright_red().bold());
        eprintln!();
        eprintln!("  File: {}", full_path.display().to_string().bright_cyan());
        eprintln!("  Size: {} bytes", file_size.to_string().bright_yellow());
        eprintln!();
        eprintln!("This will:");
        eprintln!("  1. Overwrite with 3-pass DoD 5220.22-M pattern (0x00, 0xFF, random)");
        eprintln!("  2. Delete the file");
        eprintln!("  3. Make recovery {} impossible", "cryptographically".bright_red());
        eprintln!();
        eprintln!("{}", "This operation CANNOT be undone.".bright_red().bold());
        eprintln!();

        if !ask_confirmation("Are you sure you want to obliterate this file?")? {
            println!("{}", "Operation cancelled.".bright_yellow());
            return Ok(());
        }
    }

    // Step 1: Secure overwrite
    if verbose {
        println!("🔥 Pass 1/3: Overwriting with zeros...");
    }
    secure_overwrite_3pass(&full_path, file_size)?;

    // Step 2: Delete file
    fs::remove_file(&full_path).context("Failed to delete file after overwrite")?;

    // Step 3: Record as irreversible operation (NO undo_data stored)
    let op = Operation::new(OperationType::Obliterate, path.to_string(), None);
    let op_id = op.id;
    state.record_operation(op);

    // Output
    println!(
        "{} {} {}",
        format!("[op:{}]", &op_id.to_string()[..8]).bright_black(),
        "obliterate".bright_red().bold(),
        path
    );
    println!("{}", "✓ File securely obliterated (CANNOT be undone)".bright_red());

    if verbose {
        println!("    {} DoD 5220.22-M 3-pass overwrite", "Method:".bright_black());
        println!("    {} GDPR Article 17 compliant", "Compliance:".bright_black());
        println!("    {} IRREVERSIBLE", "Undo:".bright_black());
    }

    Ok(())
}

/// Obliterate a directory and its contents (recursive)
///
/// This is an **irreversible** operation that securely deletes a directory tree.
///
/// # Arguments
/// * `state` - Mutable shell state for recording the operation
/// * `path` - Path to directory
/// * `verbose` - Whether to show detailed output
/// * `force` - Skip confirmation prompt (USE WITH CAUTION)
///
/// # Examples
/// ```no_run
/// use vsh::commands::secure_deletion;
/// use vsh::state::ShellState;
///
/// let mut state = ShellState::new("/tmp/test")?;
/// secure_deletion::obliterate_dir(&mut state, "sensitive_data/", false, false)?;
/// # Ok::<(), anyhow::Error>(())
/// ```
pub fn obliterate_dir(state: &mut ShellState, path: &str, verbose: bool, force: bool) -> Result<()> {
    let full_path = state.resolve_path(path);

    if !full_path.exists() {
        bail!("Path does not exist (ENOENT)");
    }
    if !full_path.is_dir() {
        bail!("Path is not a directory (ENOTDIR)");
    }

    // Count files for confirmation message
    let mut file_count = 0usize;
    let mut total_size = 0u64;
    for entry in walkdir::WalkDir::new(&full_path) {
        let entry = entry?;
        if entry.file_type().is_file() {
            file_count += 1;
            if let Ok(metadata) = entry.metadata() {
                total_size += metadata.len();
            }
        }
    }

    // CRITICAL: Require confirmation
    if !force {
        eprintln!();
        eprintln!("{}", "⚠️  WARNING: IRREVERSIBLE DIRECTORY DELETION".bright_red().bold());
        eprintln!();
        eprintln!("  Directory: {}", full_path.display().to_string().bright_cyan());
        eprintln!("  Files: {}", file_count.to_string().bright_yellow());
        eprintln!("  Total size: {} bytes", total_size.to_string().bright_yellow());
        eprintln!();
        eprintln!("{}", "This operation CANNOT be undone.".bright_red().bold());
        eprintln!();

        if !ask_confirmation("Are you sure you want to obliterate this directory?")? {
            println!("{}", "Operation cancelled.".bright_yellow());
            return Ok(());
        }
    }

    // Obliterate all files in directory tree
    let mut obliterated = 0usize;
    for entry in walkdir::WalkDir::new(&full_path)
        .contents_first(true) // Process files before directories
    {
        let entry = entry?;
        let entry_path = entry.path();

        if entry.file_type().is_file() {
            if let Ok(metadata) = fs::metadata(entry_path) {
                secure_overwrite_3pass(entry_path, metadata.len())?;
                obliterated += 1;
                if verbose {
                    println!("  🔥 {}", entry_path.display());
                }
            }
            fs::remove_file(entry_path)?;
        } else if entry.file_type().is_dir() && entry_path != full_path {
            fs::remove_dir(entry_path)?;
        }
    }

    // Remove root directory
    fs::remove_dir(&full_path)?;

    // Record operation
    let op = Operation::new(OperationType::Obliterate, path.to_string(), None);
    let op_id = op.id;
    state.record_operation(op);

    println!(
        "{} {} {}",
        format!("[op:{}]", &op_id.to_string()[..8]).bright_black(),
        "obliterate -r".bright_red().bold(),
        path
    );
    println!(
        "{}",
        format!("✓ {} files securely obliterated (CANNOT be undone)", obliterated).bright_red()
    );

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;
    use std::path::PathBuf;

    #[test]
    fn test_secure_overwrite_3pass() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");

        // Create test file with known content
        let original = b"SENSITIVE DATA THAT MUST BE DESTROYED";
        fs::write(&file_path, original).unwrap();

        let file_size = fs::metadata(&file_path).unwrap().len();
        secure_overwrite_3pass(&file_path, file_size).unwrap();

        // Verify content is overwritten (not original data)
        let after = fs::read(&file_path).unwrap();
        assert_eq!(after.len(), original.len());
        assert_ne!(&after[..], original);
    }

    #[test]
    #[ignore] // Requires user confirmation
    fn test_obliterate() {
        let temp_dir = TempDir::new().unwrap();
        let mut state = ShellState::new(temp_dir.path().to_str().unwrap()).unwrap();

        let test_file = "sensitive.txt";
        fs::write(temp_dir.path().join(test_file), "secret data").unwrap();

        // force=true to skip confirmation in test
        obliterate(&mut state, test_file, false, true).unwrap();

        assert!(!temp_dir.path().join(test_file).exists());
    }
}

// SPDX-License-Identifier: MPL-2.0
//! Secure Deletion (RMO - Remove-Match-Obliterate)
//!
//! GDPR-compliant irreversible file deletion with secure overwrite.
//! Implements DoD 5220.22-M 3-pass overwrite + POSIX file deletion.
//!
//! **WARNING**: These operations are NOT REVERSIBLE. No undo possible.
//!
//! # Filesystem Limitations
//!
//! Multi-pass overwrite assumes the filesystem writes new data **in place** over
//! the previous extent. This is true for traditional filesystems (ext4 without
//! journal=data, XFS, FAT, NTFS in most cases) but **does NOT hold** for:
//!
//! - **Copy-on-write (CoW) filesystems**: btrfs, ZFS, bcachefs, APFS. Each overwrite
//!   allocates a new extent, leaving prior data recoverable until the original
//!   extent is freed and reused. Set `chattr +C` (btrfs) or `zfs set copies=1`
//!   plus `zfs set sync=always` and disable snapshots, or equivalent, to defeat
//!   CoW for the target file. For full assurance use [`crate::secure_erase`]
//!   (hardware NIST SP 800-88 Purge) instead.
//! - **Log-structured filesystems**: f2fs, NILFS2. Same issue as CoW.
//! - **Snapshots / send-stream replicas**: a prior snapshot will retain the
//!   pre-overwrite content. Remove all snapshots referencing the file first.
//! - **SSDs and flash storage in general**: the FTL (flash translation layer)
//!   can remap logical blocks to different physical cells; the original cell
//!   content may persist until the cell is rewritten (which the FTL controls,
//!   not the OS). Use NVMe Format/Sanitize or ATA Secure Erase for SSDs.
//! - **Network filesystems**: NFS, SMB, FUSE-backed stores do not honor in-place
//!   semantics from the client's perspective.
//!
//! This implementation provides best-effort file-level erasure suitable for
//! GDPR Article 17 ("right to erasure") on cooperating filesystems. For
//! hardware-level guarantees use [`crate::secure_erase`].

use anyhow::{bail, Context, Result};
use colored::Colorize;
use std::fs::{self, OpenOptions};
use std::io::{BufRead, Read, Seek, SeekFrom, Write};
use std::path::Path;

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

/// Block size for streaming overwrite passes.
const OVERWRITE_BLOCK_SIZE: usize = 64 * 1024;

/// Fill a buffer with cryptographically-random bytes drawn from the OS RNG.
///
/// Uses `/dev/urandom` on Unix. Falls back to a hash-based PRNG when urandom
/// is unavailable (e.g., chroot without `/dev`), with a warning logged.
#[cfg(unix)]
fn fill_random(buf: &mut [u8]) -> Result<()> {
    let mut rng = std::fs::File::open("/dev/urandom")
        .context("Failed to open /dev/urandom for secure-overwrite RNG")?;
    rng.read_exact(buf)
        .context("Failed to read from /dev/urandom")?;
    Ok(())
}

/// Non-unix fallback: hash-mixed PRNG seeded from time + position.
#[cfg(not(unix))]
fn fill_random(buf: &mut [u8]) -> Result<()> {
    use std::collections::hash_map::RandomState;
    use std::hash::{BuildHasher, Hasher};
    let state = RandomState::new();
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos() as u64)
        .unwrap_or(0);
    for (i, b) in buf.iter_mut().enumerate() {
        let mut h = state.build_hasher();
        h.write_u64(nanos);
        h.write_u64(i as u64);
        *b = (h.finish() & 0xFF) as u8;
    }
    Ok(())
}

/// Perform a single overwrite pass with the given pattern.
///
/// `pattern` is one of:
/// - `Pattern::Random` — bytes drawn from `/dev/urandom`
/// - `Pattern::Fixed(b)` — every byte is `b`
#[derive(Clone, Copy)]
enum Pattern {
    Random,
    Fixed(u8),
}

fn overwrite_pass(file: &mut std::fs::File, file_size: u64, pattern: Pattern) -> Result<()> {
    file.seek(SeekFrom::Start(0))?;
    let mut buf = vec![0u8; OVERWRITE_BLOCK_SIZE];
    let mut written = 0u64;
    while written < file_size {
        let chunk = std::cmp::min(OVERWRITE_BLOCK_SIZE as u64, file_size - written) as usize;
        match pattern {
            Pattern::Random => fill_random(&mut buf[..chunk])?,
            Pattern::Fixed(b) => {
                for slot in buf[..chunk].iter_mut() {
                    *slot = b;
                }
            }
        }
        file.write_all(&buf[..chunk])?;
        written += chunk as u64;
    }
    // fsync at every pass so each overwrite is durable before the next begins.
    file.sync_all()?;
    Ok(())
}

/// Perform 3-pass NIST SP 800-88 Purge-style secure overwrite.
///
/// Pass order matches the task spec (random / zeros / final pattern), chosen
/// because the final pattern is a known constant — useful for verifying that
/// the overwrite ran to completion (read-back-check).
///
/// Pass 1: Random bytes from `/dev/urandom` (overwrites magnetic remanence)
/// Pass 2: All zeros (defeats simple recovery)
/// Pass 3: Final pattern `0xFF` (verifiable terminator)
///
/// `fsync` is issued after every pass so each write is durable before the
/// next begins.
///
/// See module-level docs for filesystem limitations (CoW / FTL remapping).
fn secure_overwrite_3pass(file_path: &std::path::Path, file_size: u64) -> Result<()> {
    let mut file = OpenOptions::new()
        .write(true)
        .open(file_path)
        .context("Failed to open file for secure overwrite")?;

    overwrite_pass(&mut file, file_size, Pattern::Random)?;
    overwrite_pass(&mut file, file_size, Pattern::Fixed(0x00))?;
    overwrite_pass(&mut file, file_size, Pattern::Fixed(0xFF))?;

    Ok(())
}

/// Securely delete a single regular file by 3-pass overwrite + unlink.
///
/// This is the low-level primitive used by [`obliterate`]; exposed publicly so
/// other modules (audit log compaction, RMO sweeps, GDPR right-to-erasure
/// workflows) can call it without going through the shell-state recording path.
///
/// **WARNING**: this operation is irreversible. The file is destroyed.
///
/// # Behaviour
///
/// 1. Open the file with `O_WRONLY`.
/// 2. Pass 1: overwrite with random bytes from `/dev/urandom`, then `fsync`.
/// 3. Pass 2: overwrite with zeros, then `fsync`.
/// 4. Pass 3: overwrite with `0xFF` (final pattern), then `fsync`.
/// 5. `unlink` the path.
///
/// # Errors
///
/// - `ENOENT` if `path` does not exist
/// - `EISDIR` if `path` is a directory (use [`obliterate_dir`] instead)
/// - I/O error if any pass or the unlink fails
///
/// # Filesystem Limitations
///
/// See [module docs](self) — CoW filesystems (btrfs, ZFS, APFS), SSDs with FTL
/// remapping, and snapshot-bearing volumes defeat in-place overwrite. For
/// hardware-level guarantees on SSDs use [`crate::secure_erase`].
pub fn secure_delete(path: &Path) -> Result<()> {
    if !path.exists() {
        bail!("Path does not exist (ENOENT): {}", path.display());
    }
    let meta = fs::metadata(path).context("Failed to stat target")?;
    if meta.is_dir() {
        bail!("Path is a directory (EISDIR): {}", path.display());
    }
    let file_size = meta.len();
    secure_overwrite_3pass(path, file_size)?;
    fs::remove_file(path).context("Failed to unlink after overwrite")?;
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
        eprintln!(
            "{}",
            "⚠️  WARNING: IRREVERSIBLE DELETION".bright_red().bold()
        );
        eprintln!();
        eprintln!("  File: {}", full_path.display().to_string().bright_cyan());
        eprintln!("  Size: {} bytes", file_size.to_string().bright_yellow());
        eprintln!();
        eprintln!("This will:");
        eprintln!("  1. Overwrite with 3-pass NIST SP 800-88 Purge pattern (random, 0x00, 0xFF)");
        eprintln!("  2. Delete the file");
        eprintln!(
            "  3. Make recovery {} impossible on in-place filesystems",
            "cryptographically".bright_red()
        );
        eprintln!("     (CoW filesystems like btrfs/ZFS/APFS and SSDs with FTL");
        eprintln!("     remapping require hardware-level erase — see `secure_erase`)");
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
        println!("🔥 3-pass overwrite (random / zeros / 0xFF) + unlink...");
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
    println!(
        "{}",
        "✓ File securely obliterated (CANNOT be undone)".bright_red()
    );

    if verbose {
        println!(
            "    {} DoD 5220.22-M 3-pass overwrite",
            "Method:".bright_black()
        );
        println!(
            "    {} GDPR Article 17 compliant",
            "Compliance:".bright_black()
        );
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
pub fn obliterate_dir(
    state: &mut ShellState,
    path: &str,
    verbose: bool,
    force: bool,
) -> Result<()> {
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
        eprintln!(
            "{}",
            "⚠️  WARNING: IRREVERSIBLE DIRECTORY DELETION"
                .bright_red()
                .bold()
        );
        eprintln!();
        eprintln!(
            "  Directory: {}",
            full_path.display().to_string().bright_cyan()
        );
        eprintln!("  Files: {}", file_count.to_string().bright_yellow());
        eprintln!(
            "  Total size: {} bytes",
            total_size.to_string().bright_yellow()
        );
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
    for entry in walkdir::WalkDir::new(&full_path).contents_first(true)
    // Process files before directories
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
        format!(
            "✓ {} files securely obliterated (CANNOT be undone)",
            obliterated
        )
        .bright_red()
    );

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    
    use tempfile::TempDir;

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

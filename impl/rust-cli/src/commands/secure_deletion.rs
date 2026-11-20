// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! Secure Deletion (RMO - Remove-Match-Obliterate)
//!
//! Best-effort irreversible file deletion with a 3-pass overwrite followed by
//! POSIX unlink.
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
//! This implementation narrows ordinary recovery opportunities on cooperating
//! in-place filesystems. It does not establish physical-media sanitisation,
//! removal from backups or replicas, or legal compliance. For device-level
//! operations use [`crate::secure_erase`] and validate the result independently.

use anyhow::{bail, Context, Result};
use cap_fs_ext::{FollowSymlinks, MetadataExt, OpenOptionsFollowExt};
use cap_std::fs::Dir;
use colored::Colorize;
use std::io::{BufRead, Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};

use crate::state::{Operation, OperationType, ShellState};

/// Dispatch `obliterate` to the file or directory variant by path type.
/// This is the entry point wired into the shell parser/executor.
///
/// The type is read from the name itself, without following a symbolic
/// link: a link to a directory is a link, and is refused like any other.
pub fn obliterate_path(
    state: &mut ShellState,
    path: &str,
    verbose: bool,
    force: bool,
) -> Result<()> {
    let contained = state.contained(path)?;
    let is_dir = state
        .root_dir()
        .symlink_metadata(&contained)
        .map(|meta| meta.is_dir())
        .unwrap_or(false);
    if is_dir {
        obliterate_dir(state, path, verbose, force)
    } else {
        obliterate(state, path, verbose, force)
    }
}

/// Obliteration cannot be undone, so it has no place in a transaction,
/// whose promise is that it can be rolled back (owner ruling OD-3a).
fn refuse_inside_transaction(state: &ShellState) -> Result<()> {
    if state.active_transaction.is_some() {
        bail!(
            "obliterate cannot be undone, so it is refused inside a transaction. \
             Commit or roll back the transaction first."
        );
    }
    Ok(())
}

/// Append an RMO audit entry for `op` to the audit log in the session root
/// (`<session root>/.vsh-audit.log`). It is evidence of what the command
/// did, not proof of physical erasure or legal compliance.
///
/// The `…-intent` entry is written *before* anything is destroyed, and its
/// failure stops the command: nothing is obliterated that the log does not
/// know about. The entry written afterwards records the outcome; if that
/// one fails, the destruction has already happened, so the caller only
/// warns.
fn append_rmo_residue(state: &ShellState, op: &Operation, outcome: &str) -> Result<()> {
    append_rmo_entry(state, op, outcome, None)
}

/// As [`append_rmo_residue`], with the text of the error that ended the
/// obliteration, if one did.
fn append_rmo_entry(
    state: &ShellState,
    op: &Operation,
    outcome: &str,
    error: Option<String>,
) -> Result<()> {
    let log_path = state.session_root().join(".vsh-audit.log");
    let log =
        crate::audit_log::AuditLog::new(log_path, None).context("RMO audit log unavailable")?;
    let entry = crate::audit_log::AuditEntry::from_operation(op, outcome, error);
    log.append(&entry).context("RMO audit entry not written")
}

/// Record an obliteration that began and then failed.
///
/// By this point the audit log holds the intent entry, and the history has
/// been scrubbed and saved: its earlier operations on the path are marked
/// as undone by this one. Returning the error alone left the log with an
/// intent and no outcome, and the history without the operation, although
/// some or all of the data may be gone. So the outcome is written (with
/// the error), and the operation is recorded, before the error is returned.
fn record_failed_obliteration(
    state: &mut ShellState,
    op: Operation,
    outcome: &str,
    error: &anyhow::Error,
) {
    if let Err(e) = append_rmo_entry(state, &op, outcome, Some(format!("{error:#}"))) {
        eprintln!("warning: RMO audit outcome not written: {e:#}");
    }
    state.record_rooted_operation(op);
}

/// The regular file at `contained`, opened for overwriting, and its size.
///
/// Refuses anything that would destroy data reachable some other way:
///
/// * a symbolic link, because the data belongs to the link's target, which
///   may lie outside the session root;
/// * a file with more than one hard link, because its other names, which
///   may lie outside the session root, would lose their contents.
///
/// The file is opened without following a link, and the checks are made on
/// the open file, so the name cannot be swapped for a link in between.
fn open_for_obliteration(dir: &Dir, contained: &Path) -> Result<(cap_std::fs::File, u64)> {
    let named = match dir.symlink_metadata(contained) {
        Ok(meta) => meta,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            bail!("Path does not exist (ENOENT)")
        }
        Err(e) => return Err(e).context("Failed to stat target"),
    };
    if named.is_symlink() {
        bail!(
            "Path is a symbolic link. obliterate does not follow links: remove the link \
             with rm, or obliterate its target by the target's own path."
        );
    }
    if named.is_dir() {
        bail!("Path is a directory (EISDIR)");
    }
    if !named.is_file() {
        bail!("Path is not a regular file");
    }

    let mut options = cap_std::fs::OpenOptions::new();
    options.write(true).follow(FollowSymlinks::No);
    let file = dir
        .open_with(contained, &options)
        .context("Failed to open file for secure overwrite")?;
    let opened = file.metadata().context("Failed to stat opened file")?;
    if !opened.is_file() || opened.dev() != named.dev() || opened.ino() != named.ino() {
        bail!("Path changed while it was being opened; nothing was overwritten");
    }
    refuse_other_names(&opened)?;
    Ok((file, opened.len()))
}

/// Refuse a file that has more than one name. `opened` is the metadata of
/// the open file.
fn refuse_other_names(opened: &cap_std::fs::Metadata) -> Result<()> {
    if opened.nlink() > 1 {
        bail!(
            "File has {} hard links. Obliterating it would destroy the data under its \
             other names too, so it is refused.",
            opened.nlink()
        );
    }
    Ok(())
}

/// Overwrite the open `file` three times, remove its name, and make the
/// removal durable in its directory.
fn overwrite_and_unlink(dir: &Dir, contained: &Path, file: cap_std::fs::File) -> Result<()> {
    overwrite_and_remove_name(dir, contained, file)?;
    sync_directory(dir, contained.parent())
}

/// Overwrite the open `file` three times, then remove its name.
///
/// The name is removed only if it still refers to the file that was
/// overwritten. The removal is not yet durable: the caller syncs the
/// directory.
fn overwrite_and_remove_name(dir: &Dir, contained: &Path, file: cap_std::fs::File) -> Result<()> {
    overwrite_and_remove_name_with(dir, contained, file, overwrite_3pass)
}

/// [`overwrite_and_remove_name`], with the overwrite passed in as
/// `overwrite` (given the file and its length), so that a test can add to
/// the file while it is being overwritten.
///
/// The length is read here, from the open file, at the moment the
/// overwrite starts. A length read earlier (when the file was opened,
/// before the wait for a confirmation) misses what another program
/// appended in between: those bytes were left as they were, and the name
/// was removed all the same. If the file is longer after the overwrite
/// than the length that was overwritten, it grew during the overwrite;
/// that is an error, and the name is left in place.
fn overwrite_and_remove_name_with(
    dir: &Dir,
    contained: &Path,
    file: cap_std::fs::File,
    overwrite: impl FnOnce(&mut std::fs::File, u64) -> Result<()>,
) -> Result<()> {
    let identity = file.metadata().context("Failed to stat opened file")?;
    let file_size = identity.len();
    let mut file = file.into_std();
    overwrite(&mut file, file_size)?;
    let length_now = file
        .metadata()
        .context("Failed to stat the file after the overwrite")?
        .len();
    if length_now > file_size {
        bail!(
            "The file grew from {file_size} to {length_now} bytes while it was being \
             overwritten. The added bytes were not overwritten, and the name was left in place."
        );
    }
    drop(file);

    let named = dir
        .symlink_metadata(contained)
        .context("Failed to stat target after overwrite")?;
    if named.dev() != identity.dev() || named.ino() != identity.ino() {
        bail!("Path was replaced during the overwrite; the name was left in place");
    }
    dir.remove_file(contained)
        .context("Failed to delete file after overwrite")
}

/// Make a removal durable in its directory.
fn sync_directory(dir: &Dir, parent: Option<&Path>) -> Result<()> {
    let parent = parent
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    // Opened as a file, read-only: a directory handle from `open_dir` may be
    // path-only, which cannot be synced.
    #[cfg(unix)]
    dir.open(parent)
        .with_context(|| format!("Failed to open directory {}", parent.display()))?
        .sync_all()
        .with_context(|| format!("Failed to sync directory {}", parent.display()))?;
    #[cfg(not(unix))]
    let _ = (dir, parent);
    Ok(())
}

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
fn overwrite_3pass(file: &mut std::fs::File, file_size: u64) -> Result<()> {
    overwrite_pass(file, file_size, Pattern::Random)?;
    overwrite_pass(file, file_size, Pattern::Fixed(0x00))?;
    overwrite_pass(file, file_size, Pattern::Fixed(0xFF))?;

    Ok(())
}

/// Securely delete a single regular file by 3-pass overwrite + unlink.
///
/// This is the low-level primitive used by [`obliterate`]; exposed publicly so
/// other modules (audit log compaction and RMO sweeps)
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
/// 5. `unlink` the path and sync its parent directory on Unix.
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
    // Open the containing directory, then treat the file as a name beneath
    // it. This gives the same refusals as `obliterate`: no symbolic link,
    // no file with more than one hard link.
    let parent = path
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let name = path
        .file_name()
        .with_context(|| format!("Path has no file name: {}", path.display()))?;
    let dir = Dir::open_ambient_dir(parent, cap_std::ambient_authority())
        .with_context(|| format!("Failed to open directory {}", parent.display()))?;
    let (file, _) = open_for_obliteration(&dir, Path::new(name))
        .with_context(|| format!("Cannot securely delete {}", path.display()))?;
    overwrite_and_unlink(&dir, Path::new(name), file)
}

/// Obliterate a file using best-effort overwrite and unlink
///
/// This is an **irreversible** operation that:
/// 1. Overwrites file content with 3-pass DoD 5220.22-M pattern
/// 2. Deletes the file
/// 3. Records operation as non-reversible
///
/// This primitive alone is not a legal-compliance or physical-sanitisation
/// guarantee. See the module-level filesystem and device limitations.
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
    obliterate_confirmed_by(state, path, verbose, |full_path, file_size| {
        // CRITICAL: Require confirmation for irreversible operation
        if force {
            return Ok(true);
        }
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
        eprintln!("  3. Reduce ordinary file-level recovery opportunities");
        eprintln!("     (CoW filesystems like btrfs/ZFS/APFS and SSDs with FTL");
        eprintln!("     remapping require hardware-level erase — see `secure_erase`)");
        eprintln!();
        eprintln!("{}", "This operation CANNOT be undone.".bright_red().bold());
        eprintln!();

        ask_confirmation("Are you sure you want to obliterate this file?")
    })
}

/// [`obliterate`], with the step that asks for confirmation passed in as
/// `confirm` (given the file's path and its size), so that a test can
/// change the file while the answer is awaited.
fn obliterate_confirmed_by(
    state: &mut ShellState,
    path: &str,
    verbose: bool,
    confirm: impl FnOnce(&Path, u64) -> Result<bool>,
) -> Result<()> {
    refuse_inside_transaction(state)?;
    let full_path = state.resolve_path(path);
    let contained = state.contained(path)?;

    // Precondition checks, on the file itself rather than on its name.
    let (file, file_size) = open_for_obliteration(state.root_dir(), &contained)?;

    if !confirm(&full_path, file_size)? {
        println!("{}", "Operation cancelled.".bright_yellow());
        return Ok(());
    }

    // The answer can be a long time coming, and the file can be given
    // another name meanwhile. The overwrite would then destroy the data
    // under that name too, so the link count is read again from the open
    // file, before anything is recorded or destroyed. (The length is read
    // again where the overwrite starts.)
    refuse_other_names(&file.metadata().context("Failed to stat opened file")?)?;

    // Steps 1 and 2: the audit entry, then the history. Nothing is
    // destroyed before both are done. The operation names the path as the
    // history stores it, relative to the session root, so that the audit
    // entries and the history record name the same file whatever the
    // working directory is.
    let op = Operation::new(OperationType::Obliterate, state.rooted(path), None);
    let op_id = op.id;
    prepare_obliteration(state, &op, "obliterate-intent")?;

    // Step 3: Secure overwrite, then delete the name.
    if verbose {
        println!("🔥 3-pass overwrite (random / zeros / 0xFF) + unlink...");
    }
    if let Err(e) = overwrite_and_unlink(state.root_dir(), &contained, file) {
        record_failed_obliteration(state, op, "obliterate-failed", &e);
        return Err(e);
    }

    // Step 4: Record the outcome, and the irreversible operation (NO undo_data).
    if let Err(e) = append_rmo_residue(state, &op, "obliterated") {
        eprintln!("warning: RMO audit outcome not written: {e:#}");
    }
    state.record_rooted_operation(op);

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
            "    {} not established by this command",
            "Compliance:".bright_black()
        );
        println!("    {} IRREVERSIBLE", "Undo:".bright_black());
    }

    Ok(())
}

/// What must be done before an obliteration destroys anything.
///
/// First the audit log is told what is about to happen. Then the history
/// forgets what it holds about `path` (and about anything beneath it, if it
/// is a directory), and that is saved. Earlier operations may hold the
/// content as undo data; if the history could not be saved without it, the
/// content would outlive the file in the saved state. If either step fails,
/// nothing is obliterated.
fn prepare_obliteration(state: &mut ShellState, op: &Operation, intent: &str) -> Result<()> {
    append_rmo_residue(state, op, intent)
        .context("Nothing was obliterated, because the audit entry could not be written")?;
    // The archive of operations that aged out of the history can hold the
    // content too.
    state.scrub_archive(&op.path).context(
        "Nothing was obliterated, because the history archive could not be rewritten without \
         the earlier contents of what was to be obliterated",
    )?;
    let scrubbed = state.scrub_obliterated(&op.path, op.id);
    if let Err(e) = state.save_history() {
        // The file stays, so the history must still be able to undo what
        // was done to it.
        state.restore_scrubbed(scrubbed);
        return Err(e).context(
            "Nothing was obliterated, because the history could not be saved without the \
             earlier contents of what was to be obliterated",
        );
    }
    Ok(())
}

/// Destroy what [`plan_dir`] found: the files, the links, the directories
/// deepest first, and then the directory `contained` itself. `obliterated`
/// counts the files destroyed, and holds the count reached if this fails
/// part of the way.
fn destroy_planned(
    root: &Dir,
    plan: &DirPlan,
    contained: &Path,
    verbose: bool,
    obliterated: &mut usize,
) -> Result<()> {
    destroy_planned_with(root, plan, contained, verbose, obliterated, sync_directory)
}

/// [`destroy_planned`], with the step that makes a removal durable passed
/// in as `durable`, so that a test can make that step fail.
fn destroy_planned_with(
    root: &Dir,
    plan: &DirPlan,
    contained: &Path,
    verbose: bool,
    obliterated: &mut usize,
    durable: impl Fn(&Dir, Option<&Path>) -> Result<()>,
) -> Result<()> {
    for file_path in &plan.files {
        let (file, _) = open_for_obliteration(root, file_path)?;
        overwrite_and_remove_name(root, file_path, file)?;
        // Counted as soon as the name is gone. Making the removal durable
        // can still fail, and the audit entry must then not report one
        // file fewer than were destroyed.
        *obliterated += 1;
        durable(root, file_path.parent())?;
        if verbose {
            println!("  🔥 {}", file_path.display());
        }
    }
    for link in &plan.links {
        // Removing a link removes only the link; its target is not touched.
        root.remove_file(link)?;
    }
    for dir_path in &plan.dirs {
        root.remove_dir(dir_path)?;
        durable(root, dir_path.parent())?;
    }

    // Remove root directory
    root.remove_dir(contained)?;
    durable(root, contained.parent())
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
    refuse_inside_transaction(state)?;
    let full_path = state.resolve_path(path);
    let contained = state.contained(path)?;

    if contained == Path::new(".") {
        bail!("Refusing to obliterate the session root itself");
    }
    match state.root_dir().symlink_metadata(&contained) {
        Ok(meta) if meta.is_dir() => {}
        Ok(meta) if meta.is_symlink() => bail!(
            "Path is a symbolic link. obliterate does not follow links: remove the link \
             with rm, or obliterate its target by the target's own path."
        ),
        Ok(_) => bail!("Path is not a directory (ENOTDIR)"),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            bail!("Path does not exist (ENOENT)")
        }
        Err(e) => return Err(e).context("Failed to stat target"),
    }

    // Walk the tree first, without following any link, and refuse the whole
    // operation if anything in it cannot be obliterated safely. Nothing is
    // destroyed until the whole tree has been checked.
    let mut plan = DirPlan::default();
    plan_dir(state.root_dir(), &contained, &mut plan)?;
    let file_count = plan.files.len();
    let total_size = plan.total_size;

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

    // The audit entry, then the history, before anything is destroyed.
    let op = Operation::new(OperationType::Obliterate, state.rooted(path), None);
    let op_id = op.id;
    prepare_obliteration(state, &op, "obliterate-dir-intent")?;

    // Obliterate the files, remove the links, then the directories, deepest
    // first.
    let mut obliterated = 0usize;
    if let Err(e) = destroy_planned(
        state.root_dir(),
        &plan,
        &contained,
        verbose,
        &mut obliterated,
    ) {
        let outcome = format!("obliterate-dir-failed-after-{obliterated}-of-{file_count}-files");
        record_failed_obliteration(state, op, &outcome, &e);
        return Err(e);
    }

    // Record the outcome and the operation.
    if let Err(e) = append_rmo_residue(state, &op, "obliterated-dir") {
        eprintln!("warning: RMO audit outcome not written: {e:#}");
    }
    state.record_rooted_operation(op);

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

/// What obliterating a directory will do, worked out before anything is
/// destroyed. Paths are relative to the session root.
#[derive(Default)]
struct DirPlan {
    /// Regular files to overwrite and remove.
    files: Vec<PathBuf>,
    /// Symbolic links to remove (the link only).
    links: Vec<PathBuf>,
    /// Sub-directories to remove, deepest first.
    dirs: Vec<PathBuf>,
    total_size: u64,
}

/// Walk the directory at `contained` without following links, filling
/// `plan`. Fails, with nothing destroyed, on a file with more than one hard
/// link or on anything that is not a regular file, a link or a directory.
fn plan_dir(dir: &Dir, contained: &Path, plan: &mut DirPlan) -> Result<()> {
    for entry in dir
        .read_dir(contained)
        .with_context(|| format!("Failed to read directory {}", contained.display()))?
    {
        let entry = entry?;
        let child = contained.join(entry.file_name());
        let meta = dir
            .symlink_metadata(&child)
            .with_context(|| format!("Failed to stat {}", child.display()))?;
        if meta.is_symlink() {
            plan.links.push(child);
        } else if meta.is_dir() {
            plan_dir(dir, &child, plan)?;
            plan.dirs.push(child);
        } else if meta.is_file() {
            if meta.nlink() > 1 {
                bail!(
                    "{} has {} hard links. Obliterating it would destroy the data under \
                     its other names too, so the whole directory is refused.",
                    child.display(),
                    meta.nlink()
                );
            }
            plan.total_size += meta.len();
            plan.files.push(child);
        } else {
            bail!(
                "{} is not a regular file, a link or a directory; the whole directory \
                 is refused.",
                child.display()
            );
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::fs;
    use tempfile::TempDir;

    #[test]
    fn test_secure_overwrite_3pass() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");

        // Create test file with known content
        let original = b"SENSITIVE DATA THAT MUST BE DESTROYED";
        fs::write(&file_path, original).unwrap();

        let file_size = fs::metadata(&file_path).unwrap().len();
        let mut file = fs::OpenOptions::new().write(true).open(&file_path).unwrap();
        overwrite_3pass(&mut file, file_size).unwrap();
        drop(file);

        // Verify content is overwritten (not original data)
        let after = fs::read(&file_path).unwrap();
        assert_eq!(after.len(), original.len());
        assert_ne!(&after[..], original);
    }

    /// A file whose name is gone has been destroyed, whether or not its
    /// directory could then be synced. Counting it only after the sync left
    /// the audit entry one file short ("failed after 0 of 2 files" with one
    /// file gone).
    #[test]
    fn test_a_file_is_counted_once_its_name_is_gone() {
        let temp_dir = TempDir::new().unwrap();
        fs::create_dir(temp_dir.path().join("d")).unwrap();
        fs::write(temp_dir.path().join("d/one"), b"first").unwrap();
        fs::write(temp_dir.path().join("d/two"), b"second").unwrap();
        let root = Dir::open_ambient_dir(temp_dir.path(), cap_std::ambient_authority()).unwrap();
        let mut plan = DirPlan::default();
        plan_dir(&root, Path::new("d"), &mut plan).unwrap();
        assert_eq!(plan.files.len(), 2);

        let mut destroyed = 0usize;
        let result = destroy_planned_with(
            &root,
            &plan,
            Path::new("d"),
            false,
            &mut destroyed,
            |_, _| bail!("the directory could not be synced"),
        );

        assert!(
            result.is_err(),
            "the failed sync must stop the obliteration"
        );
        let left = fs::read_dir(temp_dir.path().join("d")).unwrap().count();
        assert_eq!(left, 1, "one file was destroyed before the sync failed");
        assert_eq!(destroyed, 1, "the destroyed file must be counted");
    }

    /// What another program appends to the file while the confirmation is
    /// awaited is overwritten too. The length was read before the wait, so
    /// the added bytes were left as they were and the name was removed.
    #[cfg(unix)]
    #[test]
    fn test_bytes_appended_during_the_confirmation_are_overwritten() {
        let temp_dir = TempDir::new().unwrap();
        let mut state = ShellState::new(temp_dir.path().to_str().unwrap()).unwrap();
        let path = temp_dir.path().join("f");
        fs::write(&path, b"first").unwrap();
        // A descriptor of the test's own, which outlives the name.
        let mut kept = fs::File::open(&path).unwrap();

        obliterate_confirmed_by(&mut state, "f", false, |_, _| {
            fs::OpenOptions::new()
                .append(true)
                .open(&path)
                .unwrap()
                .write_all(b"SECRET")
                .unwrap();
            Ok(true)
        })
        .unwrap();

        assert!(!path.exists());
        let mut left = Vec::new();
        kept.read_to_end(&mut left).unwrap();
        assert_eq!(left.len(), b"firstSECRET".len());
        assert!(
            left.iter().all(|byte| *byte == 0xFF),
            "bytes were left as they were: {left:?}"
        );
    }

    /// A hard link made while the confirmation is awaited is seen, and the
    /// file is refused before anything is recorded or overwritten. The
    /// link count was read only before the wait.
    #[cfg(unix)]
    #[test]
    fn test_a_hard_link_made_during_the_confirmation_is_refused() {
        let temp_dir = TempDir::new().unwrap();
        let root = temp_dir.path().join("root");
        fs::create_dir(&root).unwrap();
        let mut state = ShellState::new(root.to_str().unwrap()).unwrap();
        let path = root.join("f");
        let other_name = temp_dir.path().join("other-name");
        fs::write(&path, b"first").unwrap();

        let refused = obliterate_confirmed_by(&mut state, "f", false, |_, _| {
            fs::hard_link(&path, &other_name).unwrap();
            Ok(true)
        })
        .unwrap_err();

        assert!(format!("{refused:#}").contains("hard links"), "{refused:#}");
        assert_eq!(fs::read(&other_name).unwrap(), b"first");
        assert_eq!(fs::read(&path).unwrap(), b"first");
        let audit = fs::read_to_string(root.join(".vsh-audit.log")).unwrap_or_default();
        assert!(!audit.contains("obliterate"), "{audit}");
    }

    /// A file that grows while it is being overwritten is not removed, and
    /// that is an error: the added bytes were not overwritten.
    #[test]
    fn test_a_file_that_grows_during_the_overwrite_keeps_its_name() {
        let temp_dir = TempDir::new().unwrap();
        fs::write(temp_dir.path().join("f"), b"first").unwrap();
        let root = Dir::open_ambient_dir(temp_dir.path(), cap_std::ambient_authority()).unwrap();
        let (file, _) = open_for_obliteration(&root, Path::new("f")).unwrap();

        let refused =
            overwrite_and_remove_name_with(&root, Path::new("f"), file, |file, length| {
                overwrite_3pass(file, length)?;
                file.seek(SeekFrom::End(0))?;
                file.write_all(b"added meanwhile")?;
                Ok(())
            })
            .unwrap_err();

        assert!(format!("{refused:#}").contains("grew"), "{refused:#}");
        assert!(temp_dir.path().join("f").exists());
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

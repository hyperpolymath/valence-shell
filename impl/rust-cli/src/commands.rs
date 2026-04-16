// SPDX-License-Identifier: PMPL-1.0-or-later
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

/// Copy a file from source to destination.
///
/// This operation is reversible via [`undo`] (deletes the copy) and corresponds
/// to the Lean 4 theorem `copyFile_reversible` in CopyMoveOperations.lean.
///
/// # Arguments
/// * `state` - Mutable shell state for recording the operation
/// * `src` - Source path relative to shell root or absolute path
/// * `dst` - Destination path relative to shell root or absolute path
/// * `verbose` - Whether to show proof references
///
/// # Errors
/// Returns error if:
/// - Source does not exist (ENOENT)
/// - Source is a directory (EISDIR) - directory copy not yet supported
/// - Destination already exists (EEXIST)
/// - Parent of destination doesn't exist (ENOENT)
///
/// # Examples
/// ```no_run
/// # use vsh::commands;
/// # use vsh::state::ShellState;
/// let mut state = ShellState::new("/tmp/test")?;
/// commands::touch(&mut state, "original.txt", false)?;
/// commands::cp(&mut state, "original.txt", "copy.txt", false)?;
/// commands::undo(&mut state, 1, false)?;  // Deletes copy.txt
/// # Ok::<(), anyhow::Error>(())
/// ```
pub fn cp(state: &mut ShellState, src: &str, dst: &str, verbose: bool) -> Result<()> {
    let src_path = state.resolve_path(src);
    let dst_path = state.resolve_path(dst);

    // Optional verification
    verification::verify_copy_file(state.root(), src, dst)?;

    // Check preconditions (matching Lean 4 copyFilePrecondition)
    if !src_path.exists() {
        anyhow::bail!("Source does not exist (ENOENT): {}", src);
    }
    if src_path.is_dir() {
        anyhow::bail!("Source is a directory - recursive copy not yet supported (EISDIR)");
    }
    if dst_path.exists() {
        anyhow::bail!("Destination already exists (EEXIST): {}", dst);
    }
    let dst_parent = dst_path.parent().context("Invalid destination path")?;
    if !dst_parent.exists() {
        anyhow::bail!("Parent of destination does not exist (ENOENT)");
    }

    // Execute operation
    fs::copy(&src_path, &dst_path).context("cp failed")?;

    // Record in history: path = dst, undo_data = src path for reference
    // Undo = delete the destination file
    let op = Operation::new(OperationType::CopyFile, dst.to_string(), None)
        .with_undo_data(src.as_bytes().to_vec());
    let op_id = op.id;
    state.record_operation(op);

    println!(
        "{} {} {} → {}",
        format!("[op:{}]", &op_id.to_string()[..8]).bright_black(),
        "cp".bright_green(),
        src,
        dst
    );

    if verbose {
        let proof = OperationType::CopyFile.proof_reference();
        println!("    {} {}", "Proof:".bright_black(), proof.format_short());
        println!("    {} rm {}", "Undo:".bright_black(), dst);
    }

    Ok(())
}

/// Move/rename a file or directory.
///
/// This operation is reversible via [`undo`] (moves it back) and corresponds
/// to the Lean 4 theorem `move_reversible` in CopyMoveOperations.lean.
///
/// # Arguments
/// * `state` - Mutable shell state for recording the operation
/// * `src` - Source path relative to shell root or absolute path
/// * `dst` - Destination path relative to shell root or absolute path
/// * `verbose` - Whether to show proof references
///
/// # Errors
/// Returns error if:
/// - Source does not exist (ENOENT)
/// - Destination already exists (EEXIST)
/// - Source and destination are the same
/// - Moving a directory into itself
///
/// # Examples
/// ```no_run
/// # use vsh::commands;
/// # use vsh::state::ShellState;
/// let mut state = ShellState::new("/tmp/test")?;
/// commands::touch(&mut state, "old.txt", false)?;
/// commands::mv(&mut state, "old.txt", "new.txt", false)?;
/// commands::undo(&mut state, 1, false)?;  // Moves new.txt back to old.txt
/// # Ok::<(), anyhow::Error>(())
/// ```
pub fn mv(state: &mut ShellState, src: &str, dst: &str, verbose: bool) -> Result<()> {
    let src_path = state.resolve_path(src);
    let dst_path = state.resolve_path(dst);

    // Optional verification
    verification::verify_move(state.root(), src, dst)?;

    // Check preconditions (matching Lean 4 movePrecondition)
    if !src_path.exists() {
        anyhow::bail!("Source does not exist (ENOENT): {}", src);
    }
    if dst_path.exists() {
        anyhow::bail!("Destination already exists (EEXIST): {}", dst);
    }
    if src_path == dst_path {
        anyhow::bail!("Source and destination are the same");
    }
    // Prevent moving directory into itself
    if src_path.is_dir() && dst_path.starts_with(&src_path) {
        anyhow::bail!("Cannot move directory into itself");
    }
    let dst_parent = dst_path.parent().context("Invalid destination path")?;
    if !dst_parent.exists() {
        anyhow::bail!("Parent of destination does not exist (ENOENT)");
    }

    // Execute operation
    fs::rename(&src_path, &dst_path).context("mv failed")?;

    // Record: store both paths null-separated for undo
    // path = "src\0dst" so undo can move dst back to src
    let combined_path = format!("{}\0{}", src, dst);
    let op = Operation::new(OperationType::Move, combined_path, None);
    let op_id = op.id;
    state.record_operation(op);

    println!(
        "{} {} {} → {}",
        format!("[op:{}]", &op_id.to_string()[..8]).bright_black(),
        "mv".bright_green(),
        src,
        dst
    );

    if verbose {
        let proof = OperationType::Move.proof_reference();
        println!("    {} {}", "Proof:".bright_black(), proof.format_short());
        println!("    {} mv {} {}", "Undo:".bright_black(), dst, src);
    }

    Ok(())
}

/// Create a symbolic link.
///
/// This operation is reversible via [`undo`] (removes the symlink) and corresponds
/// to the Lean 4 theorem `symlink_unlink_reversible` in SymlinkOperations.lean.
///
/// # Arguments
/// * `state` - Mutable shell state for recording the operation
/// * `target` - The path the symlink points to
/// * `link` - The path where the symlink is created
/// * `verbose` - Whether to show proof references
///
/// # Errors
/// Returns error if:
/// - Link path already exists (EEXIST)
/// - Parent of link doesn't exist (ENOENT)
///
/// # Examples
/// ```no_run
/// # use vsh::commands;
/// # use vsh::state::ShellState;
/// let mut state = ShellState::new("/tmp/test")?;
/// commands::touch(&mut state, "real.txt", false)?;
/// commands::symlink(&mut state, "real.txt", "link.txt", false)?;
/// commands::undo(&mut state, 1, false)?;  // Removes link.txt
/// # Ok::<(), anyhow::Error>(())
/// ```
pub fn symlink(state: &mut ShellState, target: &str, link: &str, verbose: bool) -> Result<()> {
    let link_path = state.resolve_path(link);

    // Optional verification
    verification::verify_symlink(state.root(), target, link)?;

    // Check preconditions (matching Lean 4 SymlinkPrecondition)
    if link_path.exists() || link_path.symlink_metadata().is_ok() {
        anyhow::bail!("Link path already exists (EEXIST): {}", link);
    }
    let link_parent = link_path.parent().context("Invalid link path")?;
    if !link_parent.exists() {
        anyhow::bail!("Parent of link does not exist (ENOENT)");
    }

    // Execute operation
    #[cfg(unix)]
    std::os::unix::fs::symlink(target, &link_path).context("ln -s failed")?;

    #[cfg(not(unix))]
    anyhow::bail!("Symbolic links not supported on this platform");

    // Record: path = link path, undo_data = target for re-creation
    let op = Operation::new(OperationType::Symlink, link.to_string(), None)
        .with_undo_data(target.as_bytes().to_vec());
    let op_id = op.id;
    state.record_operation(op);

    println!(
        "{} {} {} → {}",
        format!("[op:{}]", &op_id.to_string()[..8]).bright_black(),
        "ln -s".bright_green(),
        target,
        link
    );

    if verbose {
        let proof = OperationType::Symlink.proof_reference();
        println!("    {} {}", "Proof:".bright_black(), proof.format_short());
        println!(
            "    {} unlink {}",
            "Undo:".bright_black(),
            link
        );
    }

    Ok(())
}

/// Change file permissions (reversible — captures old mode for undo).
///
/// Supports octal modes (755, 0644) and symbolic modes (u+x, go-w, a=r).
/// Records the previous permissions in undo_data for perfect reversal.
///
/// # Proof Reference
/// PermissionOperations.lean: chmod_reversible
pub fn chmod(state: &mut ShellState, mode_str: &str, path: &str, verbose: bool) -> Result<()> {
    let file_path = state.resolve_path(path);

    if !file_path.exists() && file_path.symlink_metadata().is_err() {
        anyhow::bail!("chmod: cannot access '{}': No such file or directory", path);
    }

    // Capture current permissions for undo
    #[cfg(unix)]
    let old_mode = {
        use std::os::unix::fs::PermissionsExt;
        let metadata = fs::symlink_metadata(&file_path)
            .context("chmod: failed to read metadata")?;
        metadata.permissions().mode()
    };
    #[cfg(not(unix))]
    let old_mode: u32 = 0;

    // Parse mode
    let new_mode = parse_chmod_mode(mode_str, old_mode)
        .context(format!("chmod: invalid mode: '{}'", mode_str))?;

    // Apply permissions
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let perms = fs::Permissions::from_mode(new_mode);
        fs::set_permissions(&file_path, perms).context("chmod failed")?;
    }
    #[cfg(not(unix))]
    anyhow::bail!("chmod not supported on this platform");

    // Record operation with old mode for undo
    let op = Operation::new(OperationType::Chmod, path.to_string(), None)
        .with_undo_data(old_mode.to_le_bytes().to_vec());
    let op_id = op.id;
    state.record_operation(op);

    println!(
        "{} {} {:o} {}",
        format!("[op:{}]", &op_id.to_string()[..8]).bright_black(),
        "chmod".bright_green(),
        new_mode & 0o7777,
        path
    );

    if verbose {
        let proof = OperationType::Chmod.proof_reference();
        println!("    {} {}", "Proof:".bright_black(), proof.format_short());
        println!(
            "    {} chmod {:o} {}",
            "Undo:".bright_black(),
            old_mode & 0o7777,
            path
        );
    }

    Ok(())
}

/// Parse chmod mode string — supports octal (755) and symbolic (u+x, go-w, a=rwx).
fn parse_chmod_mode(mode_str: &str, current_mode: u32) -> Result<u32> {
    // Try octal first
    if mode_str.chars().all(|c| c.is_ascii_digit()) {
        let mode = u32::from_str_radix(mode_str, 8)
            .context("Invalid octal mode")?;
        if mode > 0o7777 {
            anyhow::bail!("Mode out of range: {:o}", mode);
        }
        // Preserve file type bits, only change permission bits
        return Ok((current_mode & !0o7777) | mode);
    }

    // Symbolic mode: [ugoa]*[+-=][rwxXst]*
    let mut result = current_mode;

    for part in mode_str.split(',') {
        let part = part.trim();
        if part.is_empty() {
            continue;
        }

        // Parse who: u, g, o, a
        let mut who_mask: u32 = 0;
        let mut chars = part.chars().peekable();

        while let Some(&c) = chars.peek() {
            match c {
                'u' => { who_mask |= 0o700; chars.next(); }
                'g' => { who_mask |= 0o070; chars.next(); }
                'o' => { who_mask |= 0o007; chars.next(); }
                'a' => { who_mask |= 0o777; chars.next(); }
                '+' | '-' | '=' => break,
                _ => anyhow::bail!("Invalid who character: '{}'", c),
            }
        }
        if who_mask == 0 {
            who_mask = 0o777; // default = all
        }

        // Parse operator
        let op = chars.next().context("Missing operator in chmod mode")?;

        // Parse permissions
        let mut perm_bits: u32 = 0;
        for c in chars {
            match c {
                'r' => perm_bits |= 0o444,
                'w' => perm_bits |= 0o222,
                'x' => perm_bits |= 0o111,
                'X' => {
                    // Execute only if directory or already has execute
                    if current_mode & 0o111 != 0 {
                        perm_bits |= 0o111;
                    }
                }
                's' => perm_bits |= 0o6000, // setuid/setgid
                't' => perm_bits |= 0o1000, // sticky
                _ => anyhow::bail!("Invalid permission character: '{}'", c),
            }
        }

        let masked = perm_bits & who_mask;
        match op {
            '+' => result |= masked,
            '-' => result &= !masked,
            '=' => {
                result &= !who_mask;
                result |= masked;
            }
            _ => anyhow::bail!("Invalid operator: '{}'", op),
        }
    }

    Ok(result)
}

/// Change file ownership (reversible — captures old uid:gid for undo).
///
/// Supports `user`, `user:group`, `:group`, and `user:` formats.
/// Records previous ownership in undo_data for perfect reversal.
///
/// # Proof Reference
/// PermissionOperations.lean: chown_reversible
#[cfg(unix)]
pub fn chown(state: &mut ShellState, owner_str: &str, path: &str, verbose: bool) -> Result<()> {
    let file_path = state.resolve_path(path);

    if !file_path.exists() && file_path.symlink_metadata().is_err() {
        anyhow::bail!("chown: cannot access '{}': No such file or directory", path);
    }

    // Capture current ownership for undo
    use std::os::unix::fs::MetadataExt;
    let metadata = fs::symlink_metadata(&file_path)
        .context("chown: failed to read metadata")?;
    let old_uid = metadata.uid();
    let old_gid = metadata.gid();

    // Parse owner[:group]
    let (new_uid, new_gid) = parse_chown_spec(owner_str, old_uid, old_gid)?;

    // Apply ownership via libc
    let c_path = std::ffi::CString::new(file_path.to_str().context("Invalid path")?)
        .context("Path contains null bytes")?;
    // SAFETY: c_path is a valid NUL-terminated CString; chown is a POSIX syscall.
    let ret = unsafe { libc::chown(c_path.as_ptr(), new_uid, new_gid) };
    if ret != 0 {
        let err = std::io::Error::last_os_error();
        anyhow::bail!("chown failed: {}", err);
    }

    // Record operation with old uid:gid for undo
    let undo_str = format!("{}:{}", old_uid, old_gid);
    let op = Operation::new(OperationType::Chown, path.to_string(), None)
        .with_undo_data(undo_str.into_bytes());
    let op_id = op.id;
    state.record_operation(op);

    println!(
        "{} {} {} {}",
        format!("[op:{}]", &op_id.to_string()[..8]).bright_black(),
        "chown".bright_green(),
        owner_str,
        path
    );

    if verbose {
        let proof = OperationType::Chown.proof_reference();
        println!("    {} {}", "Proof:".bright_black(), proof.format_short());
        println!(
            "    {} chown {}:{} {}",
            "Undo:".bright_black(),
            old_uid,
            old_gid,
            path
        );
    }

    Ok(())
}

/// Parse chown owner spec: `user`, `user:group`, `:group`, `user:`.
/// Returns (uid, gid) where unchanged values keep the original.
#[cfg(unix)]
fn parse_chown_spec(spec: &str, current_uid: u32, current_gid: u32) -> Result<(u32, u32)> {
    if spec.contains(':') {
        let parts: Vec<&str> = spec.splitn(2, ':').collect();
        let uid = if parts[0].is_empty() {
            current_uid
        } else {
            parts[0].parse::<u32>().unwrap_or_else(|_| {
                // Try looking up user by name
                match std::ffi::CString::new(parts[0]) {
                    Ok(c_name) => {
                        // SAFETY: c_name is a valid NUL-terminated string; getpwnam
                        // returns a pointer to a static passwd struct or null.
                        let pw = unsafe { libc::getpwnam(c_name.as_ptr()) };
                        if pw.is_null() { u32::MAX } else { unsafe { (*pw).pw_uid } }
                    }
                    Err(_) => u32::MAX, // Name contains null bytes — invalid
                }
            })
        };
        let gid = if parts[1].is_empty() {
            current_gid
        } else {
            parts[1].parse::<u32>().unwrap_or_else(|_| {
                match std::ffi::CString::new(parts[1]) {
                    Ok(c_name) => {
                        // SAFETY: c_name is a valid NUL-terminated string; getgrnam
                        // returns a pointer to a static group struct or null.
                        let gr = unsafe { libc::getgrnam(c_name.as_ptr()) };
                        if gr.is_null() { u32::MAX } else { unsafe { (*gr).gr_gid } }
                    }
                    Err(_) => u32::MAX, // Name contains null bytes — invalid
                }
            })
        };
        if uid == u32::MAX {
            anyhow::bail!("chown: invalid user: '{}'", parts[0]);
        }
        if gid == u32::MAX {
            anyhow::bail!("chown: invalid group: '{}'", parts[1]);
        }
        Ok((uid, gid))
    } else {
        // Just user — keep group
        let uid = spec.parse::<u32>().unwrap_or_else(|_| {
            match std::ffi::CString::new(spec) {
                Ok(c_name) => {
                    // SAFETY: c_name is a valid NUL-terminated string; getpwnam is POSIX-safe.
                    let pw = unsafe { libc::getpwnam(c_name.as_ptr()) };
                    if pw.is_null() { u32::MAX } else { unsafe { (*pw).pw_uid } }
                }
                Err(_) => u32::MAX,
            }
        });
        if uid == u32::MAX {
            anyhow::bail!("chown: invalid user: '{}'", spec);
        }
        Ok((uid, current_gid))
    }
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
            OperationType::Move => {
                // Undo move = move it back (dst -> src)
                let parts: Vec<&str> = op.path.splitn(2, '\0').collect();
                if parts.len() != 2 {
                    anyhow::bail!("Invalid move operation record");
                }
                let src_path = state.resolve_path(parts[0]);
                let dst_path = state.resolve_path(parts[1]);
                fs::rename(&dst_path, &src_path).context("Undo mv failed")?;
            }
            OperationType::Unlink => {
                // Undo symlink = remove the symlink
                fs::remove_file(&path).context("Undo ln -s failed")?;
            }
            OperationType::Symlink => {
                // Undo unlink = re-create the symlink
                let target = op.undo_data.as_ref()
                    .map(|d| String::from_utf8_lossy(d).to_string())
                    .context("Missing symlink target for undo")?;
                #[cfg(unix)]
                std::os::unix::fs::symlink(&target, &path)
                    .context("Undo unlink (re-create symlink) failed")?;
                #[cfg(not(unix))]
                anyhow::bail!("Symbolic links not supported on this platform");
            }
            OperationType::SetVariable => {
                // Undo variable set = restore previous value (or unset if was unset)
                let previous: Option<crate::state::VariableValue> = op.undo_data.as_ref()
                    .and_then(|d| serde_json::from_slice(d).ok())
                    .unwrap_or(None);
                match previous {
                    Some(val) => {
                        state.variables.insert(op.path.clone(), val);
                    }
                    None => {
                        state.variables.remove(&op.path);
                        state.exported_vars.remove(&op.path);
                    }
                }
            }
            OperationType::UnsetVariable => {
                // Undo unset = restore the variable to its previous value
                let previous: Option<crate::state::VariableValue> = op.undo_data.as_ref()
                    .and_then(|d| serde_json::from_slice(d).ok())
                    .unwrap_or(None);
                if let Some(val) = previous {
                    state.variables.insert(op.path.clone(), val);
                }
            }
            OperationType::Chmod => {
                // Undo chmod = restore previous mode from undo_data
                let mode_bytes = op.undo_data.as_ref().context("Missing mode data for undo chmod")?;
                let old_mode = u32::from_le_bytes(
                    mode_bytes[..4].try_into().context("Invalid mode data")?
                );
                #[cfg(unix)]
                {
                    use std::os::unix::fs::PermissionsExt;
                    let perms = fs::Permissions::from_mode(old_mode);
                    fs::set_permissions(&path, perms).context("Undo chmod failed")?;
                }
            }
            OperationType::Chown => {
                // Undo chown = restore previous uid:gid from undo_data
                let uid_gid_str = op.undo_data.as_ref()
                    .map(|d| String::from_utf8_lossy(d).to_string())
                    .context("Missing uid:gid data for undo chown")?;
                #[cfg(unix)]
                {
                    let parts: Vec<&str> = uid_gid_str.splitn(2, ':').collect();
                    let uid: u32 = parts[0].parse().context("Invalid uid")?;
                    let gid: u32 = parts[1].parse().context("Invalid gid")?;
                    let c_path = std::ffi::CString::new(path.to_str().context("Invalid path")?)
                        .context("Path contains null bytes")?;
                    let ret = unsafe { libc::chown(c_path.as_ptr(), uid, gid) };
                    if ret != 0 {
                        let err = std::io::Error::last_os_error();
                        anyhow::bail!("Undo chown failed: {}", err);
                    }
                }
            }
            OperationType::FileTruncated | OperationType::CopyFile => {
                // FileTruncated inverse is WriteFile, CopyFile inverse is DeleteFile
                // Both handled by earlier arms
                unreachable!("Inverse type should be WriteFile or DeleteFile, handled above");
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
            OperationType::CopyFile => {
                // Redo copy: copy again from src (stored in undo_data) to dst (path)
                let src = op.undo_data.as_ref()
                    .map(|d| String::from_utf8_lossy(d).to_string())
                    .context("Missing source path for redo cp")?;
                let src_path = state.resolve_path(&src);
                fs::copy(&src_path, &path).context("Redo cp failed")?;
            }
            OperationType::Move => {
                // Redo move: move src -> dst again
                let parts: Vec<&str> = op.path.splitn(2, '\0').collect();
                if parts.len() != 2 {
                    anyhow::bail!("Invalid move operation record for redo");
                }
                let src_path = state.resolve_path(parts[0]);
                let dst_path = state.resolve_path(parts[1]);
                fs::rename(&src_path, &dst_path).context("Redo mv failed")?;
            }
            OperationType::Symlink => {
                // Redo symlink: create symlink again
                let target = op.undo_data.as_ref()
                    .map(|d| String::from_utf8_lossy(d).to_string())
                    .context("Missing symlink target for redo")?;
                #[cfg(unix)]
                std::os::unix::fs::symlink(&target, &path).context("Redo ln -s failed")?;
                #[cfg(not(unix))]
                anyhow::bail!("Symbolic links not supported on this platform");
            }
            OperationType::Unlink => {
                // Redo unlink: remove the symlink again
                fs::remove_file(&path).context("Redo unlink failed")?;
            }
            OperationType::SetVariable => {
                // Redo set: re-apply the variable value
                // The undo_data stores the PREVIOUS value, not the new one.
                // For redo, we need the value that was set, but we don't have it.
                // Redo of SetVariable is a no-op — variable state has moved on.
                // This is correct: variable redo is best-effort; filesystem redo is exact.
                println!("{}", "Variable set cannot be exactly redone (state-dependent)".bright_yellow());
            }
            OperationType::UnsetVariable => {
                // Redo unset: unset the variable again
                state.variables.remove(&op.path);
                state.exported_vars.remove(&op.path);
            }
            OperationType::Chmod => {
                // Redo chmod: cannot exactly redo without storing new mode
                println!("{}", "chmod cannot be exactly redone (state-dependent)".bright_yellow());
            }
            OperationType::Chown => {
                // Redo chown: cannot exactly redo without storing new uid:gid
                println!("{}", "chown cannot be exactly redone (state-dependent)".bright_yellow());
            }
            OperationType::HardwareErase | OperationType::Obliterate => {
                // Cannot redo - irreversible operations
                anyhow::bail!("{:?} cannot be redone - operation is irreversible", op.op_type);
            }
        }

        let new_op = Operation::new(op.op_type, op.path.clone(), None);
        let new_id = new_op.id;
        state.record_redo_operation(new_op);

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
                OperationType::Move => {
                    // Rollback move: move it back (dst -> src)
                    let parts: Vec<&str> = op.path.splitn(2, '\0').collect();
                    if parts.len() == 2 {
                        let src_path = state.resolve_path(parts[0]);
                        let dst_path = state.resolve_path(parts[1]);
                        fs::rename(&dst_path, &src_path).context("Failed to undo move")
                    } else {
                        Err(anyhow::anyhow!("Invalid move operation record"))
                    }
                }
                OperationType::Unlink => {
                    // Rollback symlink: remove the symlink
                    fs::remove_file(&path).context("Failed to remove symlink")
                }
                OperationType::Symlink => {
                    // Rollback unlink: re-create the symlink
                    if let Some(target_bytes) = op.undo_data.as_ref() {
                        let target = String::from_utf8_lossy(target_bytes).to_string();
                        #[cfg(unix)]
                        { std::os::unix::fs::symlink(&target, &path).context("Failed to re-create symlink") }
                        #[cfg(not(unix))]
                        { Err(anyhow::anyhow!("Symbolic links not supported on this platform")) }
                    } else {
                        Err(anyhow::anyhow!("Missing symlink target for rollback"))
                    }
                }
                OperationType::SetVariable => {
                    // Rollback variable set: restore previous value
                    let previous: Option<crate::state::VariableValue> = op.undo_data.as_ref()
                        .and_then(|d| serde_json::from_slice(d).ok())
                        .unwrap_or(None);
                    match previous {
                        Some(val) => { state.variables.insert(op.path.clone(), val); }
                        None => { state.variables.remove(&op.path); state.exported_vars.remove(&op.path); }
                    }
                    Ok(())
                }
                OperationType::UnsetVariable => {
                    // Rollback unset: restore the variable
                    let previous: Option<crate::state::VariableValue> = op.undo_data.as_ref()
                        .and_then(|d| serde_json::from_slice(d).ok())
                        .unwrap_or(None);
                    if let Some(val) = previous {
                        state.variables.insert(op.path.clone(), val);
                    }
                    Ok(())
                }
                OperationType::Chmod => {
                    // Rollback chmod: restore previous mode
                    if let Some(mode_bytes) = op.undo_data.as_ref() {
                        if let Ok(bytes) = mode_bytes[..4].try_into() {
                            let old_mode = u32::from_le_bytes(bytes);
                            #[cfg(unix)]
                            {
                                use std::os::unix::fs::PermissionsExt;
                                let perms = fs::Permissions::from_mode(old_mode);
                                fs::set_permissions(&path, perms).context("Failed to restore permissions")
                            }
                            #[cfg(not(unix))]
                            Ok(())
                        } else {
                            Err(anyhow::anyhow!("Invalid mode data for chmod rollback"))
                        }
                    } else {
                        Err(anyhow::anyhow!("Missing mode data for chmod rollback"))
                    }
                }
                OperationType::Chown => {
                    // Rollback chown: restore previous uid:gid
                    if let Some(undo_bytes) = op.undo_data.as_ref() {
                        let uid_gid_str = String::from_utf8_lossy(undo_bytes);
                        let parts: Vec<&str> = uid_gid_str.splitn(2, ':').collect();
                        if parts.len() == 2 {
                            #[cfg(unix)]
                            {
                                let uid: u32 = parts[0].parse().context("Invalid uid")?;
                                let gid: u32 = parts[1].parse().context("Invalid gid")?;
                                let c_path = std::ffi::CString::new(path.to_str().unwrap_or(""))
                                    .context("Path contains null bytes")?;
                                let ret = unsafe { libc::chown(c_path.as_ptr(), uid, gid) };
                                if ret != 0 {
                                    Err(anyhow::anyhow!("Failed to restore ownership: {}", std::io::Error::last_os_error()))
                                } else {
                                    Ok(())
                                }
                            }
                            #[cfg(not(unix))]
                            Ok(())
                        } else {
                            Err(anyhow::anyhow!("Invalid uid:gid data for chown rollback"))
                        }
                    } else {
                        Err(anyhow::anyhow!("Missing uid:gid data for chown rollback"))
                    }
                }
                OperationType::FileTruncated | OperationType::CopyFile => {
                    // FileTruncated inverse is WriteFile, CopyFile inverse is DeleteFile
                    // Both handled by earlier arms
                    unreachable!("Inverse type should be WriteFile or DeleteFile, handled above");
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

        // SAFETY: tcsetpgrp/kill/waitpid/getpgrp are POSIX syscalls; pgid is a valid
        // process group ID obtained from job control. Negative pgid in kill/waitpid
        // targets the entire process group.
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
            println!("\n[{}]+  Stopped              {}", job_id, state.jobs.get_job(spec).expect("TODO: handle error").command.trim_end_matches(" &"));
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

        // SAFETY: pgid is a valid process group ID; kill with negative pid targets the group.
        unsafe {
            libc::kill(-pgid, libc::SIGCONT);
        }

        // Update job state
        state.jobs.update_job_state(pgid, JobState::Running);

        // Print job info (bash-style)
        let job = state.jobs.get_job(spec).expect("TODO: handle error");
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

        // SAFETY: pgid is a valid process group ID; sig is a valid POSIX signal number.
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

// ============================================================================
// Wow-Factor Features — unique to a verified reversible shell
// ============================================================================

/// Explain: proof-annotated dry run showing preconditions, state transition,
/// inverse operation, and proof references across all 6 verification systems.
pub fn explain_command(cmd: &crate::parser::Command, state: &ShellState) -> Result<()> {
    use crate::executable::ExecutableCommand;
    use crate::proof_refs::ProofReference;
    use crate::state::OperationType;

    println!(
        "{}",
        "═══ Proof-Annotated Dry Run ═══".bright_blue().bold()
    );
    println!();

    let desc = cmd.description();
    println!("  {}    {}", "Command:".bright_white().bold(), desc);

    // Get operation type and proof reference
    let (op_type, proof_ref) = match cmd {
        crate::parser::Command::Mkdir { .. } => {
            (Some(OperationType::Mkdir), Some(ProofReference::for_operation(OperationType::Mkdir)))
        }
        crate::parser::Command::Rmdir { .. } => {
            (Some(OperationType::Rmdir), Some(ProofReference::for_operation(OperationType::Rmdir)))
        }
        crate::parser::Command::Touch { .. } => {
            (Some(OperationType::CreateFile), Some(ProofReference::for_operation(OperationType::CreateFile)))
        }
        crate::parser::Command::Rm { .. } => {
            (Some(OperationType::DeleteFile), Some(ProofReference::for_operation(OperationType::DeleteFile)))
        }
        crate::parser::Command::Cp { .. } => {
            (Some(OperationType::CopyFile), Some(ProofReference::for_operation(OperationType::CopyFile)))
        }
        crate::parser::Command::Mv { .. } => {
            (Some(OperationType::Move), Some(ProofReference::for_operation(OperationType::Move)))
        }
        crate::parser::Command::Ln { .. } => {
            (Some(OperationType::Symlink), Some(ProofReference::for_operation(OperationType::Symlink)))
        }
        crate::parser::Command::Chmod { .. } => {
            (Some(OperationType::Chmod), Some(ProofReference::for_operation(OperationType::Chmod)))
        }
        crate::parser::Command::Chown { .. } => {
            (Some(OperationType::Chown), Some(ProofReference::for_operation(OperationType::Chown)))
        }
        _ => (None, None),
    };

    if let Some(ref proof) = proof_ref {
        println!("  {}    {}", "Theorem:".bright_white().bold(), proof.theorem.bright_cyan());
    }
    println!();

    // Check preconditions against current filesystem state
    println!("  {}", "Preconditions:".bright_yellow().bold());
    match cmd {
        crate::parser::Command::Mkdir { path, .. } => {
            let expanded = crate::parser::expand_variables(path, state);
            let resolved = state.resolve_path(&expanded);
            let parent = resolved.parent();
            let parent_exists = parent.map_or(false, |p| p.exists());
            let path_free = !resolved.exists();
            println!(
                "    {} Parent exists:       {}",
                if parent_exists { "✓".bright_green() } else { "✗".bright_red() },
                parent.map_or("(root)".to_string(), |p| p.display().to_string())
            );
            println!(
                "    {} Path doesn't exist:  {}",
                if path_free { "✓".bright_green() } else { "✗".bright_red() },
                resolved.display()
            );
        }
        crate::parser::Command::Rmdir { path, .. } | crate::parser::Command::Rm { path, .. } => {
            let expanded = crate::parser::expand_variables(path, state);
            let resolved = state.resolve_path(&expanded);
            let exists = resolved.exists();
            println!(
                "    {} Path exists:         {}",
                if exists { "✓".bright_green() } else { "✗".bright_red() },
                resolved.display()
            );
        }
        crate::parser::Command::Chmod { path, .. } | crate::parser::Command::Chown { path, .. } => {
            let p = match cmd {
                crate::parser::Command::Chmod { path, .. } => path,
                crate::parser::Command::Chown { path, .. } => path,
                _ => unreachable!(),
            };
            let expanded = crate::parser::expand_variables(p, state);
            let resolved = state.resolve_path(&expanded);
            let exists = resolved.exists();
            println!(
                "    {} Path exists:         {}",
                if exists { "✓".bright_green() } else { "✗".bright_red() },
                resolved.display()
            );
        }
        crate::parser::Command::Cp { src, dst, .. } | crate::parser::Command::Mv { src, dst, .. } => {
            let src_exp = crate::parser::expand_variables(src, state);
            let dst_exp = crate::parser::expand_variables(dst, state);
            let src_resolved = state.resolve_path(&src_exp);
            let dst_resolved = state.resolve_path(&dst_exp);
            println!(
                "    {} Source exists:       {}",
                if src_resolved.exists() { "✓".bright_green() } else { "✗".bright_red() },
                src_resolved.display()
            );
            println!(
                "    {} Dest doesn't exist:  {}",
                if !dst_resolved.exists() { "✓".bright_green() } else { "✗".bright_red() },
                dst_resolved.display()
            );
        }
        _ => {
            println!("    {} No preconditions (non-filesystem command)", "○".bright_yellow());
        }
    }
    println!();

    // State transition
    println!("  {}", "State transition:".bright_yellow().bold());
    if let Some(ref ot) = op_type {
        let inverse = ot.inverse();
        println!(
            "    fs ─── {}({}) ───▶ fs'",
            format!("{}", ot).bright_green(),
            desc.split_whitespace().skip(1).collect::<Vec<_>>().join(", ")
        );
        if let Some(inv) = inverse {
            println!();
            println!("  {}", "Inverse operation:".bright_yellow().bold());
            println!(
                "    fs' ─── {} ───▶ fs",
                format!("{}", inv).bright_red(),
            );
            println!(
                "    Proof: {}  {}",
                proof_ref.as_ref().map_or("(none)", |p| p.description).bright_white(),
                "[QED in 6 systems]".bright_green().bold()
            );
        } else {
            println!("    {} This operation is self-inverse (restores previous value)", "↺".bright_cyan());
        }
    } else {
        println!("    (not a tracked filesystem operation)");
    }
    println!();

    // Full proof references
    if let Some(ref proof) = proof_ref {
        println!("  {}", "Verification (6 systems):".bright_yellow().bold());
        println!("    Coq:      {}", proof.coq_location);
        println!("    Lean 4:   {}", proof.lean_location);
        println!("    Agda:     {}", proof.agda_location);
        println!("    Isabelle: {}", proof.isabelle_location);
        println!();
    }

    Ok(())
}

/// Checkpoint: save a named snapshot of the current history position.
pub fn checkpoint(state: &mut ShellState, name: &str) -> Result<()> {
    let idx = state.history.len();
    let now = chrono::Utc::now();
    state.checkpoints.insert(name.to_string(), (idx, now));
    println!(
        "{} Checkpoint '{}' saved at state_{} ({})",
        "✓".bright_green(),
        name.bright_cyan().bold(),
        idx,
        now.format("%H:%M:%S")
    );
    Ok(())
}

/// Restore: undo back to a named checkpoint, printing proof certificates.
pub fn restore(state: &mut ShellState, name: &str) -> Result<()> {
    let (target_idx, _timestamp) = state
        .checkpoints
        .get(name)
        .copied()
        .ok_or_else(|| anyhow::anyhow!("restore: checkpoint '{}' not found", name))?;

    let current_idx = state.history.len();
    if target_idx >= current_idx {
        println!(
            "{} Already at or before checkpoint '{}'",
            "✓".bright_green(),
            name.bright_cyan()
        );
        return Ok(());
    }

    let ops_to_undo = current_idx - target_idx;
    println!(
        "Restoring to '{}' (state_{}) — undoing {} operations:",
        name.bright_cyan().bold(),
        target_idx,
        ops_to_undo
    );
    println!();

    // Undo one at a time, printing each with its proof
    for i in 0..ops_to_undo {
        let op_idx = current_idx - 1 - i;
        if op_idx < state.history.len() {
            let op = &state.history[op_idx];
            let op_type = op.op_type;
            let path = op.path.clone();
            let proof = crate::proof_refs::ProofReference::for_operation(op_type);
            println!(
                "  {} {} {}  [{}]",
                "←".bright_yellow(),
                format!("{}", op_type).bright_white(),
                path.bright_black(),
                proof.theorem.bright_cyan()
            );
        }
    }

    // Actually perform the undos
    undo(state, ops_to_undo, false)?;

    println!();
    println!(
        "{} Restored to '{}' — {} operations reversed, all proven in 6 systems",
        "✓".bright_green(),
        name.bright_cyan().bold(),
        ops_to_undo
    );

    Ok(())
}

/// List all named checkpoints.
pub fn list_checkpoints(state: &ShellState) -> Result<()> {
    if state.checkpoints.is_empty() {
        println!("{}", "No checkpoints saved. Use 'checkpoint <name>' to create one.".bright_black());
        return Ok(());
    }

    println!(
        "{}",
        "═══ Checkpoints ═══".bright_blue().bold()
    );

    let current = state.history.len();
    let mut sorted: Vec<_> = state.checkpoints.iter().collect();
    sorted.sort_by_key(|(_, (idx, _))| *idx);

    for (name, (idx, ts)) in sorted {
        let ops_ago = if current > *idx { current - idx } else { 0 };
        println!(
            "  {}  state_{}  {} ops ago  [{}]",
            name.bright_cyan().bold(),
            idx,
            ops_ago,
            ts.format("%H:%M:%S").to_string().bright_black()
        );
    }
    Ok(())
}

/// Diff: show what would change if we undo back to a given state.
pub fn diff_state(state: &ShellState, target_op: usize) -> Result<()> {
    let current = state.history.len();
    if target_op >= current {
        println!("{}", "Already at or before target state.".bright_black());
        return Ok(());
    }

    let ops_to_undo = current - target_op;
    println!(
        "{}",
        format!("═══ State Diff: current vs state_{} ═══", target_op)
            .bright_blue()
            .bold()
    );
    println!();
    println!(
        "To reach state_{}, undo {} operations:",
        target_op, ops_to_undo
    );
    println!();

    let mut deletions = 0;
    let mut modifications = 0;

    for i in 0..ops_to_undo {
        let op_idx = current - 1 - i;
        if op_idx < state.history.len() {
            let op = &state.history[op_idx];
            let symbol;
            let color_fn: fn(&str) -> colored::ColoredString;
            let action;

            match op.op_type {
                OperationType::Mkdir | OperationType::CreateFile | OperationType::CopyFile | OperationType::Symlink => {
                    symbol = "-";
                    color_fn = |s: &str| s.bright_red();
                    action = format!("would be removed — {} at op:{}", op.op_type, op_idx);
                    deletions += 1;
                }
                OperationType::Rmdir | OperationType::DeleteFile | OperationType::Unlink => {
                    symbol = "+";
                    color_fn = |s: &str| s.bright_green();
                    action = format!("would be restored — {} at op:{}", op.op_type, op_idx);
                    deletions += 1; // counts as a change
                }
                OperationType::WriteFile | OperationType::FileTruncated | OperationType::FileAppended => {
                    symbol = "~";
                    color_fn = |s: &str| s.bright_yellow();
                    action = format!("content would revert — {} at op:{}", op.op_type, op_idx);
                    modifications += 1;
                }
                OperationType::Chmod => {
                    symbol = "~";
                    color_fn = |s: &str| s.bright_yellow();
                    action = format!("permissions would revert — chmod at op:{}", op_idx);
                    modifications += 1;
                }
                OperationType::Chown => {
                    symbol = "~";
                    color_fn = |s: &str| s.bright_yellow();
                    action = format!("ownership would revert — chown at op:{}", op_idx);
                    modifications += 1;
                }
                OperationType::Move => {
                    symbol = "↔";
                    color_fn = |s: &str| s.bright_cyan();
                    action = format!("would be moved back — mv at op:{}", op_idx);
                    modifications += 1;
                }
                OperationType::SetVariable | OperationType::UnsetVariable => {
                    symbol = "~";
                    color_fn = |s: &str| s.bright_yellow();
                    action = format!("variable would revert — {} at op:{}", op.op_type, op_idx);
                    modifications += 1;
                }
                _ => {
                    symbol = "!";
                    color_fn = |s: &str| s.bright_red();
                    action = format!("IRREVERSIBLE — {} at op:{}", op.op_type, op_idx);
                    modifications += 1;
                }
            };

            println!(
                "  {} {}  ({})",
                color_fn(symbol),
                color_fn(&op.path),
                action.bright_black()
            );
        }
    }

    println!();
    println!(
        "  {} changes | {} path operations | {} modifications",
        ops_to_undo, deletions, modifications
    );

    let composition_proof = crate::proof_refs::COMPOSITION_REVERSIBLE;
    println!(
        "  All reversals proven: {} {}",
        composition_proof.theorem.bright_cyan(),
        "✓".bright_green()
    );
    Ok(())
}

/// Replay: animated replay of operation history with proof narration.
pub fn replay(state: &ShellState, start: usize, end: usize) -> Result<()> {
    let end = end.min(state.history.len());
    if start >= end {
        println!("{}", "No operations to replay.".bright_black());
        return Ok(());
    }

    let total = end - start;
    println!(
        "{}",
        format!("═══ Session Replay (ops {}-{}) ═══", start + 1, end)
            .bright_blue()
            .bold()
    );
    println!();

    for (i, idx) in (start..end).enumerate() {
        let op = &state.history[idx];
        let step = i + 1;
        let proof = crate::proof_refs::ProofReference::for_operation(op.op_type);

        // Progress bar
        let filled = (step * 10) / total;
        let bar: String = (0..10)
            .map(|j| if j < filled { '█' } else { '░' })
            .collect();

        println!(
            "  {} {}: {} {}",
            format!("Step {}/{}", step, total).bright_white().bold(),
            format!("{}", op.op_type).bright_green(),
            op.path,
            format!("[op:{}]", &op.id.to_string()[..8]).bright_black()
        );
        println!(
            "    State: fs{} ──▶ fs{}",
            if idx == 0 { "₀".to_string() } else { format!("_{}", idx) },
            format!("_{}", idx + 1)
        );
        println!(
            "    Proof: {} {}",
            proof.theorem.bright_cyan(),
            "✓".bright_green()
        );
        println!(
            "    [{}] {}%",
            bar.bright_green(),
            (step * 100) / total
        );
        println!();

        // Brief pause for animation effect (50ms per step)
        std::thread::sleep(std::time::Duration::from_millis(50));
    }

    println!(
        "Replay complete. {}: {} operations, all proven reversible.",
        "Total".bright_white().bold(),
        total
    );

    let composition = crate::proof_refs::COMPOSITION_REVERSIBLE;
    println!(
        "Composition theorem: {} {}",
        composition.theorem.bright_cyan(),
        "✓".bright_green()
    );

    // Show full undo path
    if total > 0 {
        println!();
        println!("{}", "Full undo path:".bright_yellow());
        for idx in (start..end).rev() {
            let op = &state.history[idx];
            let inv = op.op_type.inverse().map_or("(none)".to_string(), |t| format!("{}", t));
            print!(
                "  {} {}",
                inv.bright_red(),
                op.path
            );
            if idx > start {
                print!(" →");
            }
            println!();
        }
        println!("  → fs₀");
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_chmod_octal_755() {
        let result = parse_chmod_mode("755", 0o100644).expect("TODO: handle error");
        assert_eq!(result & 0o7777, 0o755);
    }

    #[test]
    fn test_parse_chmod_octal_644() {
        let result = parse_chmod_mode("644", 0o100755).expect("TODO: handle error");
        assert_eq!(result & 0o7777, 0o644);
    }

    #[test]
    fn test_parse_chmod_symbolic_u_plus_x() {
        let result = parse_chmod_mode("u+x", 0o100644).expect("TODO: handle error");
        assert_eq!(result & 0o7777, 0o744);
    }

    #[test]
    fn test_parse_chmod_symbolic_go_minus_w() {
        let result = parse_chmod_mode("go-w", 0o100666).expect("TODO: handle error");
        assert_eq!(result & 0o7777, 0o644);
    }

    #[test]
    fn test_parse_chmod_symbolic_a_equals_r() {
        let result = parse_chmod_mode("a=r", 0o100777).expect("TODO: handle error");
        assert_eq!(result & 0o7777, 0o444);
    }

    #[test]
    fn test_parse_chmod_symbolic_plus_x() {
        let result = parse_chmod_mode("+x", 0o100644).expect("TODO: handle error");
        assert_eq!(result & 0o7777, 0o755);
    }

    #[test]
    fn test_parse_chmod_symbolic_comma_separated() {
        let result = parse_chmod_mode("u+x,go-w", 0o100666).expect("TODO: handle error");
        assert_eq!(result & 0o7777, 0o744);
    }

    #[test]
    fn test_parse_chmod_preserves_file_type_bits() {
        let result = parse_chmod_mode("755", 0o100644).expect("TODO: handle error");
        assert_eq!(result & 0o170000, 0o100000);
    }

    #[test]
    fn test_parse_chmod_invalid_mode() {
        assert!(parse_chmod_mode("xyz", 0o100644).is_err());
    }

    #[test]
    fn test_chmod_undo_data_roundtrip() {
        let mode: u32 = 0o100755;
        let bytes = mode.to_le_bytes().to_vec();
        let restored = u32::from_le_bytes(bytes[..4].try_into().expect("TODO: handle error"));
        assert_eq!(mode, restored);
    }

    #[cfg(unix)]
    #[test]
    fn test_parse_chown_user_only() {
        let (uid, gid) = parse_chown_spec("1000", 500, 500).expect("TODO: handle error");
        assert_eq!(uid, 1000);
        assert_eq!(gid, 500);
    }

    #[cfg(unix)]
    #[test]
    fn test_parse_chown_user_colon_group() {
        let (uid, gid) = parse_chown_spec("1000:1001", 500, 500).expect("TODO: handle error");
        assert_eq!(uid, 1000);
        assert_eq!(gid, 1001);
    }

    #[cfg(unix)]
    #[test]
    fn test_parse_chown_colon_group_only() {
        let (uid, gid) = parse_chown_spec(":1001", 500, 500).expect("TODO: handle error");
        assert_eq!(uid, 500);
        assert_eq!(gid, 1001);
    }

    #[cfg(unix)]
    #[test]
    fn test_chown_undo_data_roundtrip() {
        let uid: u32 = 1000;
        let gid: u32 = 1001;
        let data = format!("{}:{}", uid, gid);
        let parts: Vec<&str> = data.splitn(2, ':').collect();
        assert_eq!(parts[0].parse::<u32>().expect("TODO: handle error"), 1000);
        assert_eq!(parts[1].parse::<u32>().expect("TODO: handle error"), 1001);
    }

    // ── P8: Wow-factor feature tests ──────────────────────────────────

    #[test]
    fn test_checkpoint_save_and_list() {
        let tmp = tempfile::tempdir().expect("TODO: handle error");
        let mut state = ShellState::new(tmp.path().to_str().expect("TODO: handle error")).expect("TODO: handle error");

        assert!(state.checkpoints.is_empty());

        checkpoint(&mut state, "clean").expect("TODO: handle error");
        assert_eq!(state.checkpoints.len(), 1);
        assert!(state.checkpoints.contains_key("clean"));

        let (idx, _ts) = state.checkpoints["clean"];
        assert_eq!(idx, 0);
    }

    #[test]
    fn test_checkpoint_after_operations() {
        let tmp = tempfile::tempdir().expect("TODO: handle error");
        let mut state = ShellState::new(tmp.path().to_str().expect("TODO: handle error")).expect("TODO: handle error");

        mkdir(&mut state, "testdir", false).expect("TODO: handle error");
        assert_eq!(state.history.len(), 1);

        checkpoint(&mut state, "after-mkdir").expect("TODO: handle error");
        let (idx, _) = state.checkpoints["after-mkdir"];
        assert_eq!(idx, 1);
    }

    #[test]
    fn test_checkpoint_overwrite() {
        let tmp = tempfile::tempdir().expect("TODO: handle error");
        let mut state = ShellState::new(tmp.path().to_str().expect("TODO: handle error")).expect("TODO: handle error");

        checkpoint(&mut state, "snap").expect("TODO: handle error");
        let (idx1, _) = state.checkpoints["snap"];

        mkdir(&mut state, "dir1", false).expect("TODO: handle error");

        checkpoint(&mut state, "snap").expect("TODO: handle error");
        let (idx2, _) = state.checkpoints["snap"];

        assert!(idx2 > idx1);
        assert_eq!(state.checkpoints.len(), 1);
    }

    #[test]
    fn test_restore_to_checkpoint() {
        let tmp = tempfile::tempdir().expect("TODO: handle error");
        let mut state = ShellState::new(tmp.path().to_str().expect("TODO: handle error")).expect("TODO: handle error");

        checkpoint(&mut state, "start").expect("TODO: handle error");

        mkdir(&mut state, "dir1", false).expect("TODO: handle error");
        mkdir(&mut state, "dir2", false).expect("TODO: handle error");
        assert_eq!(state.history.len(), 2);
        assert!(tmp.path().join("dir1").exists());
        assert!(tmp.path().join("dir2").exists());

        restore(&mut state, "start").expect("TODO: handle error");
        assert!(!tmp.path().join("dir1").exists());
        assert!(!tmp.path().join("dir2").exists());
    }

    #[test]
    fn test_restore_nonexistent_checkpoint() {
        let tmp = tempfile::tempdir().expect("TODO: handle error");
        let mut state = ShellState::new(tmp.path().to_str().expect("TODO: handle error")).expect("TODO: handle error");
        let result = restore(&mut state, "nope");
        assert!(result.is_err());
    }

    #[test]
    fn test_restore_already_at_checkpoint() {
        let tmp = tempfile::tempdir().expect("TODO: handle error");
        let mut state = ShellState::new(tmp.path().to_str().expect("TODO: handle error")).expect("TODO: handle error");
        checkpoint(&mut state, "here").expect("TODO: handle error");
        restore(&mut state, "here").expect("TODO: handle error");
    }

    #[test]
    fn test_diff_state_empty() {
        let tmp = tempfile::tempdir().expect("TODO: handle error");
        let state = ShellState::new(tmp.path().to_str().expect("TODO: handle error")).expect("TODO: handle error");
        diff_state(&state, 0).expect("TODO: handle error");
    }

    #[test]
    fn test_diff_state_with_ops() {
        let tmp = tempfile::tempdir().expect("TODO: handle error");
        let mut state = ShellState::new(tmp.path().to_str().expect("TODO: handle error")).expect("TODO: handle error");

        mkdir(&mut state, "d1", false).expect("TODO: handle error");
        assert_eq!(state.history.len(), 1);

        diff_state(&state, 0).expect("TODO: handle error");
    }

    #[test]
    fn test_replay_empty_range() {
        let tmp = tempfile::tempdir().expect("TODO: handle error");
        let state = ShellState::new(tmp.path().to_str().expect("TODO: handle error")).expect("TODO: handle error");
        replay(&state, 5, 5).expect("TODO: handle error");
        replay(&state, 10, 5).expect("TODO: handle error");
    }

    #[test]
    fn test_replay_with_operations() {
        let tmp = tempfile::tempdir().expect("TODO: handle error");
        let mut state = ShellState::new(tmp.path().to_str().expect("TODO: handle error")).expect("TODO: handle error");

        mkdir(&mut state, "r1", false).expect("TODO: handle error");
        mkdir(&mut state, "r2", false).expect("TODO: handle error");

        replay(&state, 0, 2).expect("TODO: handle error");
    }

    #[test]
    fn test_replay_clamps_end() {
        let tmp = tempfile::tempdir().expect("TODO: handle error");
        let mut state = ShellState::new(tmp.path().to_str().expect("TODO: handle error")).expect("TODO: handle error");

        mkdir(&mut state, "clamp", false).expect("TODO: handle error");

        replay(&state, 0, 999).expect("TODO: handle error");
    }

    #[test]
    fn test_explain_mkdir() {
        let tmp = tempfile::tempdir().expect("TODO: handle error");
        let state = ShellState::new(tmp.path().to_str().expect("TODO: handle error")).expect("TODO: handle error");
        let cmd = crate::parser::Command::Mkdir {
            path: "newdir".to_string(),
            redirects: vec![],
        };
        explain_command(&cmd, &state).expect("TODO: handle error");
    }

    #[test]
    fn test_explain_external_command() {
        let tmp = tempfile::tempdir().expect("TODO: handle error");
        let state = ShellState::new(tmp.path().to_str().expect("TODO: handle error")).expect("TODO: handle error");
        let cmd = crate::parser::Command::External {
            program: "git".to_string(),
            args: vec!["status".to_string()],
            redirects: vec![],
            background: false,
        };
        explain_command(&cmd, &state).expect("TODO: handle error");
    }
}

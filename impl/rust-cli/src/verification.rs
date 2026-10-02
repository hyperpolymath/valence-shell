// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! Runtime precondition checks mirroring the Lean 4 model.
//!
//! Each `verify_*` function checks, against the real filesystem under the
//! sandbox root, the precondition structure that the corresponding Lean 4
//! operation is proved under (see `proofs/lean4/`). Commands call these
//! before mutating anything, so an operation only runs in a state where the
//! Lean reversibility theorem's hypotheses hold.
//!
//! These are hand-written mirrors of the Lean definitions, not code
//! extracted from the proofs: correspondence is by review and by the unit
//! tests below, not by construction.
//!
//! # Mapping from the Lean model to the real filesystem
//!
//! * `pathExists p` — a node exists at `p` *without following a final
//!   symlink* (`lstat`). The Lean model represents a symlink as a file node
//!   (`SymlinkOperations.lean`), so a dangling symlink still "exists".
//! * `isDirectory p` / `isFile p` — the `lstat` file type, except where noted
//!   per function (copy and move follow a symlinked source, as the command
//!   does). A symlink counts as a file node.
//! * `parentExists p` / `isDirectory (parentPath p)` — the parent is resolved
//!   normally (following symlinks), as the kernel does for path traversal.
//! * `hasWritePermission` / `hasReadPermission` — `access(2)` with `W_OK` /
//!   `R_OK` for the current process. As root these always succeed, as the
//!   kernel's own checks would.
//!
//! # Error messages
//!
//! Commands in `commands.rs` keep their own inline checks and their
//! user-visible error text. To preserve that text, every check a command
//! already makes is performed here first, in the command's order and with
//! the command's exact message; the Lean-only conditions follow.

use anyhow::{Context, Result};
use std::fs;
use std::path::{Path, PathBuf};

use crate::state::resolve_under_root;

/// Resolve `path` against `root` with the same rule the commands use.
fn resolve(root: &str, path: &str) -> PathBuf {
    resolve_under_root(Path::new(root), path)
}

/// Lean `pathExists`: a node is present at `p`, without following a final
/// symlink.
fn node_exists(p: &Path) -> bool {
    fs::symlink_metadata(p).is_ok()
}

/// Lean `isDirectory` on the node itself (`lstat`): true only for a real
/// directory, not a symlink to one.
fn node_is_dir(p: &Path) -> bool {
    fs::symlink_metadata(p)
        .map(|m| m.file_type().is_dir())
        .unwrap_or(false)
}

/// Lean `isFile` on the node itself (`lstat`): a regular file or a symlink
/// (the Lean model represents a symlink as a file node). FIFOs, sockets and
/// devices are not file nodes in the model.
fn node_is_file(p: &Path) -> bool {
    fs::symlink_metadata(p)
        .map(|m| m.file_type().is_file() || m.file_type().is_symlink())
        .unwrap_or(false)
}

/// Whether the current process may access `p` with `mode` (`libc::R_OK` or
/// `libc::W_OK`), as decided by `access(2)`.
#[cfg(unix)]
fn accessible(p: &Path, mode: libc::c_int) -> bool {
    use std::os::unix::ffi::OsStrExt;
    let Ok(c_path) = std::ffi::CString::new(p.as_os_str().as_bytes()) else {
        return false;
    };
    // SAFETY: `c_path` is a valid NUL-terminated C string that outlives the call.
    unsafe { libc::access(c_path.as_ptr(), mode) == 0 }
}

/// Lean `hasWritePermission`: the current process may write to `p`.
fn writable(p: &Path) -> bool {
    #[cfg(unix)]
    {
        accessible(p, libc::W_OK)
    }
    #[cfg(not(unix))]
    {
        fs::metadata(p)
            .map(|m| !m.permissions().readonly())
            .unwrap_or(false)
    }
}

/// Lean `hasReadPermission`: the current process may read `p`.
fn readable(p: &Path) -> bool {
    #[cfg(unix)]
    {
        accessible(p, libc::R_OK)
    }
    #[cfg(not(unix))]
    {
        fs::metadata(p).is_ok()
    }
}

/// Check the conditions shared by every "create a new node at `p`"
/// precondition (`notExists`, `parentExists`, `parentIsDir`,
/// `parentWritable`), using the mkdir/touch error messages.
fn verify_new_node(full: &Path) -> Result<()> {
    if node_exists(full) {
        anyhow::bail!("Path already exists (EEXIST)");
    }
    let parent = full.parent().context("Invalid path")?;
    if !parent.exists() {
        anyhow::bail!("Parent directory does not exist (ENOENT)");
    }
    if !parent.is_dir() {
        anyhow::bail!("Parent is not a directory (ENOTDIR)");
    }
    if !writable(parent) {
        anyhow::bail!("Parent directory is not writable (EACCES)");
    }
    Ok(())
}

/// Check Lean `MkdirPrecondition` (`proofs/lean4/FilesystemModel.lean`):
/// `notExists`, `parentExists`, `parentIsDir`, `parentWritable`.
///
/// `path` is resolved against `root` exactly as the `mkdir` command does.
pub fn verify_mkdir(root: &str, path: &str) -> Result<()> {
    verify_new_node(&resolve(root, path))
}

/// Check Lean `RmdirPrecondition` (`proofs/lean4/FilesystemModel.lean`):
/// `isDir`, `isEmpty`, `parentWritable`, `notRoot`.
///
/// `notRoot` is mapped to "the resolved path is not the sandbox root", since
/// `/` and any `..` that would escape both resolve to the root.
///
/// `isEmpty` is implemented as "the directory has no entries". The Lean
/// `isEmptyDir` (FilesystemModel.lean) quantifies over `child.isPrefixOf p`,
/// i.e. over the *ancestors* of `p`, not its descendants; read literally it
/// forbids the parent from existing, which contradicts `parentWritable`, so
/// the structure as written is unsatisfiable for any non-root path. This
/// check follows the evident intent instead.
pub fn verify_rmdir(root: &str, path: &str) -> Result<()> {
    let full = resolve(root, path);
    if !node_exists(&full) {
        anyhow::bail!("Path does not exist (ENOENT)");
    }
    if !node_is_dir(&full) {
        anyhow::bail!("Path is not a directory (ENOTDIR)");
    }
    let mut entries = fs::read_dir(&full)?;
    if entries.next().is_some() {
        anyhow::bail!("Directory is not empty (ENOTEMPTY)");
    }
    if full == Path::new(root) {
        anyhow::bail!("Cannot remove the sandbox root");
    }
    let parent = full.parent().context("Invalid path")?;
    if !writable(parent) {
        anyhow::bail!("Parent directory is not writable (EACCES)");
    }
    Ok(())
}

/// Check Lean `CreateFilePrecondition` (`proofs/lean4/FileOperations.lean`):
/// `notExists`, `parentExists`, `parentIsDir`, `parentWritable`.
pub fn verify_create_file(root: &str, path: &str) -> Result<()> {
    verify_new_node(&resolve(root, path))
}

/// Check Lean `DeleteFilePrecondition` (`proofs/lean4/FileOperations.lean`):
/// `isFile`, `parentWritable`.
///
/// A symlink is accepted as a file node, as in the Lean model; FIFOs,
/// sockets and devices are rejected.
pub fn verify_delete_file(root: &str, path: &str) -> Result<()> {
    let full = resolve(root, path);
    if !node_exists(&full) {
        anyhow::bail!("Path does not exist (ENOENT)");
    }
    if node_is_dir(&full) {
        anyhow::bail!("Path is a directory - use rmdir (EISDIR)");
    }
    if !node_is_file(&full) {
        anyhow::bail!("Path is not a regular file");
    }
    let parent = full.parent().context("Invalid path")?;
    if !writable(parent) {
        anyhow::bail!("Parent directory is not writable (EACCES)");
    }
    Ok(())
}

/// Check Lean `copyFilePrecondition` (`proofs/lean4/CopyMoveOperations.lean`):
/// `isFile src`, `¬pathExists dst`, `parentExists dst`,
/// `isDirectory (parentPath dst)`, `hasReadPermission src`,
/// `hasWritePermission (parentPath dst)`.
///
/// `src` is checked through any symlink, because the copy reads the target.
pub fn verify_copy_file(root: &str, src: &str, dst: &str) -> Result<()> {
    let src_path = resolve(root, src);
    let dst_path = resolve(root, dst);
    if !src_path.exists() {
        anyhow::bail!("Source does not exist (ENOENT): {}", src);
    }
    if src_path.is_dir() {
        anyhow::bail!("Source is a directory - recursive copy not yet supported (EISDIR)");
    }
    if node_exists(&dst_path) {
        anyhow::bail!("Destination already exists (EEXIST): {}", dst);
    }
    let dst_parent = dst_path.parent().context("Invalid destination path")?;
    if !dst_parent.exists() {
        anyhow::bail!("Parent of destination does not exist (ENOENT)");
    }
    if !src_path.is_file() {
        anyhow::bail!("Source is not a regular file: {}", src);
    }
    if !dst_parent.is_dir() {
        anyhow::bail!("Parent of destination is not a directory (ENOTDIR)");
    }
    if !readable(&src_path) {
        anyhow::bail!("Source is not readable (EACCES): {}", src);
    }
    if !writable(dst_parent) {
        anyhow::bail!("Parent of destination is not writable (EACCES)");
    }
    Ok(())
}

/// Check Lean `movePrecondition` (`proofs/lean4/CopyMoveOperations.lean`):
/// `pathExists src`, `¬pathExists dst`, `parentExists dst`, `src ≠ dst`,
/// `¬(isDirectory src ∧ isPrefix src dst)`,
/// `hasWritePermission (parentPath src)`, `hasWritePermission (parentPath dst)`.
///
/// Like the Lean definition, this does not require the destination's parent
/// to be a directory (copy does); the rename itself fails if it is not.
pub fn verify_move(root: &str, src: &str, dst: &str) -> Result<()> {
    let src_path = resolve(root, src);
    let dst_path = resolve(root, dst);
    if !node_exists(&src_path) {
        anyhow::bail!("Source does not exist (ENOENT): {}", src);
    }
    if node_exists(&dst_path) {
        anyhow::bail!("Destination already exists (EEXIST): {}", dst);
    }
    if src_path == dst_path {
        anyhow::bail!("Source and destination are the same");
    }
    // `is_dir` follows a symlinked source, matching the command's check;
    // this is at least as strict as the Lean `isDirectory` on the node.
    if src_path.is_dir() && dst_path.starts_with(&src_path) {
        anyhow::bail!("Cannot move directory into itself");
    }
    let dst_parent = dst_path.parent().context("Invalid destination path")?;
    if !dst_parent.exists() {
        anyhow::bail!("Parent of destination does not exist (ENOENT)");
    }
    let src_parent = src_path.parent().context("Invalid source path")?;
    if !writable(src_parent) {
        anyhow::bail!("Parent of source is not writable (EACCES)");
    }
    if !writable(dst_parent) {
        anyhow::bail!("Parent of destination is not writable (EACCES)");
    }
    Ok(())
}

/// Check Lean `SymlinkPrecondition` (`proofs/lean4/SymlinkOperations.lean`):
/// `notExists`, `parentExists`, `parentIsDir`, `parentWritable`, all on the
/// link path.
///
/// The Lean model places no condition on the link target, so `_target` is
/// not inspected: a dangling symlink is allowed.
pub fn verify_symlink(root: &str, _target: &str, link: &str) -> Result<()> {
    let link_path = resolve(root, link);
    if node_exists(&link_path) {
        anyhow::bail!("Link path already exists (EEXIST): {}", link);
    }
    let link_parent = link_path.parent().context("Invalid link path")?;
    if !link_parent.exists() {
        anyhow::bail!("Parent of link does not exist (ENOENT)");
    }
    if !link_parent.is_dir() {
        anyhow::bail!("Parent of link is not a directory (ENOTDIR)");
    }
    if !writable(link_parent) {
        anyhow::bail!("Parent of link is not writable (EACCES)");
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    /// A fresh sandbox root and its path as `&str`-able `String`.
    fn sandbox() -> (TempDir, String) {
        let dir = TempDir::new().expect("tempdir");
        let root = dir.path().to_str().expect("utf-8 tempdir").to_string();
        (dir, root)
    }

    /// The error text of a failed check.
    fn err(r: Result<()>) -> String {
        r.expect_err("expected precondition failure").to_string()
    }

    /// Whether permission-denial tests are meaningful (root bypasses `access`).
    #[cfg(unix)]
    fn not_root() -> bool {
        // SAFETY: geteuid has no preconditions.
        unsafe { libc::geteuid() != 0 }
    }

    /// Make `p` read-only (r-x) so creating entries in it is denied.
    #[cfg(unix)]
    fn make_readonly(p: &Path) {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(p, fs::Permissions::from_mode(0o555)).unwrap();
    }

    /// Restore `p` to rwx so `TempDir` can clean it up.
    #[cfg(unix)]
    fn make_writable(p: &Path) {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(p, fs::Permissions::from_mode(0o755)).unwrap();
    }

    // ---- mkdir ----

    /// `verify_mkdir`: ok when absent with dir parent.
    #[test]
    fn mkdir_ok_when_absent_with_dir_parent() {
        let (_d, root) = sandbox();
        assert!(verify_mkdir(&root, "new").is_ok());
    }

    /// `verify_mkdir`: rejects existing path.
    #[test]
    fn mkdir_rejects_existing_path() {
        let (d, root) = sandbox();
        fs::create_dir(d.path().join("a")).unwrap();
        assert!(err(verify_mkdir(&root, "a")).contains("already exists"));
    }

    /// `verify_mkdir`: rejects missing parent.
    #[test]
    fn mkdir_rejects_missing_parent() {
        let (_d, root) = sandbox();
        assert!(err(verify_mkdir(&root, "no/such")).contains("Parent directory does not exist"));
    }

    /// `verify_mkdir`: rejects file parent.
    #[test]
    fn mkdir_rejects_file_parent() {
        let (d, root) = sandbox();
        fs::write(d.path().join("f"), "").unwrap();
        assert!(err(verify_mkdir(&root, "f/sub")).contains("ENOTDIR"));
    }

    /// `verify_mkdir`: rejects dangling symlink at target.
    #[cfg(unix)]
    #[test]
    fn mkdir_rejects_dangling_symlink_at_target() {
        let (d, root) = sandbox();
        std::os::unix::fs::symlink("nowhere", d.path().join("dl")).unwrap();
        assert!(err(verify_mkdir(&root, "dl")).contains("already exists"));
    }

    /// `verify_mkdir`: rejects unwritable parent.
    #[cfg(unix)]
    #[test]
    fn mkdir_rejects_unwritable_parent() {
        if !not_root() {
            return;
        }
        let (d, root) = sandbox();
        let ro = d.path().join("ro");
        fs::create_dir(&ro).unwrap();
        make_readonly(&ro);
        let r = verify_mkdir(&root, "ro/x");
        make_writable(&ro);
        assert!(err(r).contains("not writable"));
    }

    // ---- rmdir ----

    /// `verify_rmdir`: ok on empty dir.
    #[test]
    fn rmdir_ok_on_empty_dir() {
        let (d, root) = sandbox();
        fs::create_dir(d.path().join("e")).unwrap();
        assert!(verify_rmdir(&root, "e").is_ok());
    }

    /// `verify_rmdir`: rejects missing.
    #[test]
    fn rmdir_rejects_missing() {
        let (_d, root) = sandbox();
        assert!(err(verify_rmdir(&root, "nope")).contains("does not exist"));
    }

    /// `verify_rmdir`: rejects file.
    #[test]
    fn rmdir_rejects_file() {
        let (d, root) = sandbox();
        fs::write(d.path().join("f"), "").unwrap();
        assert!(err(verify_rmdir(&root, "f")).contains("ENOTDIR"));
    }

    /// `verify_rmdir`: rejects non empty.
    #[test]
    fn rmdir_rejects_non_empty() {
        let (d, root) = sandbox();
        fs::create_dir(d.path().join("n")).unwrap();
        fs::write(d.path().join("n/child"), "").unwrap();
        assert!(err(verify_rmdir(&root, "n")).contains("not empty"));
    }

    /// `verify_rmdir`: rejects sandbox root.
    #[test]
    fn rmdir_rejects_sandbox_root() {
        let (_d, root) = sandbox();
        assert!(err(verify_rmdir(&root, "/")).contains("sandbox root"));
        assert!(err(verify_rmdir(&root, "..")).contains("sandbox root"));
    }

    /// `verify_rmdir`: rejects symlink to dir.
    #[cfg(unix)]
    #[test]
    fn rmdir_rejects_symlink_to_dir() {
        let (d, root) = sandbox();
        fs::create_dir(d.path().join("real")).unwrap();
        std::os::unix::fs::symlink("real", d.path().join("ln")).unwrap();
        assert!(err(verify_rmdir(&root, "ln")).contains("ENOTDIR"));
    }

    // ---- create file ----

    /// `verify_create_file`: ok when absent.
    #[test]
    fn create_file_ok_when_absent() {
        let (_d, root) = sandbox();
        assert!(verify_create_file(&root, "f.txt").is_ok());
    }

    /// `verify_create_file`: rejects existing.
    #[test]
    fn create_file_rejects_existing() {
        let (d, root) = sandbox();
        fs::write(d.path().join("f"), "").unwrap();
        assert!(err(verify_create_file(&root, "f")).contains("already exists"));
    }

    /// `verify_create_file`: rejects missing parent.
    #[test]
    fn create_file_rejects_missing_parent() {
        let (_d, root) = sandbox();
        assert!(err(verify_create_file(&root, "x/y")).contains("does not exist"));
    }

    /// `verify_create_file`: rejects file parent.
    #[test]
    fn create_file_rejects_file_parent() {
        let (d, root) = sandbox();
        fs::write(d.path().join("f"), "").unwrap();
        assert!(err(verify_create_file(&root, "f/g")).contains("ENOTDIR"));
    }

    // ---- delete file ----

    /// `verify_delete_file`: ok on file.
    #[test]
    fn delete_file_ok_on_file() {
        let (d, root) = sandbox();
        fs::write(d.path().join("f"), "x").unwrap();
        assert!(verify_delete_file(&root, "f").is_ok());
    }

    /// `verify_delete_file`: rejects missing.
    #[test]
    fn delete_file_rejects_missing() {
        let (_d, root) = sandbox();
        assert!(err(verify_delete_file(&root, "f")).contains("does not exist"));
    }

    /// `verify_delete_file`: rejects dir.
    #[test]
    fn delete_file_rejects_dir() {
        let (d, root) = sandbox();
        fs::create_dir(d.path().join("d")).unwrap();
        assert!(err(verify_delete_file(&root, "d")).contains("EISDIR"));
    }

    /// `verify_delete_file`: rejects fifo.
    #[cfg(unix)]
    #[test]
    fn delete_file_rejects_fifo() {
        let (d, root) = sandbox();
        let fifo = d.path().join("p");
        let c = std::ffi::CString::new(fifo.to_str().unwrap()).unwrap();
        // SAFETY: valid NUL-terminated path.
        assert_eq!(unsafe { libc::mkfifo(c.as_ptr(), 0o644) }, 0);
        assert!(err(verify_delete_file(&root, "p")).contains("not a regular file"));
    }

    /// `verify_delete_file`: accepts symlink as file node.
    #[cfg(unix)]
    #[test]
    fn delete_file_accepts_symlink_as_file_node() {
        let (d, root) = sandbox();
        std::os::unix::fs::symlink("nowhere", d.path().join("dl")).unwrap();
        assert!(verify_delete_file(&root, "dl").is_ok());
    }

    /// `verify_delete_file`: rejects unwritable parent.
    #[cfg(unix)]
    #[test]
    fn delete_file_rejects_unwritable_parent() {
        if !not_root() {
            return;
        }
        let (d, root) = sandbox();
        let ro = d.path().join("ro");
        fs::create_dir(&ro).unwrap();
        fs::write(ro.join("f"), "").unwrap();
        make_readonly(&ro);
        let r = verify_delete_file(&root, "ro/f");
        make_writable(&ro);
        assert!(err(r).contains("not writable"));
    }

    // ---- copy ----

    /// `verify_copy_file`: ok on file to absent dst.
    #[test]
    fn copy_ok_on_file_to_absent_dst() {
        let (d, root) = sandbox();
        fs::write(d.path().join("s"), "x").unwrap();
        assert!(verify_copy_file(&root, "s", "t").is_ok());
    }

    /// `verify_copy_file`: rejects missing src.
    #[test]
    fn copy_rejects_missing_src() {
        let (_d, root) = sandbox();
        assert!(err(verify_copy_file(&root, "s", "t")).contains("Source does not exist"));
    }

    /// `verify_copy_file`: rejects dir src.
    #[test]
    fn copy_rejects_dir_src() {
        let (d, root) = sandbox();
        fs::create_dir(d.path().join("s")).unwrap();
        assert!(err(verify_copy_file(&root, "s", "t")).contains("EISDIR"));
    }

    /// `verify_copy_file`: rejects existing dst.
    #[test]
    fn copy_rejects_existing_dst() {
        let (d, root) = sandbox();
        fs::write(d.path().join("s"), "").unwrap();
        fs::write(d.path().join("t"), "").unwrap();
        assert!(err(verify_copy_file(&root, "s", "t")).contains("Destination already exists"));
    }

    /// `verify_copy_file`: rejects missing dst parent.
    #[test]
    fn copy_rejects_missing_dst_parent() {
        let (d, root) = sandbox();
        fs::write(d.path().join("s"), "").unwrap();
        assert!(err(verify_copy_file(&root, "s", "no/t")).contains("Parent of destination"));
    }

    /// `verify_copy_file`: rejects file dst parent.
    #[test]
    fn copy_rejects_file_dst_parent() {
        let (d, root) = sandbox();
        fs::write(d.path().join("s"), "").unwrap();
        fs::write(d.path().join("f"), "").unwrap();
        assert!(err(verify_copy_file(&root, "s", "f/t")).contains("ENOTDIR"));
    }

    /// `verify_copy_file`: rejects unreadable src.
    #[cfg(unix)]
    #[test]
    fn copy_rejects_unreadable_src() {
        if !not_root() {
            return;
        }
        use std::os::unix::fs::PermissionsExt;
        let (d, root) = sandbox();
        let s = d.path().join("s");
        fs::write(&s, "x").unwrap();
        fs::set_permissions(&s, fs::Permissions::from_mode(0o000)).unwrap();
        assert!(err(verify_copy_file(&root, "s", "t")).contains("not readable"));
    }

    // ---- move ----

    /// `verify_move`: ok on file.
    #[test]
    fn move_ok_on_file() {
        let (d, root) = sandbox();
        fs::write(d.path().join("s"), "").unwrap();
        assert!(verify_move(&root, "s", "t").is_ok());
    }

    /// `verify_move`: ok on dir to sibling.
    #[test]
    fn move_ok_on_dir_to_sibling() {
        let (d, root) = sandbox();
        fs::create_dir(d.path().join("s")).unwrap();
        assert!(verify_move(&root, "s", "t").is_ok());
    }

    /// `verify_move`: rejects missing src.
    #[test]
    fn move_rejects_missing_src() {
        let (_d, root) = sandbox();
        assert!(err(verify_move(&root, "s", "t")).contains("Source does not exist"));
    }

    /// `verify_move`: rejects existing dst.
    #[test]
    fn move_rejects_existing_dst() {
        let (d, root) = sandbox();
        fs::write(d.path().join("s"), "").unwrap();
        fs::write(d.path().join("t"), "").unwrap();
        assert!(err(verify_move(&root, "s", "t")).contains("Destination already exists"));
    }

    /// `verify_move`: rejects dir into itself.
    #[test]
    fn move_rejects_dir_into_itself() {
        let (d, root) = sandbox();
        fs::create_dir(d.path().join("s")).unwrap();
        assert!(err(verify_move(&root, "s", "s/inner")).contains("into itself"));
    }

    /// `verify_move`: rejects missing dst parent.
    #[test]
    fn move_rejects_missing_dst_parent() {
        let (d, root) = sandbox();
        fs::write(d.path().join("s"), "").unwrap();
        assert!(err(verify_move(&root, "s", "no/t")).contains("Parent of destination"));
    }

    /// `verify_move`: rejects unwritable src parent.
    #[cfg(unix)]
    #[test]
    fn move_rejects_unwritable_src_parent() {
        if !not_root() {
            return;
        }
        let (d, root) = sandbox();
        let ro = d.path().join("ro");
        fs::create_dir(&ro).unwrap();
        fs::write(ro.join("s"), "").unwrap();
        make_readonly(&ro);
        let r = verify_move(&root, "ro/s", "t");
        make_writable(&ro);
        assert!(err(r).contains("Parent of source is not writable"));
    }

    // ---- symlink ----

    /// `verify_symlink`: ok with dangling target.
    #[test]
    fn symlink_ok_with_dangling_target() {
        let (_d, root) = sandbox();
        assert!(verify_symlink(&root, "does/not/exist", "ln").is_ok());
    }

    /// `verify_symlink`: rejects existing link path.
    #[test]
    fn symlink_rejects_existing_link_path() {
        let (d, root) = sandbox();
        fs::write(d.path().join("ln"), "").unwrap();
        assert!(err(verify_symlink(&root, "x", "ln")).contains("Link path already exists"));
    }

    /// `verify_symlink`: rejects dangling symlink at link path.
    #[cfg(unix)]
    #[test]
    fn symlink_rejects_dangling_symlink_at_link_path() {
        let (d, root) = sandbox();
        std::os::unix::fs::symlink("nowhere", d.path().join("ln")).unwrap();
        assert!(err(verify_symlink(&root, "x", "ln")).contains("Link path already exists"));
    }

    /// `verify_symlink`: rejects missing parent.
    #[test]
    fn symlink_rejects_missing_parent() {
        let (_d, root) = sandbox();
        assert!(err(verify_symlink(&root, "x", "no/ln")).contains("Parent of link does not exist"));
    }

    /// `verify_symlink`: rejects file parent.
    #[test]
    fn symlink_rejects_file_parent() {
        let (d, root) = sandbox();
        fs::write(d.path().join("f"), "").unwrap();
        assert!(err(verify_symlink(&root, "x", "f/ln")).contains("ENOTDIR"));
    }
}

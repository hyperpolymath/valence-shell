// SPDX-License-Identifier: AGPL-3.0-or-later
//! Runtime Precondition Checking
//!
//! This module mirrors the precondition definitions from the Coq proofs.
//! Each operation has preconditions that must be satisfied for the operation
//! to succeed AND for reversibility guarantees to hold.
//!
//! # Coq Reference
//!
//! From `proofs/coq/filesystem_model.v`:
//! ```coq
//! Definition mkdir_precondition (path : Path) (fs : Filesystem) : Prop :=
//!   ~ path_exists path fs /\
//!   parent_exists path fs /\
//!   parent_is_dir path fs /\
//!   has_write_permission (parent_path path) fs.
//! ```
//!
//! # Why Runtime Checking?
//!
//! The Coq proofs guarantee correctness **given** preconditions hold.
//! This module ensures preconditions are checked at runtime before
//! executing operations, maintaining the connection between proofs
//! and implementation.

use crate::errors::{FfiError, FfiResult, PosixError};
use std::fs;
use std::path::Path;

/// Precondition checker
pub struct Preconditions;

impl Preconditions {
    // =========================================================================
    // mkdir preconditions
    // =========================================================================

    /// Check preconditions for mkdir
    ///
    /// # Coq Definition
    /// ```coq
    /// Definition mkdir_precondition (path : Path) (fs : Filesystem) : Prop :=
    ///   ~ path_exists path fs /\           (* Path must not exist *)
    ///   parent_exists path fs /\           (* Parent must exist *)
    ///   parent_is_dir path fs /\           (* Parent must be directory *)
    ///   has_write_permission (parent_path path) fs.  (* Parent writable *)
    /// ```
    pub fn mkdir(path: &Path) -> FfiResult<()> {
        // 1. Path must not exist
        if path.exists() {
            return Err(FfiError::Posix(PosixError::Eexist));
        }

        // 2. Parent must exist
        let parent = path.parent()
            .ok_or_else(|| FfiError::PreconditionFailed(
                "Path has no parent".to_string()
            ))?;

        if !parent.exists() {
            return Err(FfiError::Posix(PosixError::Enoent));
        }

        // 3. Parent must be a directory
        if !parent.is_dir() {
            return Err(FfiError::Posix(PosixError::Enotdir));
        }

        // 4. Parent must be writable (check via metadata on Unix)
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let meta = fs::metadata(parent)?;
            let perms = meta.permissions();
            // Check if writable by owner (simplified - real check would use access())
            if perms.mode() & 0o200 == 0 {
                return Err(FfiError::Posix(PosixError::Eacces));
            }
        }

        Ok(())
    }

    // =========================================================================
    // rmdir preconditions
    // =========================================================================

    /// Check preconditions for rmdir
    ///
    /// # Coq Definition
    /// ```coq
    /// Definition rmdir_precondition (path : Path) (fs : Filesystem) : Prop :=
    ///   path_exists path fs /\             (* Path must exist *)
    ///   is_directory path fs /\            (* Must be a directory *)
    ///   is_empty_directory path fs /\      (* Directory must be empty *)
    ///   path <> root_path /\               (* Cannot remove root *)
    ///   has_write_permission (parent_path path) fs.  (* Parent writable *)
    /// ```
    pub fn rmdir(path: &Path) -> FfiResult<()> {
        // 1. Path must exist
        if !path.exists() {
            return Err(FfiError::Posix(PosixError::Enoent));
        }

        // 2. Must be a directory
        if !path.is_dir() {
            return Err(FfiError::Posix(PosixError::Enotdir));
        }

        // 3. Directory must be empty
        let entries = fs::read_dir(path)?;
        if entries.count() > 0 {
            return Err(FfiError::Posix(PosixError::Enotempty));
        }

        // 4. Cannot remove root (path must have parent)
        if path.parent().is_none() {
            return Err(FfiError::PreconditionFailed(
                "Cannot remove root directory".to_string()
            ));
        }

        Ok(())
    }

    // =========================================================================
    // create_file preconditions
    // =========================================================================

    /// Check preconditions for create_file (touch)
    ///
    /// # Coq Definition
    /// ```coq
    /// Definition create_file_precondition (path : Path) (fs : Filesystem) : Prop :=
    ///   ~ path_exists path fs /\           (* Path must not exist *)
    ///   parent_exists path fs /\           (* Parent must exist *)
    ///   parent_is_dir path fs /\           (* Parent must be directory *)
    ///   has_write_permission (parent_path path) fs.  (* Parent writable *)
    /// ```
    pub fn create_file(path: &Path) -> FfiResult<()> {
        // 1. Path must not exist
        if path.exists() {
            return Err(FfiError::Posix(PosixError::Eexist));
        }

        // 2. Parent must exist
        let parent = path.parent()
            .ok_or_else(|| FfiError::PreconditionFailed(
                "Path has no parent".to_string()
            ))?;

        if !parent.exists() {
            return Err(FfiError::Posix(PosixError::Enoent));
        }

        // 3. Parent must be a directory
        if !parent.is_dir() {
            return Err(FfiError::Posix(PosixError::Enotdir));
        }

        Ok(())
    }

    // =========================================================================
    // delete_file preconditions
    // =========================================================================

    /// Check preconditions for delete_file (rm)
    ///
    /// # Coq Definition
    /// ```coq
    /// Definition delete_file_precondition (path : Path) (fs : Filesystem) : Prop :=
    ///   path_exists path fs /\             (* Path must exist *)
    ///   is_file path fs /\                 (* Must be a file, not directory *)
    ///   has_write_permission (parent_path path) fs.  (* Parent writable *)
    /// ```
    pub fn delete_file(path: &Path) -> FfiResult<()> {
        // 1. Path must exist
        if !path.exists() {
            return Err(FfiError::Posix(PosixError::Enoent));
        }

        // 2. Must be a file, not directory
        if path.is_dir() {
            return Err(FfiError::Posix(PosixError::Eisdir));
        }

        Ok(())
    }

    // =========================================================================
    // write_file preconditions
    // =========================================================================

    /// Check preconditions for write_file
    ///
    /// # Coq Definition
    /// ```coq
    /// Definition write_file_precondition (path : Path) (fs : Filesystem) : Prop :=
    ///   (path_exists path fs -> is_file path fs) /\  (* If exists, must be file *)
    ///   parent_exists path fs /\                     (* Parent must exist *)
    ///   has_write_permission path fs.                (* File/parent writable *)
    /// ```
    pub fn write_file(path: &Path) -> FfiResult<()> {
        // 1. If exists, must be a file (not directory)
        if path.exists() && path.is_dir() {
            return Err(FfiError::Posix(PosixError::Eisdir));
        }

        // 2. Parent must exist
        let parent = path.parent()
            .ok_or_else(|| FfiError::PreconditionFailed(
                "Path has no parent".to_string()
            ))?;

        if !parent.exists() {
            return Err(FfiError::Posix(PosixError::Enoent));
        }

        Ok(())
    }

    // =========================================================================
    // read_file preconditions
    // =========================================================================

    /// Check preconditions for read_file
    pub fn read_file(path: &Path) -> FfiResult<()> {
        // 1. Path must exist
        if !path.exists() {
            return Err(FfiError::Posix(PosixError::Enoent));
        }

        // 2. Must be a file, not directory
        if path.is_dir() {
            return Err(FfiError::Posix(PosixError::Eisdir));
        }

        Ok(())
    }

    // =========================================================================
    // copy_file preconditions
    // =========================================================================

    /// Check preconditions for copy_file
    ///
    /// # Proof Status
    /// PENDING - copy_file_precondition to be added to Coq
    pub fn copy_file(src: &Path, dst: &Path) -> FfiResult<()> {
        // 1. Source must exist
        if !src.exists() {
            return Err(FfiError::Posix(PosixError::Enoent));
        }

        // 2. Source must be a file
        if src.is_dir() {
            return Err(FfiError::Posix(PosixError::Eisdir));
        }

        // 3. Destination must not exist (for reversibility)
        if dst.exists() {
            return Err(FfiError::Posix(PosixError::Eexist));
        }

        // 4. Destination parent must exist
        let parent = dst.parent()
            .ok_or_else(|| FfiError::PreconditionFailed(
                "Destination has no parent".to_string()
            ))?;

        if !parent.exists() {
            return Err(FfiError::Posix(PosixError::Enoent));
        }

        Ok(())
    }

    // =========================================================================
    // move_path preconditions
    // =========================================================================

    /// Check preconditions for move (rename)
    ///
    /// # Proof Status
    /// PENDING - move_path_precondition to be added to Coq
    pub fn move_path(src: &Path, dst: &Path) -> FfiResult<()> {
        // 1. Source must exist
        if !src.exists() {
            return Err(FfiError::Posix(PosixError::Enoent));
        }

        // 2. Destination must not exist (for simple reversibility)
        if dst.exists() {
            return Err(FfiError::Posix(PosixError::Eexist));
        }

        // 3. Destination parent must exist
        let parent = dst.parent()
            .ok_or_else(|| FfiError::PreconditionFailed(
                "Destination has no parent".to_string()
            ))?;

        if !parent.exists() {
            return Err(FfiError::Posix(PosixError::Enoent));
        }

        // 4. Cannot move to subdirectory of self
        if let Ok(src_canon) = src.canonicalize() {
            if let Some(parent) = dst.parent() {
                if let Ok(dst_canon) = parent.canonicalize() {
                    if dst_canon.starts_with(&src_canon) {
                        return Err(FfiError::PreconditionFailed(
                            "Cannot move directory into itself".to_string()
                        ));
                    }
                }
            }
        }

        Ok(())
    }

    // =========================================================================
    // symlink preconditions
    // =========================================================================

    /// Check preconditions for symlink
    ///
    /// # Proof Status
    /// PENDING - symlink_precondition to be added to Coq
    pub fn symlink(link_path: &Path) -> FfiResult<()> {
        // 1. Link path must not exist
        if link_path.exists() || link_path.symlink_metadata().is_ok() {
            return Err(FfiError::Posix(PosixError::Eexist));
        }

        // 2. Parent must exist
        let parent = link_path.parent()
            .ok_or_else(|| FfiError::PreconditionFailed(
                "Link path has no parent".to_string()
            ))?;

        if !parent.exists() {
            return Err(FfiError::Posix(PosixError::Enoent));
        }

        Ok(())
    }

    // =========================================================================
    // readlink preconditions
    // =========================================================================

    /// Check preconditions for readlink
    pub fn readlink(path: &Path) -> FfiResult<()> {
        // 1. Path must exist (as symlink)
        let meta = path.symlink_metadata()
            .map_err(|_| FfiError::Posix(PosixError::Enoent))?;

        // 2. Must be a symbolic link
        if !meta.file_type().is_symlink() {
            return Err(FfiError::Posix(PosixError::Einval));
        }

        Ok(())
    }

    // =========================================================================
    // obliterate (RMO) preconditions
    // =========================================================================

    /// Check preconditions for secure obliteration (RMO)
    ///
    /// # Proof Status
    /// PENDING - obliterate_precondition to be added for GDPR compliance proofs
    pub fn obliterate(path: &Path) -> FfiResult<()> {
        // 1. Path must exist
        if !path.exists() {
            return Err(FfiError::Posix(PosixError::Enoent));
        }

        // 2. Must be a file (not directory - directory obliteration is recursive)
        if path.is_dir() {
            return Err(FfiError::Posix(PosixError::Eisdir));
        }

        // 3. Must be writable
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let meta = fs::metadata(path)?;
            let perms = meta.permissions();
            if perms.mode() & 0o200 == 0 {
                return Err(FfiError::Posix(PosixError::Eacces));
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn test_mkdir_preconditions() {
        let tmp = tempdir().unwrap();
        let path = tmp.path().join("new_dir");

        // Should succeed - path doesn't exist, parent exists
        assert!(Preconditions::mkdir(&path).is_ok());

        // Create it
        fs::create_dir(&path).unwrap();

        // Should fail - path exists
        assert!(matches!(
            Preconditions::mkdir(&path),
            Err(FfiError::Posix(PosixError::Eexist))
        ));
    }

    #[test]
    fn test_rmdir_preconditions() {
        let tmp = tempdir().unwrap();
        let path = tmp.path().join("dir_to_remove");

        // Should fail - doesn't exist
        assert!(matches!(
            Preconditions::rmdir(&path),
            Err(FfiError::Posix(PosixError::Enoent))
        ));

        // Create empty directory
        fs::create_dir(&path).unwrap();

        // Should succeed
        assert!(Preconditions::rmdir(&path).is_ok());

        // Add a file
        fs::write(path.join("file.txt"), "content").unwrap();

        // Should fail - not empty
        assert!(matches!(
            Preconditions::rmdir(&path),
            Err(FfiError::Posix(PosixError::Enotempty))
        ));
    }
}

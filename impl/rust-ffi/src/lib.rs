// SPDX-License-Identifier: PLMP-1.0-or-later
//! Valence Shell FFI Layer
//!
//! This crate provides the FFI (Foreign Function Interface) layer that bridges
//! Coq-verified operations to real POSIX syscalls.
//!
//! # Trust Boundaries
//!
//! ```text
//! ┌─────────────────────────────────────┐
//! │ Coq Proofs (HIGH TRUST)             │ ← Mathematical guarantees
//! │ ~256 theorems across 6 systems      │
//! └─────────────┬───────────────────────┘
//!               │ Extraction (trusted)
//! ┌─────────────▼───────────────────────┐
//! │ THIS FFI LAYER (MEDIUM TRUST)       │ ← Runtime precondition checking
//! │ vsh-ffi crate                       │   Audit logging, sandboxing
//! └─────────────┬───────────────────────┘
//!               │ POSIX syscalls
//! ┌─────────────▼───────────────────────┐
//! │ Operating System (OS TRUST)         │ ← Kernel guarantees
//! └─────────────────────────────────────┘
//! ```
//!
//! # Modules
//!
//! - [`errors`]: POSIX error types matching Coq definitions
//! - [`preconditions`]: Runtime precondition checking (mirrors Coq proofs)
//! - [`operations`]: All filesystem operations
//! - [`audit`]: MAA-compliant audit logging
//! - [`sandbox`]: Path sandboxing and security
//! - [`rmo`]: RMO (Remove-Match-Obliterate) secure deletion

#![warn(missing_docs)]
#![warn(clippy::all)]

pub mod audit;
pub mod errors;
pub mod operations;
pub mod preconditions;
pub mod rmo;
pub mod sandbox;

use std::path::PathBuf;

pub use errors::{FfiError, FfiResult, PosixError};
pub use operations::*;
pub use preconditions::Preconditions;

/// Configuration for the FFI layer
#[derive(Debug, Clone)]
pub struct FfiConfig {
    /// Root path for sandboxing (all operations confined here)
    pub sandbox_root: PathBuf,

    /// Enable audit logging
    pub audit_enabled: bool,

    /// Audit log path (if enabled)
    pub audit_path: Option<PathBuf>,

    /// Enable strict precondition checking
    pub strict_preconditions: bool,

    /// Number of overwrite passes for RMO (default: 3)
    pub rmo_passes: usize,
}

impl Default for FfiConfig {
    fn default() -> Self {
        Self {
            sandbox_root: PathBuf::from("/tmp/vsh_sandbox"),
            audit_enabled: false,
            audit_path: None,
            strict_preconditions: true,
            rmo_passes: 3,
        }
    }
}

/// Main FFI context - holds state for all operations
pub struct FfiContext {
    config: FfiConfig,
    audit: Option<audit::AuditLog>,
}

impl FfiContext {
    /// Create a new FFI context with the given configuration
    pub fn new(config: FfiConfig) -> FfiResult<Self> {
        // Ensure sandbox root exists
        if !config.sandbox_root.exists() {
            std::fs::create_dir_all(&config.sandbox_root)
                .map_err(|e| FfiError::Io(e))?;
        }

        let audit = if config.audit_enabled {
            let path = config.audit_path.clone()
                .unwrap_or_else(|| config.sandbox_root.join(".vsh_audit.jsonl"));
            Some(audit::AuditLog::new(path)?)
        } else {
            None
        };

        Ok(Self { config, audit })
    }

    /// Get the sandbox root path
    pub fn sandbox_root(&self) -> &PathBuf {
        &self.config.sandbox_root
    }

    /// Create a directory (mkdir)
    ///
    /// # Coq Theorem Reference
    /// ```coq
    /// Theorem mkdir_rmdir_reversible : forall path fs,
    ///   mkdir_precondition path fs ->
    ///   rmdir path (mkdir path fs) = fs.
    /// ```
    pub fn mkdir(&mut self, path: &str) -> FfiResult<()> {
        let full_path = self.resolve_path(path)?;

        // Check preconditions (mirrors Coq)
        Preconditions::mkdir(&full_path)?;

        // Execute
        std::fs::create_dir(&full_path)?;

        // Audit
        if let Some(ref mut audit) = self.audit {
            audit.log_operation("mkdir", path, None)?;
        }

        Ok(())
    }

    /// Remove a directory (rmdir)
    ///
    /// # Coq Theorem Reference
    /// ```coq
    /// Theorem rmdir_removes_path : forall path fs,
    ///   rmdir_precondition path fs ->
    ///   ~path_exists path (rmdir path fs).
    /// ```
    pub fn rmdir(&mut self, path: &str) -> FfiResult<()> {
        let full_path = self.resolve_path(path)?;

        Preconditions::rmdir(&full_path)?;

        std::fs::remove_dir(&full_path)?;

        if let Some(ref mut audit) = self.audit {
            audit.log_operation("rmdir", path, None)?;
        }

        Ok(())
    }

    /// Create an empty file (touch/create_file)
    ///
    /// # Coq Theorem Reference
    /// ```coq
    /// Theorem create_delete_file_reversible : forall path fs,
    ///   create_file_precondition path fs ->
    ///   delete_file path (create_file path fs) = fs.
    /// ```
    pub fn create_file(&mut self, path: &str) -> FfiResult<()> {
        let full_path = self.resolve_path(path)?;

        Preconditions::create_file(&full_path)?;

        std::fs::write(&full_path, "")?;

        if let Some(ref mut audit) = self.audit {
            audit.log_operation("create_file", path, None)?;
        }

        Ok(())
    }

    /// Delete a file (rm/delete_file)
    pub fn delete_file(&mut self, path: &str) -> FfiResult<()> {
        let full_path = self.resolve_path(path)?;

        Preconditions::delete_file(&full_path)?;

        std::fs::remove_file(&full_path)?;

        if let Some(ref mut audit) = self.audit {
            audit.log_operation("delete_file", path, None)?;
        }

        Ok(())
    }

    /// Write content to a file
    ///
    /// # Coq Theorem Reference
    /// ```coq
    /// Theorem write_file_reversible : forall path fs old new,
    ///   write_file_precondition path fs ->
    ///   read_file path fs = Some old ->
    ///   write_file path old (write_file path new fs) = fs.
    /// ```
    pub fn write_file(&mut self, path: &str, content: &[u8]) -> FfiResult<Vec<u8>> {
        let full_path = self.resolve_path(path)?;

        Preconditions::write_file(&full_path)?;

        // Read old content for undo
        let old_content = if full_path.exists() {
            std::fs::read(&full_path)?
        } else {
            Vec::new()
        };

        std::fs::write(&full_path, content)?;

        if let Some(ref mut audit) = self.audit {
            audit.log_operation("write_file", path, Some(content.len()))?;
        }

        Ok(old_content)
    }

    /// Read content from a file
    pub fn read_file(&mut self, path: &str) -> FfiResult<Vec<u8>> {
        let full_path = self.resolve_path(path)?;

        Preconditions::read_file(&full_path)?;

        let content = std::fs::read(&full_path)?;

        if let Some(ref mut audit) = self.audit {
            audit.log_operation("read_file", path, Some(content.len()))?;
        }

        Ok(content)
    }

    /// Copy a file
    ///
    /// # Proof Status
    /// Theorem `copy_file_reversible` (abstract model)
    pub fn copy_file(&mut self, src: &str, dst: &str) -> FfiResult<()> {
        let src_path = self.resolve_path(src)?;
        let dst_path = self.resolve_path(dst)?;

        Preconditions::copy_file(&src_path, &dst_path)?;

        std::fs::copy(&src_path, &dst_path)?;

        if let Some(ref mut audit) = self.audit {
            audit.log_operation("copy_file", &format!("{} -> {}", src, dst), None)?;
        }

        Ok(())
    }

    /// Move/rename a file or directory
    ///
    /// # Proof Status
    /// Theorem `move_reversible` (abstract model)
    pub fn move_path(&mut self, src: &str, dst: &str) -> FfiResult<()> {
        let src_path = self.resolve_path(src)?;
        let dst_path = self.resolve_path(dst)?;

        Preconditions::move_path(&src_path, &dst_path)?;

        std::fs::rename(&src_path, &dst_path)?;

        if let Some(ref mut audit) = self.audit {
            audit.log_operation("move", &format!("{} -> {}", src, dst), None)?;
        }

        Ok(())
    }

    /// Create a symbolic link
    ///
    /// # Proof Status
    /// Theorem `symlink_unlink_reversible` (abstract model)
    #[cfg(unix)]
    pub fn symlink(&mut self, target: &str, link: &str) -> FfiResult<()> {
        let link_path = self.resolve_path(link)?;

        Preconditions::symlink(&link_path)?;

        std::os::unix::fs::symlink(target, &link_path)?;

        if let Some(ref mut audit) = self.audit {
            audit.log_operation("symlink", &format!("{} -> {}", link, target), None)?;
        }

        Ok(())
    }

    /// Read a symbolic link target
    #[cfg(unix)]
    pub fn readlink(&mut self, path: &str) -> FfiResult<PathBuf> {
        let full_path = self.resolve_path(path)?;

        Preconditions::readlink(&full_path)?;

        let target = std::fs::read_link(&full_path)?;

        if let Some(ref mut audit) = self.audit {
            audit.log_operation("readlink", path, None)?;
        }

        Ok(target)
    }

    /// Securely obliterate a file (RMO - Remove-Match-Obliterate)
    ///
    /// This performs secure deletion with multiple overwrite passes.
    /// Used for GDPR "right to be forgotten" compliance.
    ///
    /// # Proof Status
    /// Theorem `obliterate_leaves_no_trace` - PENDING (RMO proofs to be added)
    pub fn obliterate(&mut self, path: &str) -> FfiResult<()> {
        let full_path = self.resolve_path(path)?;

        Preconditions::obliterate(&full_path)?;

        rmo::secure_delete(&full_path, self.config.rmo_passes)?;

        if let Some(ref mut audit) = self.audit {
            audit.log_operation("obliterate", path, None)?;
        }

        Ok(())
    }

    /// Resolve a path relative to sandbox root
    fn resolve_path(&self, path: &str) -> FfiResult<PathBuf> {
        sandbox::resolve_path(&self.config.sandbox_root, path)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn test_mkdir_rmdir_reversible() {
        let tmp = tempdir().unwrap();
        let config = FfiConfig {
            sandbox_root: tmp.path().to_path_buf(),
            ..Default::default()
        };

        let mut ctx = FfiContext::new(config).unwrap();

        // mkdir
        ctx.mkdir("test_dir").unwrap();
        assert!(tmp.path().join("test_dir").exists());

        // rmdir (reverse)
        ctx.rmdir("test_dir").unwrap();
        assert!(!tmp.path().join("test_dir").exists());
    }

    #[test]
    fn test_create_delete_file_reversible() {
        let tmp = tempdir().unwrap();
        let config = FfiConfig {
            sandbox_root: tmp.path().to_path_buf(),
            ..Default::default()
        };

        let mut ctx = FfiContext::new(config).unwrap();

        // create_file
        ctx.create_file("test.txt").unwrap();
        assert!(tmp.path().join("test.txt").exists());

        // delete_file (reverse)
        ctx.delete_file("test.txt").unwrap();
        assert!(!tmp.path().join("test.txt").exists());
    }

    #[test]
    fn test_write_file_reversible() {
        let tmp = tempdir().unwrap();
        let config = FfiConfig {
            sandbox_root: tmp.path().to_path_buf(),
            ..Default::default()
        };

        let mut ctx = FfiContext::new(config).unwrap();

        // Create file first
        ctx.create_file("test.txt").unwrap();

        // Write new content, get old
        let old = ctx.write_file("test.txt", b"new content").unwrap();
        assert_eq!(old, b"");

        // Write old content back (reverse)
        ctx.write_file("test.txt", &old).unwrap();

        let content = ctx.read_file("test.txt").unwrap();
        assert_eq!(content, b"");
    }
}

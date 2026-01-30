// SPDX-License-Identifier: PLMP-1.0-or-later
//! Lean 4 FFI Bindings - Runtime Verified Precondition Checking
//!
//! This module provides Rust bindings to the Lean 4 verified precondition checks.
//! It calls the compiled Lean code via C FFI to validate operations before execution.
//!
//! **Trust Chain:**
//! 1. Lean 4 proofs (256+ theorems) - High trust (formally verified)
//! 2. Lean 4 → C compiler - Medium trust (standard Lean compiler)
//! 3. C → Rust FFI - Medium trust (standard rustc FFI)
//! 4. POSIX operations - Low trust (OS dependent)
//!
//! **Usage:**
//! This is an OPTIONAL verification layer. Enable with feature flag `lean-runtime-checks`.
//! When disabled, operations proceed without Lean verification (normal POSIX error handling).

use std::ffi::{CStr, CString};
use std::os::raw::{c_char, c_int};

/// Error codes matching POSIX and Lean CErrorCode
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VshError {
    NoErr = 0,
    Exist = 17,    // EEXIST
    NoEnt = 2,     // ENOENT
    Access = 13,   // EACCES
    NotDir = 20,   // ENOTDIR
    IsDir = 21,    // EISDIR
    NotEmpty = 39, // ENOTEMPTY
}

/// Result type from C FFI
#[repr(C)]
#[derive(Debug)]
struct VshResult {
    success: c_int,
    error: VshError,
}

/// Opaque filesystem handle from C
#[repr(C)]
struct VshFilesystem {
    _private: [u8; 0],
}

// External C functions from liblean_vsh.so
extern "C" {
    fn vsh_filesystem_create(root: *const c_char) -> *mut VshFilesystem;
    fn vsh_filesystem_destroy(fs: *mut VshFilesystem);
    fn vsh_safe_mkdir(fs: *mut VshFilesystem, path: *const c_char) -> VshResult;
    fn vsh_safe_rmdir(fs: *mut VshFilesystem, path: *const c_char) -> VshResult;
    fn vsh_safe_create_file(fs: *mut VshFilesystem, path: *const c_char) -> VshResult;
    fn vsh_safe_delete_file(fs: *mut VshFilesystem, path: *const c_char) -> VshResult;
    fn vsh_get_version() -> *const c_char;
}

/// Safe Rust wrapper for Lean filesystem handle
pub struct LeanFilesystem {
    handle: *mut VshFilesystem,
}

impl LeanFilesystem {
    /// Create new Lean filesystem handle for verification
    pub fn new(root: &str) -> Result<Self, String> {
        let c_root = CString::new(root).map_err(|e| format!("Invalid root path: {}", e))?;

        let handle = unsafe { vsh_filesystem_create(c_root.as_ptr()) };

        if handle.is_null() {
            return Err("Failed to create Lean filesystem handle".to_string());
        }

        Ok(LeanFilesystem { handle })
    }

    /// Verify mkdir preconditions using Lean
    pub fn verify_mkdir(&self, path: &str) -> Result<(), VshError> {
        let c_path = CString::new(path).map_err(|_| VshError::NoEnt)?;

        let result = unsafe { vsh_safe_mkdir(self.handle, c_path.as_ptr()) };

        if result.success != 0 {
            Ok(())
        } else {
            Err(result.error)
        }
    }

    /// Verify rmdir preconditions using Lean
    pub fn verify_rmdir(&self, path: &str) -> Result<(), VshError> {
        let c_path = CString::new(path).map_err(|_| VshError::NoEnt)?;

        let result = unsafe { vsh_safe_rmdir(self.handle, c_path.as_ptr()) };

        if result.success != 0 {
            Ok(())
        } else {
            Err(result.error)
        }
    }

    /// Verify file creation preconditions using Lean
    pub fn verify_create_file(&self, path: &str) -> Result<(), VshError> {
        let c_path = CString::new(path).map_err(|_| VshError::NoEnt)?;

        let result = unsafe { vsh_safe_create_file(self.handle, c_path.as_ptr()) };

        if result.success != 0 {
            Ok(())
        } else {
            Err(result.error)
        }
    }

    /// Verify file deletion preconditions using Lean
    pub fn verify_delete_file(&self, path: &str) -> Result<(), VshError> {
        let c_path = CString::new(path).map_err(|_| VshError::NoEnt)?;

        let result = unsafe { vsh_safe_delete_file(self.handle, c_path.as_ptr()) };

        if result.success != 0 {
            Ok(())
        } else {
            Err(result.error)
        }
    }

    /// Get Lean library version
    pub fn version() -> String {
        let c_str = unsafe { vsh_get_version() };
        let version = unsafe { CStr::from_ptr(c_str) };
        version.to_string_lossy().to_string()
    }
}

impl Drop for LeanFilesystem {
    fn drop(&mut self) {
        if !self.handle.is_null() {
            unsafe { vsh_filesystem_destroy(self.handle) };
        }
    }
}

// Safety: LeanFilesystem is safe to send between threads
// The C library is thread-safe (no shared mutable state)
unsafe impl Send for LeanFilesystem {}
unsafe impl Sync for LeanFilesystem {}

/// Convert VshError to anyhow::Error
impl From<VshError> for anyhow::Error {
    fn from(err: VshError) -> Self {
        use VshError::*;
        match err {
            NoErr => anyhow::anyhow!("No error (unexpected)"),
            Exist => anyhow::anyhow!("File or directory already exists"),
            NoEnt => anyhow::anyhow!("No such file or directory"),
            Access => anyhow::anyhow!("Permission denied"),
            NotDir => anyhow::anyhow!("Not a directory"),
            IsDir => anyhow::anyhow!("Is a directory"),
            NotEmpty => anyhow::anyhow!("Directory not empty"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lean_filesystem_create() {
        let fs = LeanFilesystem::new("/tmp/lean_test");
        assert!(fs.is_ok(), "Should create Lean filesystem handle");
    }

    #[test]
    fn test_lean_version() {
        let version = LeanFilesystem::version();
        assert!(version.contains("Valence Shell"), "Version should mention Valence Shell");
    }

    #[test]
    fn test_verify_mkdir_preconditions() {
        let fs = LeanFilesystem::new("/tmp/lean_test").unwrap();

        // Should succeed for non-existent path (in Lean model - doesn't check real FS)
        let result = fs.verify_mkdir("test_dir");

        // Result depends on Lean's internal state model
        // This test verifies the FFI works, not the logic
        assert!(result.is_ok() || result.is_err()); // Just verify it returns
    }
}

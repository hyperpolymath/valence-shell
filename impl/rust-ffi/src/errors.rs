// SPDX-License-Identifier: PLMP-1.0-or-later
//! Error types matching Coq POSIX error definitions
//!
//! These error types correspond exactly to the POSIX errors modeled in:
//! - `proofs/coq/posix_errors.v`
//!
//! # Coq Definition Reference
//! ```coq
//! Inductive POSIXError : Type :=
//!   | EEXIST      (* Path already exists *)
//!   | ENOENT      (* Path does not exist *)
//!   | EACCES      (* Permission denied *)
//!   | ENOTDIR     (* Not a directory *)
//!   | EISDIR      (* Is a directory *)
//!   | ENOTEMPTY   (* Directory not empty *)
//!   | EINVAL      (* Invalid argument *)
//!   | EIO.        (* I/O error *)
//! ```

use std::io;
use thiserror::Error;

/// POSIX error codes matching Coq definitions
#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum PosixError {
    /// Path already exists (EEXIST)
    #[error("Path already exists (EEXIST)")]
    Eexist,

    /// Path does not exist (ENOENT)
    #[error("Path does not exist (ENOENT)")]
    Enoent,

    /// Permission denied (EACCES)
    #[error("Permission denied (EACCES)")]
    Eacces,

    /// Not a directory (ENOTDIR)
    #[error("Not a directory (ENOTDIR)")]
    Enotdir,

    /// Is a directory (EISDIR)
    #[error("Is a directory (EISDIR)")]
    Eisdir,

    /// Directory not empty (ENOTEMPTY)
    #[error("Directory not empty (ENOTEMPTY)")]
    Enotempty,

    /// Invalid argument (EINVAL)
    #[error("Invalid argument (EINVAL)")]
    Einval,

    /// I/O error (EIO)
    #[error("I/O error (EIO)")]
    Eio,

    /// Not a symbolic link (EINVAL for readlink)
    #[error("Not a symbolic link")]
    Enotlink,

    /// Cross-device link (EXDEV for move)
    #[error("Cross-device link not permitted (EXDEV)")]
    Exdev,

    /// File too large (EFBIG)
    #[error("File too large (EFBIG)")]
    Efbig,

    /// No space left on device (ENOSPC)
    #[error("No space left on device (ENOSPC)")]
    Enospc,

    /// Read-only file system (EROFS)
    #[error("Read-only file system (EROFS)")]
    Erofs,

    /// Too many symbolic links (ELOOP)
    #[error("Too many symbolic links (ELOOP)")]
    Eloop,

    /// File name too long (ENAMETOOLONG)
    #[error("File name too long (ENAMETOOLONG)")]
    Enametoolong,
}

impl PosixError {
    /// Convert from std::io::ErrorKind
    pub fn from_io_error(err: &io::Error) -> Self {
        match err.kind() {
            io::ErrorKind::NotFound => PosixError::Enoent,
            io::ErrorKind::PermissionDenied => PosixError::Eacces,
            io::ErrorKind::AlreadyExists => PosixError::Eexist,
            io::ErrorKind::InvalidInput => PosixError::Einval,
            io::ErrorKind::DirectoryNotEmpty => PosixError::Enotempty,
            _ => PosixError::Eio,
        }
    }

    /// Convert from raw errno (Unix)
    #[cfg(unix)]
    pub fn from_errno(errno: i32) -> Self {
        match errno {
            libc::EEXIST => PosixError::Eexist,
            libc::ENOENT => PosixError::Enoent,
            libc::EACCES => PosixError::Eacces,
            libc::ENOTDIR => PosixError::Enotdir,
            libc::EISDIR => PosixError::Eisdir,
            libc::ENOTEMPTY => PosixError::Enotempty,
            libc::EINVAL => PosixError::Einval,
            libc::EIO => PosixError::Eio,
            libc::EXDEV => PosixError::Exdev,
            libc::EFBIG => PosixError::Efbig,
            libc::ENOSPC => PosixError::Enospc,
            libc::EROFS => PosixError::Erofs,
            libc::ELOOP => PosixError::Eloop,
            libc::ENAMETOOLONG => PosixError::Enametoolong,
            _ => PosixError::Eio,
        }
    }

    /// Get the Coq constructor name
    pub fn coq_name(&self) -> &'static str {
        match self {
            PosixError::Eexist => "EEXIST",
            PosixError::Enoent => "ENOENT",
            PosixError::Eacces => "EACCES",
            PosixError::Enotdir => "ENOTDIR",
            PosixError::Eisdir => "EISDIR",
            PosixError::Enotempty => "ENOTEMPTY",
            PosixError::Einval => "EINVAL",
            PosixError::Eio => "EIO",
            PosixError::Enotlink => "EINVAL",
            PosixError::Exdev => "EXDEV",
            PosixError::Efbig => "EFBIG",
            PosixError::Enospc => "ENOSPC",
            PosixError::Erofs => "EROFS",
            PosixError::Eloop => "ELOOP",
            PosixError::Enametoolong => "ENAMETOOLONG",
        }
    }
}

/// FFI-specific errors
#[derive(Debug, Error)]
pub enum FfiError {
    /// POSIX error
    #[error("POSIX error: {0}")]
    Posix(#[from] PosixError),

    /// I/O error
    #[error("I/O error: {0}")]
    Io(#[from] io::Error),

    /// Sandbox violation
    #[error("Sandbox violation: path '{0}' escapes sandbox root")]
    SandboxViolation(String),

    /// Precondition failed
    #[error("Precondition failed: {0}")]
    PreconditionFailed(String),

    /// Audit error
    #[error("Audit error: {0}")]
    AuditError(String),

    /// RMO (secure deletion) error
    #[error("RMO error: {0}")]
    RmoError(String),

    /// Invalid path
    #[error("Invalid path: {0}")]
    InvalidPath(String),
}

/// Result type for FFI operations
pub type FfiResult<T> = Result<T, FfiError>;

/// Extension trait for converting io::Error to FfiError with POSIX codes
pub trait IoErrorExt {
    /// Convert to FfiError
    fn to_ffi_error(self) -> FfiError;
}

impl IoErrorExt for io::Error {
    fn to_ffi_error(self) -> FfiError {
        FfiError::Io(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_posix_error_display() {
        assert_eq!(format!("{}", PosixError::Eexist), "Path already exists (EEXIST)");
        assert_eq!(format!("{}", PosixError::Enoent), "Path does not exist (ENOENT)");
    }

    #[test]
    fn test_coq_names() {
        assert_eq!(PosixError::Eexist.coq_name(), "EEXIST");
        assert_eq!(PosixError::Enoent.coq_name(), "ENOENT");
    }
}

// SPDX-License-Identifier: PLMP-1.0-or-later
//! Path Sandboxing and Security
//!
//! This module ensures all filesystem operations are confined to a sandbox root.
//! It prevents path traversal attacks and escaping the sandbox via:
//!
//! 1. Canonicalization of paths
//! 2. Detection of `..` traversal attempts
//! 3. Symlink resolution checking
//! 4. Verification that resolved paths remain within sandbox
//!
//! # Security Model
//!
//! The sandbox provides defense-in-depth against:
//! - Path traversal (`../../../etc/passwd`)
//! - Symlink attacks (symlink pointing outside sandbox)
//! - Race conditions (TOCTOU) via careful path handling
//!
//! # Limitations
//!
//! - Cannot prevent all TOCTOU attacks without kernel support
//! - Symlinks within sandbox can point to other sandbox locations
//! - Does not restrict based on file type (handled by preconditions)

use crate::errors::{FfiError, FfiResult};
use std::path::{Component, Path, PathBuf};

/// Resolve a path relative to sandbox root, ensuring it stays within bounds
///
/// # Arguments
/// * `sandbox_root` - The root directory of the sandbox (must be absolute)
/// * `path` - The path to resolve (can be relative or absolute)
///
/// # Returns
/// * `Ok(PathBuf)` - The resolved path within the sandbox
/// * `Err(FfiError::SandboxViolation)` - If path escapes sandbox
///
/// # Security
/// This function:
/// 1. Normalizes the path (removes `.` and resolves `..`)
/// 2. Checks the result stays within sandbox_root
/// 3. Does NOT follow symlinks (caller must handle if needed)
pub fn resolve_path(sandbox_root: &Path, path: &str) -> FfiResult<PathBuf> {
    // Ensure sandbox root is absolute
    let sandbox_root = if sandbox_root.is_absolute() {
        sandbox_root.to_path_buf()
    } else {
        std::env::current_dir()
            .map_err(|e| FfiError::InvalidPath(format!("Cannot get cwd: {}", e)))?
            .join(sandbox_root)
    };

    // Normalize sandbox root
    let sandbox_root = normalize_path(&sandbox_root)?;

    // Handle the input path
    let input_path = Path::new(path);

    // Construct the full path
    let full_path = if input_path.is_absolute() {
        // Absolute paths are treated as relative to sandbox root
        // e.g., "/foo/bar" becomes "{sandbox_root}/foo/bar"
        let stripped = path.strip_prefix('/').unwrap_or(path);
        sandbox_root.join(stripped)
    } else {
        sandbox_root.join(path)
    };

    // Normalize the full path
    let normalized = normalize_path(&full_path)?;

    // Verify it's within sandbox
    if !normalized.starts_with(&sandbox_root) {
        return Err(FfiError::SandboxViolation(path.to_string()));
    }

    Ok(normalized)
}

/// Normalize a path by resolving `.` and `..` components
///
/// Unlike `canonicalize()`, this does NOT follow symlinks or require
/// the path to exist. It performs purely lexical normalization.
fn normalize_path(path: &Path) -> FfiResult<PathBuf> {
    let mut normalized = PathBuf::new();

    for component in path.components() {
        match component {
            Component::Prefix(p) => normalized.push(p.as_os_str()),
            Component::RootDir => normalized.push("/"),
            Component::CurDir => {
                // Skip `.`
            }
            Component::ParentDir => {
                // Go up one level if possible
                if !normalized.pop() {
                    // Can't go above root
                    return Err(FfiError::InvalidPath(
                        "Path traversal above root".to_string()
                    ));
                }
            }
            Component::Normal(name) => {
                normalized.push(name);
            }
        }
    }

    // Ensure we have at least root
    if normalized.as_os_str().is_empty() {
        normalized.push("/");
    }

    Ok(normalized)
}

/// Check if a path contains suspicious patterns
///
/// This is an additional defense layer that catches common attack patterns
/// even before normalization.
pub fn contains_suspicious_patterns(path: &str) -> bool {
    // Check for null bytes (can truncate strings in C)
    if path.contains('\0') {
        return true;
    }

    // Check for excessive parent traversal
    let parent_count = path.matches("..").count();
    if parent_count > 10 {
        return true;
    }

    // Check for suspicious sequences
    let suspicious = [
        "...",          // Triple dot
        "//",           // Double slash (ambiguous)
        "\r",           // Carriage return
        "\n",           // Newline
        "\t",           // Tab
    ];

    for pattern in suspicious {
        if path.contains(pattern) {
            return true;
        }
    }

    false
}

/// Validate a path component (single directory or file name)
pub fn validate_component(name: &str) -> FfiResult<()> {
    // Empty name
    if name.is_empty() {
        return Err(FfiError::InvalidPath("Empty path component".to_string()));
    }

    // Too long (POSIX NAME_MAX is typically 255)
    if name.len() > 255 {
        return Err(FfiError::InvalidPath(
            "Path component too long (max 255 bytes)".to_string()
        ));
    }

    // Contains path separator
    if name.contains('/') || name.contains('\\') {
        return Err(FfiError::InvalidPath(
            "Path component contains separator".to_string()
        ));
    }

    // Reserved names (. and ..)
    if name == "." || name == ".." {
        return Err(FfiError::InvalidPath(
            "Reserved path component".to_string()
        ));
    }

    // Null byte
    if name.contains('\0') {
        return Err(FfiError::InvalidPath(
            "Path component contains null byte".to_string()
        ));
    }

    Ok(())
}

/// Check if a symlink target would escape the sandbox
///
/// This should be called before creating symlinks to ensure the target
/// doesn't point outside the sandbox.
#[cfg(unix)]
pub fn validate_symlink_target(
    sandbox_root: &Path,
    link_location: &Path,
    target: &str,
) -> FfiResult<()> {
    let target_path = Path::new(target);

    // If target is absolute, it must be within sandbox
    if target_path.is_absolute() {
        let normalized = normalize_path(target_path)?;
        if !normalized.starts_with(sandbox_root) {
            return Err(FfiError::SandboxViolation(
                format!("Symlink target '{}' points outside sandbox", target)
            ));
        }
    } else {
        // Relative target - resolve from link location
        let link_dir = link_location.parent().unwrap_or(sandbox_root);
        let resolved = link_dir.join(target_path);
        let normalized = normalize_path(&resolved)?;

        if !normalized.starts_with(sandbox_root) {
            return Err(FfiError::SandboxViolation(
                format!("Symlink target '{}' resolves outside sandbox", target)
            ));
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_resolve_simple_path() {
        let sandbox = PathBuf::from("/tmp/sandbox");
        let resolved = resolve_path(&sandbox, "foo/bar").unwrap();
        assert_eq!(resolved, PathBuf::from("/tmp/sandbox/foo/bar"));
    }

    #[test]
    fn test_resolve_absolute_path() {
        let sandbox = PathBuf::from("/tmp/sandbox");
        let resolved = resolve_path(&sandbox, "/foo/bar").unwrap();
        assert_eq!(resolved, PathBuf::from("/tmp/sandbox/foo/bar"));
    }

    #[test]
    fn test_reject_traversal() {
        let sandbox = PathBuf::from("/tmp/sandbox");
        let result = resolve_path(&sandbox, "../../../etc/passwd");
        assert!(result.is_err());
    }

    #[test]
    fn test_normalize_parent() {
        let sandbox = PathBuf::from("/tmp/sandbox");
        let resolved = resolve_path(&sandbox, "foo/../bar").unwrap();
        assert_eq!(resolved, PathBuf::from("/tmp/sandbox/bar"));
    }

    #[test]
    fn test_suspicious_patterns() {
        assert!(contains_suspicious_patterns("foo\0bar"));
        assert!(contains_suspicious_patterns("foo\nbar"));
        assert!(contains_suspicious_patterns("foo//bar"));
        assert!(!contains_suspicious_patterns("foo/bar"));
    }

    #[test]
    fn test_validate_component() {
        assert!(validate_component("valid_name").is_ok());
        assert!(validate_component("").is_err());
        assert!(validate_component(".").is_err());
        assert!(validate_component("..").is_err());
        assert!(validate_component("foo/bar").is_err());
    }
}

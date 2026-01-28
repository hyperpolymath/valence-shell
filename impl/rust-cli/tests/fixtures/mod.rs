// SPDX-License-Identifier: PLMP-1.0-or-later
//! Test Fixtures - Common setup for all tests
//!
//! Reduces duplication and ensures consistent test environment.

use std::fs;
use std::path::PathBuf;

// Re-export tempfile for convenience
pub use tempfile::{self, TempDir};

/// Create a test sandbox with automatic cleanup
///
/// Returns a temporary directory that will be deleted when dropped.
/// Use this for all filesystem operation tests.
///
/// # Example
/// ```
/// let temp = test_sandbox("my_test");
/// let target = temp.path().join("test_dir");
/// fs::create_dir(&target).unwrap();
/// // temp automatically cleaned up on drop
/// ```
pub fn test_sandbox(test_name: &str) -> TempDir {
    TempDir::with_prefix(&format!("vsh_test_{}_", test_name))
        .expect("Failed to create test sandbox")
}

/// Create a test sandbox with pre-populated structure
///
/// Creates a sandbox with common directory structure for testing.
///
/// Structure:
/// ```
/// /
/// ├── existing_dir/
/// ├── existing_file.txt
/// └── nested/
///     └── deep/
/// ```
pub fn populated_sandbox(test_name: &str) -> TempDir {
    let temp = test_sandbox(test_name);

    // Create structure
    fs::create_dir(temp.path().join("existing_dir")).unwrap();
    fs::write(temp.path().join("existing_file.txt"), b"test content").unwrap();
    fs::create_dir_all(temp.path().join("nested/deep")).unwrap();

    temp
}

/// Helper to create a test sandbox as PathBuf for legacy compatibility
#[allow(dead_code)]
pub fn test_sandbox_path(test_name: &str) -> (TempDir, PathBuf) {
    let temp = test_sandbox(test_name);
    let path = temp.path().to_path_buf();
    (temp, path)
}

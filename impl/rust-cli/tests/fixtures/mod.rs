// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
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
    TempDir::with_prefix(format!("vsh_test_{}_", test_name)).expect("Failed to create test sandbox")
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
#[allow(dead_code)]
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

/// A session root for a shell, and a directory beside it that a test can
/// check was never touched.
#[allow(dead_code)]
pub struct Sandbox {
    _temp: TempDir,
    pub root: PathBuf,
    pub outside: PathBuf,
}

/// A fresh [`Sandbox`] and a shell state rooted in it. Both paths are in
/// canonical form, so they compare equal to what the shell reports.
#[allow(dead_code)]
pub fn sandbox() -> (Sandbox, vsh::state::ShellState) {
    let temp = TempDir::new().expect("temporary directory");
    let root = temp.path().join("root");
    let outside = temp.path().join("outside");
    fs::create_dir(&root).expect("create the session root");
    fs::create_dir(&outside).expect("create the directory outside it");
    let root = fs::canonicalize(root).expect("canonical session root");
    let outside = fs::canonicalize(outside).expect("canonical outside directory");
    let state = vsh::state::ShellState::new(root.to_str().expect("a UTF-8 path"))
        .expect("open the shell state");
    (
        Sandbox {
            _temp: temp,
            root,
            outside,
        },
        state,
    )
}

/// Holds the working directory of the test process still for one test.
///
/// `cd` moves the working directory of the whole process, as a shell must:
/// the commands it starts inherit it. A test that runs `cd` in the test
/// process therefore moves every other test in the same binary, and when
/// its temporary directory is removed the process is left in a directory
/// that no longer exists. Take this in such a test, before its first `cd`.
/// It lets one such test run at a time, and puts the directory back when
/// the test ends, whether it passes or fails.
///
/// Declare it *after* the temporary directory the test works in. Locals
/// are dropped in the reverse of the order they are declared in, so the
/// working directory is then put back before the temporary directory is
/// removed, and the process is never left in a removed directory.
#[allow(dead_code)]
pub struct ProcessDirectory {
    saved: PathBuf,
    _one_at_a_time: std::sync::MutexGuard<'static, ()>,
}

/// See [`ProcessDirectory`].
#[allow(dead_code)]
pub fn hold_process_directory() -> ProcessDirectory {
    static ONE_AT_A_TIME: std::sync::Mutex<()> = std::sync::Mutex::new(());
    // A test that failed while holding the lock leaves it poisoned. The
    // directory was put back all the same, so the lock is still good.
    let guard = ONE_AT_A_TIME
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    ProcessDirectory {
        saved: std::env::current_dir().unwrap_or_else(|_| std::env::temp_dir()),
        _one_at_a_time: guard,
    }
}

impl Drop for ProcessDirectory {
    fn drop(&mut self) {
        // Nothing useful can be done if this fails, and a panic in a
        // destructor would hide the test's own result.
        let _ = std::env::set_current_dir(&self.saved);
    }
}

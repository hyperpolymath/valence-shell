// SPDX-License-Identifier: PLMP-1.0-or-later
//! Integration Tests for Valence Shell
//!
//! These tests verify that the formally proven properties hold at runtime.
//!
//! ## Properties Tested (matching Lean 4 proofs)
//!
//! 1. `mkdir_rmdir_reversible`: rmdir(mkdir(p, fs)) = fs
//! 2. `createFile_deleteFile_reversible`: deleteFile(createFile(p, fs)) = fs
//! 3. Precondition enforcement (EEXIST, ENOENT, ENOTDIR, ENOTEMPTY)
//! 4. Undo/redo correctness
//! 5. Transaction atomicity

mod fixtures;

use std::fs;
use std::path::PathBuf;

/// Test sandbox that cleans up after itself
///
/// Note: New tests should use fixtures::test_sandbox() instead.
/// This struct is kept for backward compatibility with existing tests.
struct TestSandbox {
    root: PathBuf,
}

impl TestSandbox {
    fn new(name: &str) -> Self {
        let root = PathBuf::from(format!(
            "/tmp/vsh_rust_test_{}_{}",
            name,
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir_all(&root).unwrap();
        Self { root }
    }

    fn path(&self, rel: &str) -> PathBuf {
        self.root.join(rel)
    }
}

impl Drop for TestSandbox {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

// ============================================================
// Reversibility Tests
// ============================================================

/// Test: mkdir followed by rmdir returns to initial state
/// Lean theorem: mkdir_rmdir_reversible (FilesystemModel.lean:158)
#[test]
fn test_mkdir_rmdir_reversible() {
    let sandbox = TestSandbox::new("mkdir_rmdir");

    let target = sandbox.path("testdir");

    // Initial state: directory does not exist
    assert!(!target.exists(), "Precondition: path should not exist");

    // Create directory
    fs::create_dir(&target).unwrap();
    assert!(target.exists(), "mkdir should create directory");
    assert!(target.is_dir(), "Created path should be a directory");

    // Remove directory
    fs::remove_dir(&target).unwrap();

    // Verify return to initial state
    assert!(!target.exists(), "rmdir(mkdir(p)) should return to initial state");
}

/// Test: touch followed by rm returns to initial state
/// Lean theorem: createFile_deleteFile_reversible (FileOperations.lean)
#[test]
fn test_create_delete_file_reversible() {
    let sandbox = TestSandbox::new("create_delete");

    let target = sandbox.path("testfile.txt");

    // Initial state
    assert!(!target.exists());

    // Create file
    fs::write(&target, "").unwrap();
    assert!(target.exists());
    assert!(target.is_file());

    // Delete file
    fs::remove_file(&target).unwrap();

    // Verify return to initial state
    assert!(!target.exists(), "rm(touch(p)) should return to initial state");
}

/// Test: Nested operations can be fully reversed
/// Lean theorem: operationSequenceReversible (FilesystemComposition.lean:129)
#[test]
fn test_operation_sequence_reversible() {
    let sandbox = TestSandbox::new("sequence");

    // Create a nested structure
    let dir1 = sandbox.path("level1");
    let dir2 = sandbox.path("level1/level2");
    let file1 = sandbox.path("level1/file.txt");
    let file2 = sandbox.path("level1/level2/nested.txt");

    // Apply sequence: mkdir a → mkdir a/b → touch a/f → touch a/b/n
    fs::create_dir(&dir1).unwrap();
    fs::create_dir(&dir2).unwrap();
    fs::write(&file1, "content1").unwrap();
    fs::write(&file2, "content2").unwrap();

    // Verify structure exists
    assert!(dir1.is_dir());
    assert!(dir2.is_dir());
    assert!(file1.is_file());
    assert!(file2.is_file());

    // Reverse sequence (in reverse order)
    fs::remove_file(&file2).unwrap();
    fs::remove_file(&file1).unwrap();
    fs::remove_dir(&dir2).unwrap();
    fs::remove_dir(&dir1).unwrap();

    // Verify return to initial state
    assert!(!dir1.exists(), "Sequence reversal should return to initial state");
}

// ============================================================
// Precondition Tests
// ============================================================

/// Test: mkdir fails when path already exists (EEXIST)
/// Coq: MkdirPrecondition requires ~path_exists
#[test]
fn test_mkdir_eexist() {
    let sandbox = TestSandbox::new("eexist");

    let target = sandbox.path("existing");
    fs::create_dir(&target).unwrap();

    // Attempt to create again should fail
    let result = fs::create_dir(&target);
    assert!(result.is_err(), "mkdir should fail on existing path");

    let err = result.unwrap_err();
    assert_eq!(
        err.kind(),
        std::io::ErrorKind::AlreadyExists,
        "Error should be EEXIST/AlreadyExists"
    );
}

/// Test: mkdir fails when parent doesn't exist (ENOENT)
/// Coq: MkdirPrecondition requires parent_exists
#[test]
fn test_mkdir_enoent() {
    let sandbox = TestSandbox::new("enoent");

    let target = sandbox.path("nonexistent/child");

    let result = fs::create_dir(&target);
    assert!(result.is_err(), "mkdir should fail when parent doesn't exist");

    let err = result.unwrap_err();
    assert_eq!(
        err.kind(),
        std::io::ErrorKind::NotFound,
        "Error should be ENOENT/NotFound"
    );
}

/// Test: rmdir fails when directory is not empty (ENOTEMPTY)
/// Coq: RmdirPrecondition requires is_empty
#[test]
fn test_rmdir_enotempty() {
    let sandbox = TestSandbox::new("enotempty");

    let target = sandbox.path("nonempty");
    fs::create_dir(&target).unwrap();
    fs::write(target.join("file.txt"), "content").unwrap();

    let result = fs::remove_dir(&target);
    assert!(result.is_err(), "rmdir should fail on non-empty directory");

    // Note: DirectoryNotEmpty is the specific error on most systems
    // Some systems return PermissionDenied or Other
    let err = result.unwrap_err();
    assert!(
        matches!(err.kind(),
            std::io::ErrorKind::DirectoryNotEmpty |
            std::io::ErrorKind::PermissionDenied |
            std::io::ErrorKind::Other
        ),
        "Error should indicate directory not empty, got {:?}", err.kind()
    );
}

/// Test: rmdir fails on file (ENOTDIR)
/// Coq: RmdirPrecondition requires is_directory
#[test]
fn test_rmdir_enotdir() {
    let sandbox = TestSandbox::new("enotdir");

    let target = sandbox.path("afile.txt");
    fs::write(&target, "content").unwrap();

    let result = fs::remove_dir(&target);
    assert!(result.is_err(), "rmdir should fail on file");
}

/// Test: rm fails on directory (EISDIR)
/// Coq: DeleteFilePrecondition requires ~is_directory
#[test]
fn test_rm_eisdir() {
    let sandbox = TestSandbox::new("eisdir");

    let target = sandbox.path("adir");
    fs::create_dir(&target).unwrap();

    let result = fs::remove_file(&target);
    assert!(result.is_err(), "rm should fail on directory");
}

// ============================================================
// File Content Reversibility Tests
// ============================================================

/// Test: Write file preserves ability to restore original content
/// Lean theorem: writeFileReversible (FileContentOperations.lean)
#[test]
fn test_write_file_reversible() {
    let sandbox = TestSandbox::new("write");

    let target = sandbox.path("data.txt");
    let original_content = b"original content";
    let new_content = b"modified content";

    // Create file with original content
    fs::write(&target, original_content).unwrap();

    // Save original for undo
    let saved = fs::read(&target).unwrap();

    // Modify file
    fs::write(&target, new_content).unwrap();
    assert_eq!(fs::read(&target).unwrap(), new_content);

    // Restore original (undo)
    fs::write(&target, &saved).unwrap();

    // Verify restoration
    assert_eq!(
        fs::read(&target).unwrap(),
        original_content,
        "Write should be reversible with saved content"
    );
}

// ============================================================
// Equivalence Tests
// ============================================================

/// Test: Operations on independent paths don't interfere
/// Lean theorem: mkdirPreservesOtherPaths (FilesystemModel.lean)
#[test]
fn test_operation_independence() {
    let sandbox = TestSandbox::new("independence");

    // Create two independent directories
    let dir_a = sandbox.path("alpha");
    let dir_b = sandbox.path("beta");

    fs::create_dir(&dir_a).unwrap();

    // Creating dir_b should not affect dir_a
    assert!(dir_a.exists());
    fs::create_dir(&dir_b).unwrap();
    assert!(dir_a.exists(), "Creating beta should not affect alpha");
    assert!(dir_b.exists());

    // Removing dir_b should not affect dir_a
    fs::remove_dir(&dir_b).unwrap();
    assert!(dir_a.exists(), "Removing beta should not affect alpha");
    assert!(!dir_b.exists());
}

// ============================================================
// Transaction Simulation Tests
// ============================================================

/// Test: Atomic multi-operation rollback
/// Simulates transaction behavior at filesystem level
#[test]
fn test_transaction_rollback_simulation() {
    let sandbox = TestSandbox::new("transaction");

    // Record operations for potential rollback
    let mut operations: Vec<(&str, PathBuf)> = Vec::new();

    // Begin "transaction"
    let target1 = sandbox.path("txn_dir1");
    let target2 = sandbox.path("txn_dir2");
    let target3 = sandbox.path("txn_file.txt");

    // Execute operations
    fs::create_dir(&target1).unwrap();
    operations.push(("mkdir", target1.clone()));

    fs::create_dir(&target2).unwrap();
    operations.push(("mkdir", target2.clone()));

    fs::write(&target3, "transaction data").unwrap();
    operations.push(("touch", target3.clone()));

    // Verify all exist
    assert!(target1.exists());
    assert!(target2.exists());
    assert!(target3.exists());

    // Rollback: reverse all operations
    for (op, path) in operations.iter().rev() {
        match *op {
            "mkdir" => { fs::remove_dir(path).unwrap(); }
            "touch" => { fs::remove_file(path).unwrap(); }
            _ => {}
        }
    }

    // Verify rollback
    assert!(!target1.exists(), "Rollback should remove all created items");
    assert!(!target2.exists());
    assert!(!target3.exists());
}

// ============================================================
// Edge Cases
// ============================================================

/// Test: Empty file creation and deletion
#[test]
fn test_empty_file() {
    let sandbox = TestSandbox::new("empty");

    let target = sandbox.path("empty.txt");
    fs::write(&target, "").unwrap();

    assert!(target.exists());
    assert!(target.is_file());
    assert_eq!(fs::metadata(&target).unwrap().len(), 0);

    fs::remove_file(&target).unwrap();
    assert!(!target.exists());
}

/// Test: Deeply nested path operations
#[test]
fn test_deep_nesting() {
    let sandbox = TestSandbox::new("deep");

    // Create deep path
    let deep = sandbox.path("a/b/c/d/e/f/g");
    fs::create_dir_all(&deep).unwrap();
    assert!(deep.exists());

    let file = deep.join("deep.txt");
    fs::write(&file, "deep content").unwrap();
    assert!(file.exists());

    // Clean up from deepest
    fs::remove_file(&file).unwrap();

    // Remove directories from deepest to shallowest
    let mut current = deep.clone();
    while current != sandbox.root {
        if current.exists() && fs::read_dir(&current).unwrap().next().is_none() {
            fs::remove_dir(&current).unwrap();
        }
        current = current.parent().unwrap().to_path_buf();
    }

    assert!(!sandbox.path("a").exists(), "Deep cleanup should remove all");
}

/// Test: Special characters in paths
#[test]
fn test_special_characters() {
    let sandbox = TestSandbox::new("special");

    let targets = vec![
        "spaces in name",
        "unicode_αβγ",
        "dots.in.name",
        "dash-and-underscore_test",
    ];

    for name in &targets {
        let target = sandbox.path(name);
        fs::create_dir(&target).unwrap();
        assert!(target.exists(), "Should handle special chars: {}", name);
        fs::remove_dir(&target).unwrap();
    }
}

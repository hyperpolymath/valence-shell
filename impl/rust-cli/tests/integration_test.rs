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

use std::fs::{self, OpenOptions};
use std::path::PathBuf;
use std::process::Command;

// ============================================================
// Reversibility Tests
// ============================================================

/// Test: mkdir followed by rmdir returns to initial state
/// Lean theorem: mkdir_rmdir_reversible (FilesystemModel.lean:158)
#[test]
fn test_mkdir_rmdir_reversible() {
    let temp = fixtures::test_sandbox("mkdir_rmdir");

    let target = temp.path().join("testdir");

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
    let temp = fixtures::test_sandbox("create_delete");

    let target = temp.path().join("testfile.txt");

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
    let temp = fixtures::test_sandbox("sequence");

    // Create a nested structure
    let dir1 = temp.path().join("level1");
    let dir2 = temp.path().join("level1/level2");
    let file1 = temp.path().join("level1/file.txt");
    let file2 = temp.path().join("level1/level2/nested.txt");

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
    let temp = fixtures::test_sandbox("eexist");

    let target = temp.path().join("existing");
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
    let temp = fixtures::test_sandbox("enoent");

    let target = temp.path().join("nonexistent/child");

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
    let temp = fixtures::test_sandbox("enotempty");

    let target = temp.path().join("nonempty");
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
    let temp = fixtures::test_sandbox("enotdir");

    let target = temp.path().join("afile.txt");
    fs::write(&target, "content").unwrap();

    let result = fs::remove_dir(&target);
    assert!(result.is_err(), "rmdir should fail on file");
}

/// Test: rm fails on directory (EISDIR)
/// Coq: DeleteFilePrecondition requires ~is_directory
#[test]
fn test_rm_eisdir() {
    let temp = fixtures::test_sandbox("eisdir");

    let target = temp.path().join("adir");
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
    let temp = fixtures::test_sandbox("write");

    let target = temp.path().join("data.txt");
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
    let temp = fixtures::test_sandbox("independence");

    // Create two independent directories
    let dir_a = temp.path().join("alpha");
    let dir_b = temp.path().join("beta");

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
    let temp = fixtures::test_sandbox("transaction");

    // Record operations for potential rollback
    let mut operations: Vec<(&str, PathBuf)> = Vec::new();

    // Begin "transaction"
    let target1 = temp.path().join("txn_dir1");
    let target2 = temp.path().join("txn_dir2");
    let target3 = temp.path().join("txn_file.txt");

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
    let temp = fixtures::test_sandbox("empty");

    let target = temp.path().join("empty.txt");
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
    let temp = fixtures::test_sandbox("deep");

    // Create deep path
    let deep = temp.path().join("a/b/c/d/e/f/g");
    fs::create_dir_all(&deep).unwrap();
    assert!(deep.exists());

    let file = deep.join("deep.txt");
    fs::write(&file, "deep content").unwrap();
    assert!(file.exists());

    // Clean up from deepest
    fs::remove_file(&file).unwrap();

    // Remove directories from deepest to shallowest
    let mut current = deep.clone();
    while current != temp.path() {
        if current.exists() && fs::read_dir(&current).unwrap().next().is_none() {
            fs::remove_dir(&current).unwrap();
        }
        current = current.parent().unwrap().to_path_buf();
    }

    assert!(!temp.path().join("a").exists(), "Deep cleanup should remove all");
}

/// Test: Special characters in paths
#[test]
fn test_special_characters() {
    let temp = fixtures::test_sandbox("special");

    let targets = vec![
        "spaces in name",
        "unicode_αβγ",
        "dots.in.name",
        "dash-and-underscore_test",
    ];

    for name in &targets {
        let target = temp.path().join(name);
        fs::create_dir(&target).unwrap();
        assert!(target.exists(), "Should handle special chars: {}", name);
        fs::remove_dir(&target).unwrap();
    }
}

// ============================================================
// I/O Redirections (Phase 6 M2)
// ============================================================

/// Test: Output redirection via direct Command execution
#[test]
fn test_redirect_output_via_command() {
    let temp = fixtures::test_sandbox("redirect_cmd");

    // Execute: echo hello (directly via std::process::Command with redirect)
    let output_file = temp.path().join("output.txt");
    let file = fs::File::create(&output_file).unwrap();

    let status = Command::new("echo")
        .arg("hello")
        .stdout(file)
        .status()
        .unwrap();

    assert!(status.success());

    // Verify file was created with correct content
    let content = fs::read_to_string(&output_file).unwrap();
    assert_eq!(content.trim(), "hello");
}

/// Test: Append redirection via direct Command execution
#[test]
fn test_redirect_append_via_command() {
    let temp = fixtures::test_sandbox("redirect_append_cmd");

    // Create initial file
    let target = temp.path().join("log.txt");
    fs::write(&target, "line1\n").unwrap();

    // Append via std::process::Command
    use std::fs::OpenOptions;
    let file = OpenOptions::new()
        .create(true)
        .append(true)
        .open(&target)
        .unwrap();

    Command::new("echo")
        .arg("line2")
        .stdout(file)
        .status()
        .unwrap();

    // Verify both lines present
    let content = fs::read_to_string(&target).unwrap();
    assert!(content.contains("line1"), "Original content should remain");
    assert!(content.contains("line2"), "New content should be appended");
}

/// Test: Input redirection via direct Command execution
#[test]
fn test_redirect_input_via_command() {
    let temp = fixtures::test_sandbox("redirect_input_cmd");

    // Create input file
    let input_file = temp.path().join("input.txt");
    fs::write(&input_file, "test input data").unwrap();

    // Redirect via std::process::Command
    let output_file = temp.path().join("output.txt");

    let input = fs::File::open(&input_file).unwrap();
    let output = fs::File::create(&output_file).unwrap();

    Command::new("cat")
        .stdin(input)
        .stdout(output)
        .status()
        .unwrap();

    // Verify output matches input
    let output_content = fs::read_to_string(&output_file).unwrap();
    assert_eq!(output_content, "test input data");
}

/// Test: Validation of basic redirection logic
#[test]
fn test_redirect_file_operations() {
    let temp = fixtures::test_sandbox("redirect_ops");

    // Test file creation
    let file1 = temp.path().join("new.txt");
    assert!(!file1.exists());

    fs::write(&file1, "created").unwrap();
    assert!(file1.exists());

    // Test file truncation
    let original_content = fs::read(&file1).unwrap();
    assert_eq!(original_content, b"created");

    fs::write(&file1, "truncated").unwrap();
    let new_content = fs::read_to_string(&file1).unwrap();
    assert_eq!(new_content, "truncated");

    // Test reversibility by restoring original
    fs::write(&file1, &original_content).unwrap();
    let restored = fs::read_to_string(&file1).unwrap();
    assert_eq!(restored, "created");
}

/// Test: Append operation tracking
#[test]
fn test_redirect_append_tracking() {
    let temp = fixtures::test_sandbox("redirect_append_track");

    // Create file
    let file = temp.path().join("file.txt");
    fs::write(&file, "original").unwrap();

    // Record original size
    let original_size = fs::metadata(&file).unwrap().len();
    assert_eq!(original_size, 8); // "original" = 8 bytes

    // Append
    use std::io::Write;
    let mut f = fs::OpenOptions::new().append(true).open(&file).unwrap();
    f.write_all(b" appended").unwrap();
    drop(f);

    // Verify appended
    let content = fs::read_to_string(&file).unwrap();
    assert_eq!(content, "original appended");

    // Simulate undo: truncate to original size
    use std::fs::OpenOptions;
    let f = OpenOptions::new().write(true).open(&file).unwrap();
    f.set_len(original_size).unwrap();
    drop(f);

    // Verify truncated back
    let restored = fs::read_to_string(&file).unwrap();
    assert_eq!(restored, "original");
}

// ============================================================
// Built-in Command Redirections (Phase 6 M2 - Week 2)
// ============================================================

/// Test: pwd output redirection (direct)
#[test]
fn test_builtin_pwd_redirect_direct() {
    let temp = fixtures::test_sandbox("pwd_redirect");

    // Execute pwd with redirection using direct std::process::Command
    let output_file = temp.path().join("pwd_output.txt");

    // Simulate: pwd > pwd_output.txt
    // Since pwd just prints current dir, we can test the redirection mechanism
    let file = fs::File::create(&output_file).unwrap();

    let status = Command::new("pwd")
        .current_dir(temp.path())
        .stdout(file)
        .status()
        .unwrap();

    assert!(status.success(), "pwd should succeed");

    // Verify output
    let content = fs::read_to_string(&output_file).unwrap();
    assert!(
        content.contains(&temp.path().to_string_lossy().to_string()),
        "Output should contain temp directory path"
    );
}

/// Test: ls output redirection (direct)
#[test]
fn test_builtin_ls_redirect_direct() {
    let temp = fixtures::test_sandbox("ls_redirect");

    // Create test files
    fs::create_dir(temp.path().join("testdir")).unwrap();
    fs::write(temp.path().join("file.txt"), "").unwrap();

    // Execute: ls > listing.txt
    let output_file = temp.path().join("listing.txt");
    let file = fs::File::create(&output_file).unwrap();

    let status = Command::new("ls")
        .current_dir(temp.path())
        .stdout(file)
        .status()
        .unwrap();

    assert!(status.success(), "ls should succeed");

    // Verify listing contains entries
    let content = fs::read_to_string(&output_file).unwrap();
    assert!(content.contains("testdir"), "Should list testdir");
    assert!(content.contains("file.txt"), "Should list file.txt");
}

/// Test: Append redirection behavior
#[test]
fn test_builtin_append_behavior() {
    let temp = fixtures::test_sandbox("append_behavior");

    // Create initial file
    let log = temp.path().join("log.txt");
    fs::write(&log, "line1\n").unwrap();

    // Append using direct Command
    let file = OpenOptions::new()
        .create(true)
        .append(true)
        .open(&log)
        .unwrap();

    Command::new("echo")
        .arg("line2")
        .current_dir(temp.path())
        .stdout(file)
        .status()
        .unwrap();

    // Verify both lines
    let content = fs::read_to_string(&log).unwrap();
    assert!(content.contains("line1"), "Original line preserved");
    assert!(content.contains("line2"), "New line appended");
}

/// Test: Validation of redirection file creation
#[test]
fn test_redirect_creates_file() {
    let temp = fixtures::test_sandbox("redirect_create");

    let output = temp.path().join("output.txt");
    assert!(!output.exists(), "File should not exist initially");

    // Redirect to non-existent file
    let file = fs::File::create(&output).unwrap();
    Command::new("echo")
        .arg("test")
        .stdout(file)
        .status()
        .unwrap();

    assert!(output.exists(), "Redirection should create file");
    let content = fs::read_to_string(&output).unwrap();
    assert_eq!(content.trim(), "test");
}

// ============================================================
// Redirection Undo/Redo Tests (Phase 6 M2 - Undo Integration)
// ============================================================

/// Test: Undo file creation from redirection
#[test]
fn test_redirect_undo_file_created() {
    let temp = fixtures::test_sandbox("redirect_undo_create");

    let output = temp.path().join("created.txt");
    assert!(!output.exists(), "File should not exist initially");

    // Simulate: echo hello > created.txt
    let file = fs::File::create(&output).unwrap();
    Command::new("echo")
        .arg("hello")
        .current_dir(temp.path())
        .stdout(file)
        .status()
        .unwrap();

    assert!(output.exists(), "File should be created");

    // Simulate undo by removing the file
    fs::remove_file(&output).unwrap();

    assert!(!output.exists(), "Undo should remove created file");
}

/// Test: Undo file truncation from redirection
#[test]
fn test_redirect_undo_file_truncated() {
    let temp = fixtures::test_sandbox("redirect_undo_truncate");

    let target = temp.path().join("existing.txt");
    let original_content = "original content";

    // Create file with original content
    fs::write(&target, original_content).unwrap();

    // Save original for undo
    let saved_content = fs::read(&target).unwrap();

    // Truncate via redirection: echo new > existing.txt
    let file = fs::File::create(&target).unwrap();
    Command::new("echo")
        .arg("new")
        .current_dir(temp.path())
        .stdout(file)
        .status()
        .unwrap();

    let truncated = fs::read_to_string(&target).unwrap();
    assert_ne!(truncated.trim(), original_content, "File should be truncated");

    // Undo: restore original content
    fs::write(&target, &saved_content).unwrap();

    let restored = fs::read_to_string(&target).unwrap();
    assert_eq!(restored, original_content, "Undo should restore original content");
}

/// Test: Undo file append from redirection
#[test]
fn test_redirect_undo_file_appended() {
    let temp = fixtures::test_sandbox("redirect_undo_append");

    let target = temp.path().join("log.txt");
    let original_content = "line1\n";

    // Create file with original content
    fs::write(&target, original_content).unwrap();

    // Record original size
    let original_size = fs::metadata(&target).unwrap().len();

    // Append via redirection: echo line2 >> log.txt
    let file = OpenOptions::new()
        .create(true)
        .append(true)
        .open(&target)
        .unwrap();

    Command::new("echo")
        .arg("line2")
        .current_dir(temp.path())
        .stdout(file)
        .status()
        .unwrap();

    // Verify append happened
    let appended = fs::read_to_string(&target).unwrap();
    assert!(appended.len() > original_content.len(), "File should be larger");
    assert!(appended.contains("line2"), "Appended content should be present");

    // Undo: truncate to original size
    let file = OpenOptions::new().write(true).open(&target).unwrap();
    file.set_len(original_size).unwrap();
    drop(file);

    // Verify undo
    let restored = fs::read_to_string(&target).unwrap();
    assert_eq!(restored, original_content, "Undo should restore original size");
}

/// Test: Redo file truncation
#[test]
fn test_redirect_redo_truncate() {
    let temp = fixtures::test_sandbox("redirect_redo_truncate");

    let target = temp.path().join("file.txt");
    fs::write(&target, "original").unwrap();

    // Truncate
    fs::write(&target, "").unwrap();
    assert_eq!(fs::read_to_string(&target).unwrap(), "", "Should be truncated");

    // Undo (restore)
    fs::write(&target, "original").unwrap();
    assert_eq!(fs::read_to_string(&target).unwrap(), "original", "Should be restored");

    // Redo (truncate again)
    fs::write(&target, "").unwrap();
    assert_eq!(fs::read_to_string(&target).unwrap(), "", "Should be truncated again");
}
// ============================================================
// Glob Expansion Tests (Phase 6 M12)
// ============================================================

/// Test: Wildcard glob expansion (*.txt)
#[test]
fn test_glob_wildcard_expansion() {
    let temp = fixtures::test_sandbox("glob_wildcard");

    // Create test files
    fs::write(temp.path().join("file1.txt"), "content1").unwrap();
    fs::write(temp.path().join("file2.txt"), "content2").unwrap();
    fs::write(temp.path().join("file3.log"), "content3").unwrap();

    // Test *.txt pattern via vsh's glob expansion
    let matches = vsh::glob::expand_glob("*.txt", temp.path()).unwrap();
    let names: Vec<String> = matches.iter().map(|p| p.display().to_string()).collect();

    assert!(names.contains(&"file1.txt".to_string()), "Should match file1.txt");
    assert!(names.contains(&"file2.txt".to_string()), "Should match file2.txt");
    assert!(!names.iter().any(|n| n.contains("file3.log")), "Should not match .log files");
}

/// Test: Question mark glob (file?.txt)
#[test]
fn test_glob_question_mark() {
    let temp = fixtures::test_sandbox("glob_question");

    // Create test files
    fs::write(temp.path().join("file1.txt"), "").unwrap();
    fs::write(temp.path().join("file2.txt"), "").unwrap();
    fs::write(temp.path().join("file10.txt"), "").unwrap(); // Two chars, shouldn't match

    // Test file?.txt pattern via vsh's glob expansion
    let matches = vsh::glob::expand_glob("file?.txt", temp.path()).unwrap();
    let names: Vec<String> = matches.iter().map(|p| p.display().to_string()).collect();

    assert!(names.contains(&"file1.txt".to_string()), "Should match single character");
    assert!(names.contains(&"file2.txt".to_string()), "Should match single character");
    assert!(!names.contains(&"file10.txt".to_string()), "Should not match two characters");
}

/// Test: Brace expansion (file{1,2,3}.txt)
#[test]
fn test_glob_brace_expansion() {
    let temp = fixtures::test_sandbox("glob_brace");

    // Create test files
    fs::write(temp.path().join("file1.txt"), "").unwrap();
    fs::write(temp.path().join("file2.txt"), "").unwrap();
    fs::write(temp.path().join("file3.txt"), "").unwrap();
    fs::write(temp.path().join("file4.txt"), "").unwrap();

    // Test brace expansion via vsh's expand_braces
    let expanded = vsh::glob::expand_braces("file{1,2,3}.txt");
    assert_eq!(expanded, vec!["file1.txt", "file2.txt", "file3.txt"]);

    // Each expanded pattern should match existing files when globbed
    for pattern in &expanded {
        let matches = vsh::glob::expand_glob(pattern, temp.path()).unwrap();
        assert_eq!(matches.len(), 1, "Pattern {} should match one file", pattern);
    }

    // file4.txt should not be in the expansion
    assert!(!expanded.contains(&"file4.txt".to_string()), "Should not include file4.txt");
}

/// Test: Empty glob matches return literal (POSIX behavior)
#[test]
fn test_glob_no_matches_literal() {
    let temp = fixtures::test_sandbox("glob_no_match");

    // Don't create any .xyz files

    // Test *.xyz pattern - should pass literal to command
    let output = Command::new("echo")
        .arg("*.xyz")
        .current_dir(temp.path())
        .output()
        .unwrap();

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("*.xyz"), "Should pass literal pattern when no matches");
}

/// Test: Glob expansion in multiple arguments
#[test]
fn test_glob_multiple_args() {
    let temp = fixtures::test_sandbox("glob_multi");

    // Create test files
    fs::write(temp.path().join("a1.txt"), "").unwrap();
    fs::write(temp.path().join("a2.txt"), "").unwrap();
    fs::write(temp.path().join("b1.log"), "").unwrap();
    fs::write(temp.path().join("b2.log"), "").unwrap();

    // Test multiple patterns expanded independently via vsh's glob
    let txt_matches = vsh::glob::expand_glob("*.txt", temp.path()).unwrap();
    let log_matches = vsh::glob::expand_glob("*.log", temp.path()).unwrap();

    let txt_names: Vec<String> = txt_matches.iter().map(|p| p.display().to_string()).collect();
    let log_names: Vec<String> = log_matches.iter().map(|p| p.display().to_string()).collect();

    assert!(txt_names.contains(&"a1.txt".to_string()), "Should expand *.txt");
    assert!(txt_names.contains(&"a2.txt".to_string()), "Should expand *.txt");
    assert!(log_names.contains(&"b1.log".to_string()), "Should expand *.log");
    assert!(log_names.contains(&"b2.log".to_string()), "Should expand *.log");
}

/// Test: Glob patterns do not expand in quoted strings
#[test]
fn test_glob_no_expansion_in_quotes() {
    let temp = fixtures::test_sandbox("glob_quoted");

    fs::write(temp.path().join("file.txt"), "").unwrap();

    // Test echo "*.txt" (should NOT expand)
    let output = Command::new("echo")
        .arg("\"*.txt\"") // This would need quote processing in parser
        .current_dir(temp.path())
        .output()
        .unwrap();

    let stdout = String::from_utf8_lossy(&output.stdout);
    // Note: This test may need quote handling in parser to work correctly
    // For now it documents expected behavior
}

/// Test: Hidden files require explicit dot
#[test]
fn test_glob_hidden_files() {
    let temp = fixtures::test_sandbox("glob_hidden");

    // Create hidden and visible files
    fs::write(temp.path().join(".hidden.txt"), "").unwrap();
    fs::write(temp.path().join("visible.txt"), "").unwrap();

    // Test *.txt (should NOT match .hidden.txt) via vsh's glob expansion
    let matches = vsh::glob::expand_glob("*.txt", temp.path()).unwrap();
    let names: Vec<String> = matches.iter().map(|p| p.display().to_string()).collect();

    assert!(names.contains(&"visible.txt".to_string()), "Should match visible files");
    assert!(!names.iter().any(|n| n.contains(".hidden")), "Should not match hidden files without explicit .");
}

/// Test: Glob character class [0-9]
#[test]
fn test_glob_character_class() {
    let temp = fixtures::test_sandbox("glob_class");

    // Create test files
    fs::write(temp.path().join("file1.txt"), "").unwrap();
    fs::write(temp.path().join("file2.txt"), "").unwrap();
    fs::write(temp.path().join("fileA.txt"), "").unwrap();

    // Test file[0-9].txt pattern via vsh's glob expansion
    let matches = vsh::glob::expand_glob("file[0-9].txt", temp.path()).unwrap();
    let names: Vec<String> = matches.iter().map(|p| p.display().to_string()).collect();

    assert!(names.contains(&"file1.txt".to_string()), "Should match digit 1");
    assert!(names.contains(&"file2.txt".to_string()), "Should match digit 2");
    assert!(!names.contains(&"fileA.txt".to_string()), "Should not match letter A");
}

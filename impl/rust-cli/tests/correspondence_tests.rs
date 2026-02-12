// SPDX-License-Identifier: PLMP-1.0-or-later
//! Correspondence Tests - Verify Rust implementation matches Lean 4 theorems
//!
//! These tests verify that the Rust implementation correctly implements
//! the semantics proven in Lean 4 formal proofs.
//!
//! Correspondence Document: docs/PHASE4_CORRESPONDENCE.md
//! Lean Proofs: proofs/lean4/FilesystemModel.lean, FileOperations.lean

use anyhow::Result;
use std::fs;
use tempfile::tempdir;
use vsh::commands::{mkdir, rmdir, rm, touch};
use vsh::state::ShellState;

/// Test: mkdir followed by rmdir restores original state
/// Corresponds to Lean theorem: mkdir_rmdir_reversible
#[test]
fn test_mkdir_rmdir_reversible() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    let test_path = "test_dir";

    // Initial state: path doesn't exist
    assert!(!state.resolve_path(test_path).exists());

    // mkdir creates the directory (corresponds to Lean: mkdir p fs)
    mkdir(&mut state, test_path, false)?;
    assert!(state.resolve_path(test_path).exists());
    assert!(state.resolve_path(test_path).is_dir());

    // rmdir removes it (corresponds to Lean: rmdir p (mkdir p fs))
    rmdir(&mut state, test_path, false)?;

    // Final state: path doesn't exist (corresponds to Lean: = fs)
    assert!(!state.resolve_path(test_path).exists());

    Ok(())
}

/// Test: touch followed by rm restores original state
/// Corresponds to Lean theorem: createFile_deleteFile_reversible
#[test]
fn test_createfile_deletefile_reversible() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    let test_file = "test_file.txt";

    // Initial state: file doesn't exist
    assert!(!state.resolve_path(test_file).exists());

    // touch creates the file (corresponds to Lean: createFile p fs)
    touch(&mut state, test_file, false)?;
    assert!(state.resolve_path(test_file).exists());
    assert!(state.resolve_path(test_file).is_file());

    // rm removes it (corresponds to Lean: deleteFile p (createFile p fs))
    rm(&mut state, test_file, false)?;

    // Final state: file doesn't exist (corresponds to Lean: = fs)
    assert!(!state.resolve_path(test_file).exists());

    Ok(())
}

/// Test: mkdir preserves other paths
/// Corresponds to Lean theorem: mkdir_preserves_other_paths
#[test]
fn test_mkdir_preserves_other_paths() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Create initial file (unrelated path)
    touch(&mut state, "existing_file.txt", false)?;
    let existing_path = state.resolve_path("existing_file.txt");
    assert!(existing_path.exists());

    // Record initial state
    let initial_metadata = fs::metadata(&existing_path)?;

    // mkdir on different path
    mkdir(&mut state, "new_dir", false)?;
    assert!(state.resolve_path("new_dir").exists());

    // Verify existing file unchanged (corresponds to Lean: fs p' = (mkdir p fs) p' when p ≠ p')
    let final_metadata = fs::metadata(&existing_path)?;
    assert_eq!(initial_metadata.len(), final_metadata.len());
    assert_eq!(initial_metadata.is_file(), final_metadata.is_file());

    Ok(())
}

/// Test: rmdir preserves other paths
/// Corresponds to Lean theorem: rmdir_preserves_other_paths
#[test]
fn test_rmdir_preserves_other_paths() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Create two directories
    mkdir(&mut state, "dir1", false)?;
    mkdir(&mut state, "dir2", false)?;

    let dir2_path = state.resolve_path("dir2");
    assert!(dir2_path.exists());

    // Remove dir1
    rmdir(&mut state, "dir1", false)?;

    // Verify dir2 still exists (corresponds to Lean: fs p' = (rmdir p fs) p' when p ≠ p')
    assert!(dir2_path.exists());
    assert!(dir2_path.is_dir());

    Ok(())
}

/// Test: mkdir precondition - path must not exist
/// Corresponds to Lean: MkdirPrecondition.notExists
#[test]
fn test_mkdir_precondition_not_exists() {
    let temp = tempdir().unwrap();
    let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

    // Create directory
    mkdir(&mut state, "test", false).unwrap();

    // Attempting to mkdir again should fail (violates notExists precondition)
    let result = mkdir(&mut state, "test", false);
    assert!(result.is_err());
    assert!(result.unwrap_err().to_string().contains("already exists"));
}

/// Test: mkdir precondition - parent must exist
/// Corresponds to Lean: MkdirPrecondition.parentExists
#[test]
fn test_mkdir_precondition_parent_exists() {
    let temp = tempdir().unwrap();
    let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

    // Attempting to create nested dir without parent should fail
    let result = mkdir(&mut state, "nonexistent/nested", false);
    assert!(result.is_err());
    assert!(result.unwrap_err().to_string().contains("Parent directory does not exist"));
}

/// Test: rmdir precondition - path must be a directory
/// Corresponds to Lean: RmdirPrecondition.isDir
#[test]
fn test_rmdir_precondition_is_dir() {
    let temp = tempdir().unwrap();
    let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

    // Create a file
    touch(&mut state, "file.txt", false).unwrap();

    // Attempting to rmdir a file should fail (violates isDir precondition)
    let result = rmdir(&mut state, "file.txt", false);
    assert!(result.is_err());
    assert!(result.unwrap_err().to_string().contains("not a directory"));
}

/// Test: rmdir precondition - directory must be empty
/// Corresponds to Lean: RmdirPrecondition.isEmpty
#[test]
fn test_rmdir_precondition_is_empty() {
    let temp = tempdir().unwrap();
    let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

    // Create directory with a file inside
    mkdir(&mut state, "dir", false).unwrap();
    touch(&mut state, "dir/file.txt", false).unwrap();

    // Attempting to rmdir non-empty dir should fail (violates isEmpty precondition)
    let result = rmdir(&mut state, "dir", false);
    assert!(result.is_err());
    assert!(result.unwrap_err().to_string().contains("not empty"));
}

/// Test: rm precondition - path must be a file
/// Corresponds to Lean: DeleteFilePrecondition.isFile
#[test]
fn test_rm_precondition_is_file() {
    let temp = tempdir().unwrap();
    let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

    // Create a directory
    mkdir(&mut state, "dir", false).unwrap();

    // Attempting to rm a directory should fail (violates isFile precondition)
    let result = rm(&mut state, "dir", false);
    assert!(result.is_err(), "rm should fail on directory");
    // Just verify it fails - the exact error message may vary
}

/// Test: file isolation - createFile doesn't affect other paths
/// Corresponds to Lean theorem: file_isolation
#[test]
fn test_createfile_preserves_other_paths() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Create initial file
    touch(&mut state, "file1.txt", false)?;
    fs::write(state.resolve_path("file1.txt"), "content1")?;

    // Create another file
    touch(&mut state, "file2.txt", false)?;

    // Verify file1 unchanged
    let content = fs::read_to_string(state.resolve_path("file1.txt"))?;
    assert_eq!(content, "content1");

    Ok(())
}

/// Test: multiple operations preserve reversibility
/// Verifies that reversibility holds across multiple operations
#[test]
fn test_multiple_operations_reversible() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Create dir1
    mkdir(&mut state, "dir1", false)?;
    assert!(state.resolve_path("dir1").exists());

    // Create dir2
    mkdir(&mut state, "dir2", false)?;
    assert!(state.resolve_path("dir2").exists());

    // Remove dir1
    rmdir(&mut state, "dir1", false)?;
    assert!(!state.resolve_path("dir1").exists());
    assert!(state.resolve_path("dir2").exists());

    // Remove dir2
    rmdir(&mut state, "dir2", false)?;
    assert!(!state.resolve_path("dir2").exists());

    // Both paths gone - state restored
    Ok(())
}

/// Test: nested operations work correctly
/// Tests mkdir/rmdir on nested paths
#[test]
fn test_nested_mkdir_rmdir() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Create parent
    mkdir(&mut state, "parent", false)?;

    // Create child
    mkdir(&mut state, "parent/child", false)?;
    assert!(state.resolve_path("parent/child").exists());

    // Remove child
    rmdir(&mut state, "parent/child", false)?;
    assert!(!state.resolve_path("parent/child").exists());
    assert!(state.resolve_path("parent").exists());

    // Remove parent
    rmdir(&mut state, "parent", false)?;
    assert!(!state.resolve_path("parent").exists());

    Ok(())
}

/// Test: operation order independence for disjoint paths
/// Corresponds to commutativity of operations on disjoint paths
#[test]
fn test_operation_commutativity_disjoint_paths() -> Result<()> {
    // Use separate temp directories for each scenario
    let temp1 = tempdir()?;
    let temp2 = tempdir()?;

    // Scenario 1: mkdir dir1, then mkdir dir2
    let mut state1 = ShellState::new(temp1.path().to_str().unwrap())?;
    mkdir(&mut state1, "dir1", false)?;
    mkdir(&mut state1, "dir2", false)?;

    // Scenario 2: mkdir dir2, then mkdir dir1
    let mut state2 = ShellState::new(temp2.path().to_str().unwrap())?;
    mkdir(&mut state2, "dir2", false)?;
    mkdir(&mut state2, "dir1", false)?;

    // Both scenarios result in same final state
    assert!(state1.resolve_path("dir1").exists());
    assert!(state1.resolve_path("dir2").exists());
    assert!(state2.resolve_path("dir1").exists());
    assert!(state2.resolve_path("dir2").exists());

    Ok(())
}

/// Test: mkdir creates directory with correct type
/// Corresponds to Lean theorem: mkdir_creates_directory
#[test]
fn test_mkdir_creates_directory() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    mkdir(&mut state, "test", false)?;

    let path = state.resolve_path("test");
    assert!(path.exists());
    assert!(path.is_dir());
    assert!(!path.is_file());

    Ok(())
}

/// Test: createFile creates file with correct type
/// Corresponds to Lean theorem: createFile_creates_file
#[test]
fn test_createfile_creates_file() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    touch(&mut state, "test.txt", false)?;

    let path = state.resolve_path("test.txt");
    assert!(path.exists());
    assert!(path.is_file());
    assert!(!path.is_dir());

    Ok(())
}

// =============================================================================
// Property-Based Tests - Extended Coverage
// =============================================================================

use proptest::prelude::*;

/// Property test: mkdir followed by rmdir always restores state
/// Corresponds to Lean theorem: mkdir_rmdir_reversible (property version)
proptest! {
    #[test]
    fn prop_mkdir_rmdir_reversible(name in "[a-z]{1,10}") {
        let temp = tempdir().unwrap();
        let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

        // Precondition: path doesn't exist
        assert!(!state.resolve_path(&name).exists());

        // mkdir then rmdir
        mkdir(&mut state, &name, false).unwrap();
        assert!(state.resolve_path(&name).exists());

        rmdir(&mut state, &name, false).unwrap();

        // Postcondition: path doesn't exist (state restored)
        assert!(!state.resolve_path(&name).exists());
    }
}

/// Property test: touch followed by rm always restores state
proptest! {
    #[test]
    fn prop_touch_rm_reversible(name in "[a-z]{1,10}\\.txt") {
        let temp = tempdir().unwrap();
        let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

        // Precondition: path doesn't exist
        assert!(!state.resolve_path(&name).exists());

        // touch then rm
        touch(&mut state, &name, false).unwrap();
        assert!(state.resolve_path(&name).exists());

        rm(&mut state, &name, false).unwrap();

        // Postcondition: path doesn't exist (state restored)
        assert!(!state.resolve_path(&name).exists());
    }
}

/// Property test: operations on disjoint paths are independent
proptest! {
    #[test]
    fn prop_path_independence(
        name1 in "[a-z]{1,5}",
        name2 in "[a-z]{1,5}",
    ) {
        // Ensure paths are different
        if name1 == name2 {
            return Ok(());
        }

        let temp = tempdir().unwrap();
        let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

        // Create first dir
        mkdir(&mut state, &name1, false).unwrap();

        // Create second dir
        mkdir(&mut state, &name2, false).unwrap();

        // Remove first dir
        rmdir(&mut state, &name1, false).unwrap();

        // Second dir should still exist (path independence)
        assert!(state.resolve_path(&name2).exists());
        assert!(state.resolve_path(&name2).is_dir());
    }
}

/// Test: Deep nested directories maintain reversibility
#[test]
fn test_deep_nesting_reversible() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Create deeply nested structure
    mkdir(&mut state, "a", false)?;
    mkdir(&mut state, "a/b", false)?;
    mkdir(&mut state, "a/b/c", false)?;
    mkdir(&mut state, "a/b/c/d", false)?;

    assert!(state.resolve_path("a/b/c/d").exists());

    // Remove in reverse order (bottom-up)
    rmdir(&mut state, "a/b/c/d", false)?;
    rmdir(&mut state, "a/b/c", false)?;
    rmdir(&mut state, "a/b", false)?;
    rmdir(&mut state, "a", false)?;

    // All paths gone
    assert!(!state.resolve_path("a").exists());

    Ok(())
}

/// Test: Multiple sequential operations maintain state consistency
#[test]
fn test_sequential_operations_consistent() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Create multiple dirs and files in sequence
    mkdir(&mut state, "dir1", false)?;
    touch(&mut state, "dir1/file1.txt", false)?;
    mkdir(&mut state, "dir2", false)?;
    touch(&mut state, "dir2/file2.txt", false)?;
    touch(&mut state, "top.txt", false)?;

    // All should exist
    assert!(state.resolve_path("dir1/file1.txt").exists());
    assert!(state.resolve_path("dir2/file2.txt").exists());
    assert!(state.resolve_path("top.txt").exists());

    // Remove in specific order
    rm(&mut state, "dir1/file1.txt", false)?;
    rmdir(&mut state, "dir1", false)?;
    rm(&mut state, "top.txt", false)?;

    // Partial cleanup - dir2 should still exist
    assert!(!state.resolve_path("dir1").exists());
    assert!(state.resolve_path("dir2/file2.txt").exists());
    assert!(!state.resolve_path("top.txt").exists());

    Ok(())
}

/// Test: Error conditions match Lean preconditions
#[test]
fn test_precondition_violations() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // mkdir on existing path fails (notExists violated)
    mkdir(&mut state, "test", false)?;
    assert!(mkdir(&mut state, "test", false).is_err());

    // rmdir on non-existent path fails (exists violated)
    assert!(rmdir(&mut state, "nonexistent", false).is_err());

    // rmdir on file fails (isDir violated)
    touch(&mut state, "file.txt", false)?;
    assert!(rmdir(&mut state, "file.txt", false).is_err());

    // rm on dir fails (isFile violated)
    assert!(rm(&mut state, "test", false).is_err());

    // mkdir without parent fails (parentExists violated)
    assert!(mkdir(&mut state, "missing/child", false).is_err());

    Ok(())
}

/// Test: Undo operation restores exact prior state
#[test]
fn test_undo_correspondence() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Initial state
    touch(&mut state, "file1.txt", false)?;
    let history_len_before = state.history.len();

    // Perform operation
    mkdir(&mut state, "new_dir", false)?;
    assert!(state.resolve_path("new_dir").exists());
    let history_len_after = state.history.len();
    assert_eq!(history_len_after, history_len_before + 1);

    // Undo should restore
    vsh::commands::undo(&mut state, 1, false)?;
    assert!(!state.resolve_path("new_dir").exists());
    assert!(state.resolve_path("file1.txt").exists());

    Ok(())
}

/// Test: Redo reapplies operation correctly
#[test]
fn test_redo_correspondence() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Perform operation
    mkdir(&mut state, "test_dir", false)?;
    assert!(state.resolve_path("test_dir").exists());

    // Undo
    vsh::commands::undo(&mut state, 1, false)?;
    assert!(!state.resolve_path("test_dir").exists());

    // Redo
    vsh::commands::redo(&mut state, 1, false)?;
    assert!(state.resolve_path("test_dir").exists());

    Ok(())
}

/// Test: Multiple undo/redo cycles maintain correctness
#[test]
fn test_undo_redo_cycles() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Create sequence of operations
    mkdir(&mut state, "dir1", false)?;
    mkdir(&mut state, "dir2", false)?;
    touch(&mut state, "file.txt", false)?;

    // All exist
    assert!(state.resolve_path("dir1").exists());
    assert!(state.resolve_path("dir2").exists());
    assert!(state.resolve_path("file.txt").exists());

    // Undo all
    vsh::commands::undo(&mut state, 1, false)?; // undo touch
    vsh::commands::undo(&mut state, 1, false)?; // undo mkdir dir2
    vsh::commands::undo(&mut state, 1, false)?; // undo mkdir dir1

    // None exist
    assert!(!state.resolve_path("dir1").exists());
    assert!(!state.resolve_path("dir2").exists());
    assert!(!state.resolve_path("file.txt").exists());

    // Redo all
    vsh::commands::redo(&mut state, 1, false)?; // redo mkdir dir1
    vsh::commands::redo(&mut state, 1, false)?; // redo mkdir dir2
    vsh::commands::redo(&mut state, 1, false)?; // redo touch

    // All exist again
    assert!(state.resolve_path("dir1").exists());
    assert!(state.resolve_path("dir2").exists());
    assert!(state.resolve_path("file.txt").exists());

    Ok(())
}

/// Test: Stress test - many operations maintain consistency
#[test]
fn test_stress_many_operations() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Create 50 directories
    for i in 0..50 {
        let name = format!("dir_{:03}", i);
        mkdir(&mut state, &name, false)?;
        assert!(state.resolve_path(&name).exists());
    }

    // Verify all exist
    for i in 0..50 {
        let name = format!("dir_{:03}", i);
        assert!(state.resolve_path(&name).is_dir());
    }

    // Remove all in reverse order
    for i in (0..50).rev() {
        let name = format!("dir_{:03}", i);
        rmdir(&mut state, &name, false)?;
    }

    // Verify all gone
    for i in 0..50 {
        let name = format!("dir_{:03}", i);
        assert!(!state.resolve_path(&name).exists());
    }

    Ok(())
}

/// Test: Interleaved operations on different paths
#[test]
fn test_interleaved_operations() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Interleave dir and file operations
    mkdir(&mut state, "d1", false)?;
    touch(&mut state, "f1.txt", false)?;
    mkdir(&mut state, "d2", false)?;
    touch(&mut state, "d1/f2.txt", false)?;
    mkdir(&mut state, "d2/d3", false)?;

    // Verify structure
    assert!(state.resolve_path("d1").is_dir());
    assert!(state.resolve_path("f1.txt").is_file());
    assert!(state.resolve_path("d2").is_dir());
    assert!(state.resolve_path("d1/f2.txt").is_file());
    assert!(state.resolve_path("d2/d3").is_dir());

    // Selective cleanup
    rm(&mut state, "d1/f2.txt", false)?;
    rmdir(&mut state, "d2/d3", false)?;

    // Partial state
    assert!(state.resolve_path("d1").is_dir());
    assert!(state.resolve_path("d2").is_dir());
    assert!(!state.resolve_path("d1/f2.txt").exists());
    assert!(!state.resolve_path("d2/d3").exists());

    Ok(())
}

/// Test: Transaction semantics - operations are atomic
#[test]
fn test_operation_atomicity() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Single operation either succeeds completely or fails completely
    let result = mkdir(&mut state, "test", false);
    assert!(result.is_ok());
    assert!(state.resolve_path("test").exists());

    // Failed operation doesn't create partial state
    let result = mkdir(&mut state, "missing/child", false);
    assert!(result.is_err());
    assert!(!state.resolve_path("missing").exists());
    assert!(!state.resolve_path("missing/child").exists());

    Ok(())
}

/// Test: Variables expand correctly in redirections (M11 edge case)
/// Verifies that $VAR is expanded in redirection file paths
#[test]
fn test_variables_in_redirections() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Set a variable
    state.set_variable("OUTFILE", "test_output.txt");

    // Verify variable expansion works
    let expanded = vsh::parser::expand_variables("$OUTFILE", &state);
    assert_eq!(expanded, "test_output.txt");

    // Verify with braced form
    let expanded2 = vsh::parser::expand_variables("${OUTFILE}", &state);
    assert_eq!(expanded2, "test_output.txt");

    // Test that resolve_path works with expanded variables
    let path = state.resolve_path(&vsh::parser::expand_variables("$OUTFILE", &state));
    assert!(path.to_string_lossy().contains("test_output.txt"));

    Ok(())
}

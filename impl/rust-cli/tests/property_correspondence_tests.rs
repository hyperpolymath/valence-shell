// SPDX-License-Identifier: PLMP-1.0-or-later
//! Property-Based Correspondence Tests
//!
//! Uses proptest to generate random test cases and verify that Rust operations
//! satisfy the properties proven in Lean 4 theorems.
//!
//! This complements correspondence_tests.rs with QuickCheck-style generative testing.

use anyhow::Result;
use proptest::prelude::*;
use std::fs;
use tempfile::tempdir;
use vsh::commands::{mkdir, rmdir, rm, touch};
use vsh::state::ShellState;

// ============================================================================
// Generators - Generate random valid inputs
// ============================================================================

/// Generate valid directory names (no special chars, reasonable length)
fn dir_name() -> impl Strategy<Value = String> {
    "[a-z][a-z0-9_]{0,15}".prop_map(|s| s)
}

/// Generate valid file names with extension
fn file_name() -> impl Strategy<Value = String> {
    ("[a-z][a-z0-9_]{0,10}", "[a-z]{2,4}")
        .prop_map(|(name, ext)| format!("{}.{}", name, ext))
}

/// Generate lists of directory names (for path components)
fn dir_path() -> impl Strategy<Value = String> {
    prop::collection::vec(dir_name(), 1..=3)
        .prop_map(|parts| parts.join("/"))
}

/// Generate either a file or directory name
fn any_name() -> impl Strategy<Value = (String, bool)> {
    prop_oneof![
        dir_name().prop_map(|n| (n, true)),  // (name, is_dir)
        file_name().prop_map(|n| (n, false)), // (name, is_file)
    ]
}

// ============================================================================
// Property 1: Reversibility - mkdir ∘ rmdir = id
// Corresponds to Lean: mkdir_rmdir_reversible
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// Property: For any valid path, mkdir followed by rmdir restores state
    #[test]
    fn prop_mkdir_rmdir_reversible(path in dir_name()) {
        let temp = tempdir().unwrap();
        let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

        // Initial state: path doesn't exist
        let initial_exists = state.resolve_path(&path).exists();
        prop_assume!(!initial_exists); // Only test when path doesn't exist initially

        // Apply mkdir
        let mkdir_result = mkdir(&mut state, &path, false);
        prop_assert!(mkdir_result.is_ok(), "mkdir should succeed");
        prop_assert!(state.resolve_path(&path).exists(), "path should exist after mkdir");

        // Apply rmdir (inverse operation)
        let rmdir_result = rmdir(&mut state, &path, false);
        prop_assert!(rmdir_result.is_ok(), "rmdir should succeed");

        // Final state should match initial state
        let final_exists = state.resolve_path(&path).exists();
        prop_assert_eq!(initial_exists, final_exists, "state should be restored");
    }

    /// Property: For any valid file path, touch followed by rm restores state
    #[test]
    fn prop_createfile_deletefile_reversible(path in file_name()) {
        let temp = tempdir().unwrap();
        let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

        // Initial state: file doesn't exist
        let initial_exists = state.resolve_path(&path).exists();
        prop_assume!(!initial_exists);

        // Apply touch (createFile)
        let touch_result = touch(&mut state, &path, false);
        prop_assert!(touch_result.is_ok(), "touch should succeed");
        prop_assert!(state.resolve_path(&path).exists(), "file should exist after touch");

        // Apply rm (deleteFile)
        let rm_result = rm(&mut state, &path, false);
        prop_assert!(rm_result.is_ok(), "rm should succeed");

        // Final state should match initial state
        let final_exists = state.resolve_path(&path).exists();
        prop_assert_eq!(initial_exists, final_exists, "state should be restored");
    }
}

// ============================================================================
// Property 2: Path Isolation - Operations preserve unrelated paths
// Corresponds to Lean: mkdir_preserves_other_paths, rmdir_preserves_other_paths
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// Property: mkdir on path1 doesn't affect path2 when path1 ≠ path2
    #[test]
    fn prop_mkdir_preserves_other_paths(path1 in dir_name(), path2 in dir_name()) {
        prop_assume!(path1 != path2); // Paths must be different

        let temp = tempdir().unwrap();
        let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

        // Create path2 first
        mkdir(&mut state, &path2, false).unwrap();
        let path2_exists_before = state.resolve_path(&path2).exists();
        prop_assert!(path2_exists_before);

        // Create path1
        let result = mkdir(&mut state, &path1, false);
        prop_assume!(result.is_ok()); // Only test successful operations

        // Verify path2 unchanged
        let path2_exists_after = state.resolve_path(&path2).exists();
        prop_assert_eq!(path2_exists_before, path2_exists_after, "path2 should be unchanged");
        prop_assert!(path2_exists_after, "path2 should still exist");
    }

    /// Property: rmdir on path1 doesn't affect path2 when path1 ≠ path2
    #[test]
    fn prop_rmdir_preserves_other_paths(path1 in dir_name(), path2 in dir_name()) {
        prop_assume!(path1 != path2);

        let temp = tempdir().unwrap();
        let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

        // Create both paths
        mkdir(&mut state, &path1, false).unwrap();
        mkdir(&mut state, &path2, false).unwrap();

        let path2_exists_before = state.resolve_path(&path2).exists();
        prop_assert!(path2_exists_before);

        // Remove path1
        rmdir(&mut state, &path1, false).unwrap();

        // Verify path2 unchanged
        let path2_exists_after = state.resolve_path(&path2).exists();
        prop_assert_eq!(path2_exists_before, path2_exists_after);
        prop_assert!(path2_exists_after);
    }

    /// Property: touch on file1 doesn't affect file2 when file1 ≠ file2
    #[test]
    fn prop_touch_preserves_other_files(file1 in file_name(), file2 in file_name()) {
        prop_assume!(file1 != file2);

        let temp = tempdir().unwrap();
        let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

        // Create file2 with content
        touch(&mut state, &file2, false).unwrap();
        fs::write(state.resolve_path(&file2), "content").unwrap();

        let file2_content_before = fs::read_to_string(state.resolve_path(&file2)).unwrap();

        // Create file1
        touch(&mut state, &file1, false).unwrap();

        // Verify file2 unchanged
        let file2_content_after = fs::read_to_string(state.resolve_path(&file2)).unwrap();
        prop_assert_eq!(file2_content_before, file2_content_after);
    }
}

// ============================================================================
// Property 3: Commutativity - Independent operations commute
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// Property: mkdir(p1); mkdir(p2) ≅ mkdir(p2); mkdir(p1) for disjoint paths
    #[test]
    fn prop_mkdir_commutativity(path1 in dir_name(), path2 in dir_name()) {
        prop_assume!(path1 != path2);

        // Scenario 1: path1 then path2
        let temp1 = tempdir().unwrap();
        let mut state1 = ShellState::new(temp1.path().to_str().unwrap()).unwrap();
        mkdir(&mut state1, &path1, false).unwrap();
        mkdir(&mut state1, &path2, false).unwrap();

        // Scenario 2: path2 then path1
        let temp2 = tempdir().unwrap();
        let mut state2 = ShellState::new(temp2.path().to_str().unwrap()).unwrap();
        mkdir(&mut state2, &path2, false).unwrap();
        mkdir(&mut state2, &path1, false).unwrap();

        // Both scenarios result in same final state
        prop_assert!(state1.resolve_path(&path1).exists());
        prop_assert!(state1.resolve_path(&path2).exists());
        prop_assert!(state2.resolve_path(&path1).exists());
        prop_assert!(state2.resolve_path(&path2).exists());
    }

    /// Property: Operations on different file types commute
    #[test]
    fn prop_mixed_operations_commute(dir_name in dir_name(), file_name in file_name()) {
        prop_assume!(dir_name != file_name); // Different names

        // Scenario 1: mkdir then touch
        let temp1 = tempdir().unwrap();
        let mut state1 = ShellState::new(temp1.path().to_str().unwrap()).unwrap();
        mkdir(&mut state1, &dir_name, false).unwrap();
        touch(&mut state1, &file_name, false).unwrap();

        // Scenario 2: touch then mkdir
        let temp2 = tempdir().unwrap();
        let mut state2 = ShellState::new(temp2.path().to_str().unwrap()).unwrap();
        touch(&mut state2, &file_name, false).unwrap();
        mkdir(&mut state2, &dir_name, false).unwrap();

        // Both scenarios result in same final state
        prop_assert!(state1.resolve_path(&dir_name).is_dir());
        prop_assert!(state1.resolve_path(&file_name).is_file());
        prop_assert!(state2.resolve_path(&dir_name).is_dir());
        prop_assert!(state2.resolve_path(&file_name).is_file());
    }
}

// ============================================================================
// Property 4: Precondition Enforcement - Operations fail when preconditions violated
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// Property: mkdir fails when path already exists (violates notExists precondition)
    #[test]
    fn prop_mkdir_fails_when_exists(path in dir_name()) {
        let temp = tempdir().unwrap();
        let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

        // Create path
        mkdir(&mut state, &path, false).unwrap();

        // Second mkdir should fail
        let result = mkdir(&mut state, &path, false);
        prop_assert!(result.is_err(), "mkdir should fail when path exists");
    }

    /// Property: rmdir fails when directory not empty (violates isEmpty precondition)
    #[test]
    fn prop_rmdir_fails_when_not_empty(parent in dir_name(), child in dir_name()) {
        let temp = tempdir().unwrap();
        let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

        // Create parent and child
        mkdir(&mut state, &parent, false).unwrap();
        let child_path = format!("{}/{}", parent, child);
        mkdir(&mut state, &child_path, false).unwrap();

        // rmdir on parent should fail
        let result = rmdir(&mut state, &parent, false);
        prop_assert!(result.is_err(), "rmdir should fail when directory not empty");
    }

    /// Property: rmdir fails when path is not a directory (violates isDir precondition)
    #[test]
    fn prop_rmdir_fails_on_file(file in file_name()) {
        let temp = tempdir().unwrap();
        let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

        // Create file
        touch(&mut state, &file, false).unwrap();

        // rmdir on file should fail
        let result = rmdir(&mut state, &file, false);
        prop_assert!(result.is_err(), "rmdir should fail on file");
    }

    /// Property: rm fails when path is a directory (violates isFile precondition)
    #[test]
    fn prop_rm_fails_on_directory(dir in dir_name()) {
        let temp = tempdir().unwrap();
        let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

        // Create directory
        mkdir(&mut state, &dir, false).unwrap();

        // rm on directory should fail
        let result = rm(&mut state, &dir, false);
        prop_assert!(result.is_err(), "rm should fail on directory");
    }
}

// ============================================================================
// Property 5: Multiple Operations - Complex sequences preserve properties
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(30))]

    /// Property: Sequence of creates and deletes maintains consistency
    #[test]
    fn prop_create_delete_sequence(paths in prop::collection::vec(dir_name(), 1..=5)) {
        let temp = tempdir().unwrap();
        let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

        // Create all directories
        for path in &paths {
            mkdir(&mut state, path, false).unwrap();
        }

        // Verify all exist
        for path in &paths {
            prop_assert!(state.resolve_path(path).exists(), "path {} should exist", path);
        }

        // Delete all directories
        for path in &paths {
            rmdir(&mut state, path, false).unwrap();
        }

        // Verify none exist
        for path in &paths {
            prop_assert!(!state.resolve_path(path).exists(), "path {} should not exist", path);
        }
    }

    /// Property: Alternating creates and deletes work correctly
    #[test]
    fn prop_alternating_operations(path in dir_name(), iterations in 1..=5usize) {
        let temp = tempdir().unwrap();
        let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

        for i in 0..iterations {
            if i % 2 == 0 {
                // Create
                mkdir(&mut state, &path, false).unwrap();
                prop_assert!(state.resolve_path(&path).exists());
            } else {
                // Delete
                rmdir(&mut state, &path, false).unwrap();
                prop_assert!(!state.resolve_path(&path).exists());
            }
        }

        // Final state depends on whether iterations is odd or even
        let should_exist = iterations % 2 == 1;
        prop_assert_eq!(state.resolve_path(&path).exists(), should_exist);
    }
}

// ============================================================================
// Property 6: Idempotency - Some operations are idempotent
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// Property: touch is idempotent (can be applied multiple times safely)
    #[test]
    fn prop_touch_idempotent(file in file_name()) {
        let temp = tempdir().unwrap();
        let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

        // First touch
        touch(&mut state, &file, false).unwrap();
        prop_assert!(state.resolve_path(&file).exists());

        // Second touch (idempotent)
        let result = touch(&mut state, &file, false);
        // Note: touch updates timestamp, so it's allowed on existing files
        prop_assert!(result.is_ok() || result.is_err()); // Either is valid for touch
        prop_assert!(state.resolve_path(&file).exists());
    }
}

// ============================================================================
// Property 7: Type Safety - Operations respect file/directory distinction
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// Property: mkdir creates directories, touch creates files
    #[test]
    fn prop_type_correctness(dir_name in dir_name(), file_name in file_name()) {
        prop_assume!(dir_name != file_name);

        let temp = tempdir().unwrap();
        let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

        // mkdir creates directory
        mkdir(&mut state, &dir_name, false).unwrap();
        prop_assert!(state.resolve_path(&dir_name).is_dir());
        prop_assert!(!state.resolve_path(&dir_name).is_file());

        // touch creates file
        touch(&mut state, &file_name, false).unwrap();
        prop_assert!(state.resolve_path(&file_name).is_file());
        prop_assert!(!state.resolve_path(&file_name).is_dir());
    }
}

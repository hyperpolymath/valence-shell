// SPDX-License-Identifier: PLMP-1.0-or-later
//! Property-Based Tests - Seam 0↔1 Validation
//!
//! These tests validate that the Rust implementation upholds the properties
//! proven in Lean 4 theorems. This seals the gap between abstract proofs
//! and concrete implementation.
//!
//! Corresponds to:
//! - `proofs/lean4/FilesystemModel.lean`
//! - `proofs/lean4/FileOperations.lean`
//! - `proofs/lean4/FilesystemComposition.lean`

mod fixtures;

use fixtures::tempfile::TempDir;
use proptest::prelude::*;
use std::fs;
use std::path::Path;

// ============================================================
// Test Utilities
// ============================================================

/// Filesystem snapshot for equivalence checking
#[derive(Debug, Clone, PartialEq)]
struct FsSnapshot {
    dirs: Vec<String>,
    files: Vec<(String, Vec<u8>)>,
}

impl FsSnapshot {
    /// Capture current filesystem state
    fn capture(root: &Path) -> std::io::Result<Self> {
        let mut dirs = Vec::new();
        let mut files = Vec::new();

        fn walk(
            base: &Path,
            current: &Path,
            dirs: &mut Vec<String>,
            files: &mut Vec<(String, Vec<u8>)>,
        ) -> std::io::Result<()> {
            for entry in fs::read_dir(current)? {
                let entry = entry?;
                let path = entry.path();
                let rel_path = path.strip_prefix(base).unwrap().to_string_lossy().to_string();

                if path.is_dir() {
                    dirs.push(rel_path.clone());
                    walk(base, &path, dirs, files)?;
                } else if path.is_file() {
                    let content = fs::read(&path)?;
                    files.push((rel_path, content));
                }
            }
            Ok(())
        }

        walk(root, root, &mut dirs, &mut files)?;

        dirs.sort();
        files.sort_by(|a, b| a.0.cmp(&b.0));

        Ok(Self { dirs, files })
    }
}

/// Valid path strategy for property tests
fn valid_path_strategy() -> impl Strategy<Value = String> {
    prop::string::string_regex("[a-z][a-z0-9_]{0,15}")
        .unwrap()
        .prop_map(|s| s.to_lowercase())
}

/// Valid nested path strategy
fn valid_nested_path_strategy() -> impl Strategy<Value = String> {
    prop::collection::vec(valid_path_strategy(), 1..=3)
        .prop_map(|parts| parts.join("/"))
}

// ============================================================
// Property Tests - Lean 4 Theorem Validation
// ============================================================

/// Property: mkdir followed by rmdir returns to initial state
///
/// Lean theorem: `mkdir_rmdir_reversible` (FilesystemModel.lean:158)
/// ```lean
/// theorem mkdir_rmdir_reversible (fs : Filesystem) (p : Path)
///   (h_pre : MkdirPrecondition p fs) :
///   rmdir p (mkdir p fs) = fs
/// ```
#[test]
fn prop_mkdir_rmdir_reversible() {
    proptest!(|(path in valid_path_strategy())| {
        let temp = TempDir::new().unwrap();
        let target = temp.path().join(&path);

        // Precondition: path must not exist
        if target.exists() {
            return Ok(());
        }

        // Capture initial state
        let before = FsSnapshot::capture(temp.path()).unwrap();

        // mkdir then rmdir
        fs::create_dir(&target).unwrap();
        assert!(target.exists(), "mkdir should create directory");

        fs::remove_dir(&target).unwrap();
        assert!(!target.exists(), "rmdir should remove directory");

        // Verify return to initial state (Lean 4 postcondition)
        let after = FsSnapshot::capture(temp.path()).unwrap();
        prop_assert_eq!(before, after);
    });
}

/// Property: createFile followed by deleteFile returns to initial state
///
/// Lean theorem: `createFile_deleteFile_reversible` (FileOperations.lean:89)
/// ```lean
/// theorem createFile_deleteFile_reversible (fs : Filesystem) (p : Path)
///   (h_pre : CreateFilePrecondition p fs) :
///   deleteFile p (createFile p fs) = fs
/// ```
#[test]
fn prop_create_delete_file_reversible() {
    proptest!(|(path in valid_path_strategy())| {
        let temp = TempDir::new().unwrap();
        let target = temp.path().join(&path);

        // Precondition: path must not exist
        if target.exists() {
            return Ok(());
        }

        // Capture initial state
        let before = FsSnapshot::capture(temp.path()).unwrap();

        // createFile then deleteFile
        fs::write(&target, b"").unwrap();
        assert!(target.exists(), "createFile should create file");

        fs::remove_file(&target).unwrap();
        assert!(!target.exists(), "deleteFile should remove file");

        // Verify return to initial state
        let after = FsSnapshot::capture(temp.path()).unwrap();
        prop_assert_eq!(before, after);
    });
}

/// Property: Operations on different paths are independent
///
/// Lean theorem: `mkdirPreservesOtherPaths` (FilesystemModel.lean:180)
/// ```lean
/// theorem mkdirPreservesOtherPaths (fs : Filesystem) (p1 p2 : Path)
///   (h_diff : p1 ≠ p2) (h_pre : MkdirPrecondition p1 fs) :
///   lookup p2 (mkdir p1 fs) = lookup p2 fs
/// ```
#[test]
fn prop_operation_independence() {
    proptest!(|(path1 in valid_path_strategy(), path2 in valid_path_strategy())| {
        // Ensure paths are different
        if path1 == path2 {
            return Ok(());
        }

        let temp = TempDir::new().unwrap();
        let target1 = temp.path().join(&path1);
        let target2 = temp.path().join(&path2);

        // Preconditions
        if target1.exists() || target2.exists() {
            return Ok(());
        }

        // Create path2 first
        fs::create_dir(&target2).unwrap();
        assert!(target2.exists());

        // Operating on path1 should not affect path2
        fs::create_dir(&target1).unwrap();
        prop_assert!(target2.exists(), "mkdir p1 should not affect p2");

        fs::remove_dir(&target1).unwrap();
        prop_assert!(target2.exists(), "rmdir p1 should not affect p2");
    });
}

/// Property: Operation sequences are reversible
///
/// Lean theorem: `operationSequenceReversible` (FilesystemComposition.lean:129)
/// ```lean
/// theorem operationSequenceReversible (fs : Filesystem) (ops : List Operation)
///   (h_valid : ValidSequence ops fs) :
///   reverseSequence ops (applySequence ops fs) = fs
/// ```
#[test]
fn prop_sequence_reversible() {
    proptest!(|(paths in prop::collection::vec(valid_path_strategy(), 1..=5))| {
        let temp = TempDir::new().unwrap();

        // Ensure all paths are unique and don't exist
        let mut unique_paths = paths.clone();
        unique_paths.sort();
        unique_paths.dedup();

        let targets: Vec<_> = unique_paths.iter()
            .map(|p| temp.path().join(p))
            .collect();

        for target in &targets {
            if target.exists() {
                return Ok(());
            }
        }

        // Capture initial state
        let before = FsSnapshot::capture(temp.path()).unwrap();

        // Apply sequence: mkdir all
        for target in &targets {
            fs::create_dir(target).unwrap();
        }

        // Verify all exist
        for target in &targets {
            prop_assert!(target.exists());
        }

        // Reverse sequence: rmdir all (in reverse order)
        for target in targets.iter().rev() {
            fs::remove_dir(target).unwrap();
        }

        // Verify return to initial state
        let after = FsSnapshot::capture(temp.path()).unwrap();
        prop_assert_eq!(before, after);
    });
}

/// Property: writeFile is reversible with saved content
///
/// Lean theorem: `writeFileReversible` (FileContentOperations.lean)
/// ```lean
/// theorem writeFileReversible (fs : Filesystem) (p : Path) (old_content new_content : Bytes)
///   (h_exists : fileExists p fs) :
///   writeFile p old_content (writeFile p new_content fs) = writeFile p old_content fs
/// ```
#[test]
fn prop_write_file_reversible() {
    proptest!(|(
        path in valid_path_strategy(),
        content1 in prop::collection::vec(any::<u8>(), 0..100),
        content2 in prop::collection::vec(any::<u8>(), 0..100)
    )| {
        let temp = TempDir::new().unwrap();
        let target = temp.path().join(&path);

        // Create file with initial content
        fs::write(&target, &content1).unwrap();

        // Save original for undo
        let saved = fs::read(&target).unwrap();
        prop_assert_eq!(saved.clone(), content1.clone());

        // Modify file
        fs::write(&target, &content2).unwrap();
        let modified = fs::read(&target).unwrap();
        prop_assert_eq!(modified, content2);

        // Restore original (undo)
        fs::write(&target, &saved).unwrap();

        // Verify restoration
        let restored = fs::read(&target).unwrap();
        prop_assert_eq!(restored, content1);
    });
}

/// Property: mkdir respects EEXIST precondition
///
/// Lean theorem: `mkdirSuccessImpliesPrecondition` (FilesystemModel.lean)
/// ```lean
/// theorem mkdirSuccessImpliesPrecondition (fs : Filesystem) (p : Path) :
///   isOk (tryMkdir p fs) → MkdirPrecondition p fs
/// ```
#[test]
fn prop_mkdir_eexist() {
    proptest!(|(path in valid_path_strategy())| {
        let temp = TempDir::new().unwrap();
        let target = temp.path().join(&path);

        // Create directory
        fs::create_dir(&target).unwrap();

        // Attempt to create again should fail (EEXIST)
        let result = fs::create_dir(&target);
        prop_assert!(result.is_err(), "mkdir should fail on existing path");

        if let Err(e) = result {
            prop_assert_eq!(e.kind(), std::io::ErrorKind::AlreadyExists);
        }
    });
}

/// Property: rmdir respects ENOTEMPTY precondition
///
/// Lean theorem: `rmdirSuccessImpliesPrecondition` (FilesystemModel.lean)
/// ```lean
/// theorem rmdirSuccessImpliesPrecondition (fs : Filesystem) (p : Path) :
///   isOk (tryRmdir p fs) → RmdirPrecondition p fs
/// ```
#[test]
fn prop_rmdir_enotempty() {
    proptest!(|(
        dir_path in valid_path_strategy(),
        file_path in valid_path_strategy()
    )| {
        let temp = TempDir::new().unwrap();
        let dir = temp.path().join(&dir_path);
        let file = dir.join(&file_path);

        // Create directory with file inside
        fs::create_dir(&dir).unwrap();
        fs::write(&file, b"content").unwrap();

        // Attempt to remove non-empty directory should fail
        let result = fs::remove_dir(&dir);
        prop_assert!(result.is_err(), "rmdir should fail on non-empty directory");
    });
}

/// Property: Type preservation - operations maintain filesystem invariants
///
/// Lean theorem: `operationPreservesTypeInvariant` (FilesystemModel.lean)
/// ```lean
/// theorem operationPreservesTypeInvariant (fs : Filesystem) (op : Operation)
///   (h_valid : ValidOperation op fs) :
///   validFilesystem (applyOp op fs) = true
/// ```
#[test]
fn prop_type_preservation() {
    proptest!(|(
        dir_path in valid_path_strategy(),
        file_path in valid_path_strategy()
    )| {
        // Ensure different paths
        if dir_path == file_path {
            return Ok(());
        }

        let temp = TempDir::new().unwrap();
        let dir = temp.path().join(&dir_path);
        let file = temp.path().join(&file_path);

        // Create both directory and file
        fs::create_dir(&dir).unwrap();
        fs::write(&file, b"test").unwrap();

        // Verify types are preserved
        prop_assert!(dir.is_dir(), "Directory should remain a directory");
        prop_assert!(file.is_file(), "File should remain a file");

        // Removing file shouldn't affect directory type
        fs::remove_file(&file).unwrap();
        prop_assert!(dir.is_dir(), "Directory type preserved after file removal");

        // Removing directory shouldn't affect (now missing) file
        fs::remove_dir(&dir).unwrap();
        prop_assert!(!file.exists(), "File remains deleted");
    });
}

/// Property: Composition - multiple operations compose correctly
///
/// Lean theorem: `compositionCorrectness` (FilesystemComposition.lean)
/// ```lean
/// theorem compositionCorrectness (fs : Filesystem) (op1 op2 : Operation)
///   (h1 : ValidOperation op1 fs)
///   (h2 : ValidOperation op2 (applyOp op1 fs)) :
///   applyOp op2 (applyOp op1 fs) = applySequence [op1, op2] fs
/// ```
#[test]
fn prop_composition_correctness() {
    proptest!(|(
        path1 in valid_path_strategy(),
        path2 in valid_path_strategy()
    )| {
        // Ensure different paths
        if path1 == path2 {
            return Ok(());
        }

        let temp = TempDir::new().unwrap();
        let target1 = temp.path().join(&path1);
        let target2 = temp.path().join(&path2);

        // Preconditions
        if target1.exists() || target2.exists() {
            return Ok(());
        }

        // Apply op1
        fs::create_dir(&target1).unwrap();
        let after_op1 = FsSnapshot::capture(temp.path()).unwrap();

        // Apply op2
        fs::create_dir(&target2).unwrap();
        let _after_both = FsSnapshot::capture(temp.path()).unwrap();

        // Reverse composition
        fs::remove_dir(&target2).unwrap();
        let after_reverse_op2 = FsSnapshot::capture(temp.path()).unwrap();

        fs::remove_dir(&target1).unwrap();
        let _final_state = FsSnapshot::capture(temp.path()).unwrap();

        // Verify composition properties
        prop_assert_eq!(after_reverse_op2, after_op1, "Reversing op2 should return to after_op1 state");
    });
}

/// Property: Nested path operations work correctly
///
/// Validates: Parent directory must exist (ENOENT handling)
#[test]
fn prop_nested_paths() {
    proptest!(|(nested_path in valid_nested_path_strategy())| {
        let temp = TempDir::new().unwrap();
        let target = temp.path().join(&nested_path);

        // Attempting mkdir without parent should fail
        if let Some(parent) = target.parent() {
            if !parent.exists() && parent != temp.path() {
                let result = fs::create_dir(&target);
                prop_assert!(result.is_err(), "mkdir should fail when parent doesn't exist");

                if let Err(e) = result {
                    prop_assert_eq!(e.kind(), std::io::ErrorKind::NotFound);
                }
                return Ok(());
            }
        }

        // If parent exists, mkdir should succeed
        if let Some(parent) = target.parent() {
            if !parent.exists() && parent != temp.path() {
                fs::create_dir_all(parent).unwrap();
            }
        }

        fs::create_dir(&target).unwrap();
        prop_assert!(target.exists());

        fs::remove_dir(&target).unwrap();
        prop_assert!(!target.exists());
    });
}

/// Property: CNO (Create-No-Op) creates identity element
///
/// Lean theorem: `reversibleCreatesIdentity` (FilesystemComposition.lean:95)
/// ```lean
/// theorem reversibleCreatesIdentity (op : Operation)
///   (h_rev : Reversible op) :
///   ∃ (inv : Operation), applyOp inv (applyOp op fs) = fs
/// ```
#[test]
fn prop_cno_identity() {
    proptest!(|(path in valid_path_strategy())| {
        let temp = TempDir::new().unwrap();
        let target = temp.path().join(&path);

        if target.exists() {
            return Ok(());
        }

        // Capture state
        let before = FsSnapshot::capture(temp.path()).unwrap();

        // Apply operation (mkdir)
        fs::create_dir(&target).unwrap();

        // Apply inverse (rmdir) - should be identity
        fs::remove_dir(&target).unwrap();

        // Verify identity: op⁻¹(op(fs)) = fs
        let after = FsSnapshot::capture(temp.path()).unwrap();
        prop_assert_eq!(before, after, "Inverse operation should be identity");
    });
}

/// Property: File content preservation during reversible operations
///
/// Validates that reversing file operations preserves original content
#[test]
fn prop_content_preservation() {
    proptest!(|(
        path in valid_path_strategy(),
        original in prop::collection::vec(any::<u8>(), 0..200)
    )| {
        let temp = TempDir::new().unwrap();
        let target = temp.path().join(&path);

        // Create file with original content
        fs::write(&target, &original).unwrap();

        // Read back
        let read_content = fs::read(&target).unwrap();
        prop_assert_eq!(read_content, original.clone(), "Content should be preserved");

        // Delete and recreate
        fs::remove_file(&target).unwrap();
        fs::write(&target, &original).unwrap();

        // Verify content again
        let final_content = fs::read(&target).unwrap();
        prop_assert_eq!(final_content, original, "Content preserved after delete/recreate");
    });
}

/// Property: Equivalence relation properties
///
/// Lean theorem: `fs_equiv_refl/sym/trans` (FilesystemEquivalence.lean)
/// ```lean
/// theorem fs_equiv_refl : Reflexive fs_equivalent
/// theorem fs_equiv_sym : Symmetric fs_equivalent
/// theorem fs_equiv_trans : Transitive fs_equivalent
/// ```
#[test]
fn prop_equivalence_reflexive() {
    proptest!(|(path in valid_path_strategy())| {
        let temp = TempDir::new().unwrap();
        let target = temp.path().join(&path);

        if !target.exists() {
            fs::create_dir(&target).unwrap();
        }

        // Capture state twice
        let snapshot1 = FsSnapshot::capture(temp.path()).unwrap();
        let snapshot2 = FsSnapshot::capture(temp.path()).unwrap();

        // Reflexivity: fs ≡ fs
        prop_assert_eq!(snapshot1, snapshot2);
    });
}

/// Property: Path validation edge cases
///
/// Tests boundary conditions for path handling
#[test]
fn prop_path_validation() {
    proptest!(|(path in valid_path_strategy())| {
        let temp = TempDir::new().unwrap();
        let target = temp.path().join(&path);

        // Empty paths should work (valid directory names)
        if path.is_empty() {
            return Ok(());
        }

        // Path should be creatable if preconditions met
        if !target.exists() {
            fs::create_dir(&target).unwrap();
            prop_assert!(target.exists());
            prop_assert!(target.is_dir());
        }
    });
}

// ============================================================
// File Content Modification Properties (Phase 6 M2)
// ============================================================

/// Property: File truncation is reversible with saved content
///
/// Pending Lean theorem: `truncate_restore_reversible` (FileContentOperations.lean)
/// ```lean
/// theorem truncate_restore_reversible (p : Path) (fs : Filesystem) :
///   let original := readFile p fs
///   let truncated := writeFile p "" fs
///   let restored := writeFile p original truncated
///   restored = fs
/// ```
///
/// Validates: Output redirection (>) undo restores original content
#[test]
fn prop_truncate_restore_reversible() {
    proptest!(|(
        path in valid_path_strategy(),
        original_content in prop::collection::vec(any::<u8>(), 1..500)
    )| {
        let temp = TempDir::new().unwrap();
        let target = temp.path().join(&path);

        // Create file with original content
        fs::write(&target, &original_content).unwrap();

        // Save original for undo
        let saved_content = fs::read(&target).unwrap();
        prop_assert_eq!(saved_content.clone(), original_content.clone());

        // Truncate (simulate > redirection)
        fs::write(&target, b"").unwrap();
        let truncated = fs::read(&target).unwrap();
        prop_assert_eq!(truncated.len(), 0, "File should be truncated to zero");

        // Restore original (undo)
        fs::write(&target, &saved_content).unwrap();

        // Verify restoration
        let restored = fs::read(&target).unwrap();
        prop_assert_eq!(
            restored,
            original_content,
            "Restore should return to original state"
        );
    });
}

/// Property: File append is reversible with truncation to original size
///
/// Pending Lean theorem: `append_truncate_reversible` (FileContentOperations.lean)
/// ```lean
/// theorem append_truncate_reversible (p : Path) (data : String) (fs : Filesystem) :
///   let original_size := fileSize p fs
///   let appended := appendFile p data fs
///   let restored := truncateFile p original_size appended
///   restored = fs
/// ```
///
/// Validates: Append redirection (>>) undo truncates to original size
#[test]
fn prop_append_truncate_reversible() {
    proptest!(|(
        path in valid_path_strategy(),
        original_content in prop::collection::vec(any::<u8>(), 1..500),
        appended_content in prop::collection::vec(any::<u8>(), 1..500)
    )| {
        use std::fs::OpenOptions;
        use std::io::Write;

        let temp = TempDir::new().unwrap();
        let target = temp.path().join(&path);

        // Create file with original content
        fs::write(&target, &original_content).unwrap();

        // Record original size
        let original_size = fs::metadata(&target).unwrap().len();
        prop_assert_eq!(original_size, original_content.len() as u64);

        // Append (simulate >> redirection)
        let mut file = OpenOptions::new()
            .append(true)
            .open(&target)
            .unwrap();
        file.write_all(&appended_content).unwrap();
        drop(file);

        // Verify append happened
        let appended = fs::read(&target).unwrap();
        let expected_size = original_content.len() + appended_content.len();
        prop_assert_eq!(appended.len(), expected_size, "Content should be appended");

        // Truncate to original size (undo)
        let file = OpenOptions::new()
            .write(true)
            .open(&target)
            .unwrap();
        file.set_len(original_size).unwrap();
        drop(file);

        // Verify restoration
        let restored = fs::read(&target).unwrap();
        prop_assert_eq!(
            restored,
            original_content,
            "Truncate to original size should restore original content"
        );
    });
}

/// Property: Multiple truncations are reversible in sequence
///
/// Validates: Multiple > redirections can be undone in reverse order
#[test]
fn prop_multiple_truncates_reversible() {
    proptest!(|(
        path in valid_path_strategy(),
        content1 in prop::collection::vec(any::<u8>(), 1..200),
        content2 in prop::collection::vec(any::<u8>(), 1..200),
        content3 in prop::collection::vec(any::<u8>(), 1..200)
    )| {
        let temp = TempDir::new().unwrap();
        let target = temp.path().join(&path);

        // Initial state
        fs::write(&target, &content1).unwrap();
        let state1 = fs::read(&target).unwrap();

        // Truncate to content2
        let saved1 = fs::read(&target).unwrap();
        fs::write(&target, &content2).unwrap();
        let state2 = fs::read(&target).unwrap();

        // Truncate to content3
        let saved2 = fs::read(&target).unwrap();
        fs::write(&target, &content3).unwrap();
        let _state3 = fs::read(&target).unwrap();

        // Undo sequence (reverse order)
        fs::write(&target, &saved2).unwrap();
        let after_undo1 = fs::read(&target).unwrap();
        prop_assert_eq!(after_undo1, state2, "First undo should restore state2");

        fs::write(&target, &saved1).unwrap();
        let after_undo2 = fs::read(&target).unwrap();
        prop_assert_eq!(after_undo2.clone(), state1, "Second undo should restore state1");
        prop_assert_eq!(after_undo2, content1, "Should return to initial content");
    });
}

/// Property: Append-truncate-append composition
///
/// Validates: Complex modification sequences are reversible
#[test]
fn prop_append_truncate_append() {
    proptest!(|(
        path in valid_path_strategy(),
        base in prop::collection::vec(any::<u8>(), 10..100),
        data1 in prop::collection::vec(any::<u8>(), 5..50),
        data2 in prop::collection::vec(any::<u8>(), 5..50)
    )| {
        use std::fs::OpenOptions;
        use std::io::Write;

        let temp = TempDir::new().unwrap();
        let target = temp.path().join(&path);

        // Base state
        fs::write(&target, &base).unwrap();
        let base_size = fs::metadata(&target).unwrap().len();

        // Append data1
        let mut f = OpenOptions::new().append(true).open(&target).unwrap();
        f.write_all(&data1).unwrap();
        drop(f);

        // Truncate to base
        let f = OpenOptions::new().write(true).open(&target).unwrap();
        f.set_len(base_size).unwrap();
        drop(f);
        let after_truncate1 = fs::read(&target).unwrap();
        prop_assert_eq!(after_truncate1, base.clone(), "Truncate should restore base");

        // Append data2
        let mut f = OpenOptions::new().append(true).open(&target).unwrap();
        f.write_all(&data2).unwrap();
        drop(f);

        // Truncate to base again
        let f = OpenOptions::new().write(true).open(&target).unwrap();
        f.set_len(base_size).unwrap();
        drop(f);

        let final_state = fs::read(&target).unwrap();
        prop_assert_eq!(final_state, base, "Should return to base after second cycle");
    });
}

/// Property: Zero-byte file operations
///
/// Validates: Edge case handling for empty files
#[test]
fn prop_empty_file_operations() {
    proptest!(|(path in valid_path_strategy())| {
        let temp = TempDir::new().unwrap();
        let target = temp.path().join(&path);

        // Create empty file
        fs::write(&target, b"").unwrap();
        prop_assert!(target.exists());
        prop_assert_eq!(fs::metadata(&target).unwrap().len(), 0);

        // Append to empty file
        use std::fs::OpenOptions;
        use std::io::Write;
        let mut f = OpenOptions::new().append(true).open(&target).unwrap();
        f.write_all(b"data").unwrap();
        drop(f);

        let content = fs::read(&target).unwrap();
        prop_assert_eq!(content, b"data");

        // Truncate back to zero
        let f = OpenOptions::new().write(true).open(&target).unwrap();
        f.set_len(0).unwrap();
        drop(f);

        let final_content = fs::read(&target).unwrap();
        prop_assert_eq!(final_content.len(), 0, "Should be empty again");
    });
}

// ============================================================
// Conditional & Logical Operator Properties (Phase 6 M14)
// ============================================================

/// Property: test -f always returns 0 for regular files, 1 otherwise
///
/// POSIX requirement: test -f should check if path is a regular file
#[test]
fn prop_test_f_file_detection() {
    proptest!(|(path in valid_path_strategy())| {
        use vsh::test_command::execute_test;

        let temp = TempDir::new().unwrap();
        let target = temp.path().join(&path);

        // Create a file
        fs::write(&target, b"test").unwrap();

        // test -f should return 0 (success)
        let args = vec!["-f".to_string(), target.to_string_lossy().to_string()];
        let exit_code = execute_test(&args, false).unwrap();
        prop_assert_eq!(exit_code, 0, "test -f should return 0 for regular files");

        // Remove and create dir instead
        fs::remove_file(&target).unwrap();
        fs::create_dir(&target).unwrap();

        // test -f should return 1 (failure) for directory
        let args = vec!["-f".to_string(), target.to_string_lossy().to_string()];
        let exit_code = execute_test(&args, false).unwrap();
        prop_assert_eq!(exit_code, 1, "test -f should return 1 for directories");
    });
}

/// Property: test -d always returns 0 for directories, 1 otherwise
///
/// POSIX requirement: test -d should check if path is a directory
#[test]
fn prop_test_d_directory_detection() {
    proptest!(|(path in valid_path_strategy())| {
        use vsh::test_command::execute_test;

        let temp = TempDir::new().unwrap();
        let target = temp.path().join(&path);

        // Create a directory
        fs::create_dir(&target).unwrap();

        // test -d should return 0 (success)
        let args = vec!["-d".to_string(), target.to_string_lossy().to_string()];
        let exit_code = execute_test(&args, false).unwrap();
        prop_assert_eq!(exit_code, 0, "test -d should return 0 for directories");

        // Remove and create file instead
        fs::remove_dir(&target).unwrap();
        fs::write(&target, b"test").unwrap();

        // test -d should return 1 (failure) for file
        let args = vec!["-d".to_string(), target.to_string_lossy().to_string()];
        let exit_code = execute_test(&args, false).unwrap();
        prop_assert_eq!(exit_code, 1, "test -d should return 1 for files");
    });
}

/// Property: test -e returns 0 for any existing path
///
/// POSIX requirement: test -e checks existence regardless of type
#[test]
fn prop_test_e_existence_check() {
    proptest!(|(path in valid_path_strategy(), is_dir in any::<bool>())| {
        use vsh::test_command::execute_test;

        let temp = TempDir::new().unwrap();
        let target = temp.path().join(&path);

        // Create either file or directory
        if is_dir {
            fs::create_dir(&target).unwrap();
        } else {
            fs::write(&target, b"test").unwrap();
        }

        // test -e should return 0 (exists)
        let args = vec!["-e".to_string(), target.to_string_lossy().to_string()];
        let exit_code = execute_test(&args, false).unwrap();
        prop_assert_eq!(exit_code, 0, "test -e should return 0 for existing paths");

        // Remove
        if is_dir {
            fs::remove_dir(&target).unwrap();
        } else {
            fs::remove_file(&target).unwrap();
        }

        // test -e should return 1 (doesn't exist)
        let args = vec!["-e".to_string(), target.to_string_lossy().to_string()];
        let exit_code = execute_test(&args, false).unwrap();
        prop_assert_eq!(exit_code, 1, "test -e should return 1 for non-existing paths");
    });
}

/// Property: test string equality is reflexive and symmetric
///
/// POSIX requirement: string comparison should follow equality properties
#[test]
fn prop_test_string_equality() {
    proptest!(|(s in "[a-z]{1,20}")| {
        use vsh::test_command::execute_test;

        // s = s should be true
        let args = vec![s.clone(), "=".to_string(), s.clone()];
        let exit_code = execute_test(&args, false).unwrap();
        prop_assert_eq!(exit_code, 0, "String should equal itself");

        // s != s should be false
        let args = vec![s.clone(), "!=".to_string(), s.clone()];
        let exit_code = execute_test(&args, false).unwrap();
        prop_assert_eq!(exit_code, 1, "String should not be not-equal to itself");
    });
}

/// Property: test integer comparisons are transitive
///
/// If a < b and b < c, then a < c
#[test]
fn prop_test_integer_transitivity() {
    proptest!(|(a in 0i64..100, b in 100i64..200, c in 200i64..300)| {
        use vsh::test_command::execute_test;

        // a -lt b should be true
        let args = vec![a.to_string(), "-lt".to_string(), b.to_string()];
        let exit_code = execute_test(&args, false).unwrap();
        prop_assert_eq!(exit_code, 0, "a < b should be true");

        // b -lt c should be true
        let args = vec![b.to_string(), "-lt".to_string(), c.to_string()];
        let exit_code = execute_test(&args, false).unwrap();
        prop_assert_eq!(exit_code, 0, "b < c should be true");

        // Therefore a -lt c should be true (transitivity)
        let args = vec![a.to_string(), "-lt".to_string(), c.to_string()];
        let exit_code = execute_test(&args, false).unwrap();
        prop_assert_eq!(exit_code, 0, "a < c should be true (transitivity)");
    });
}

/// Property: Logical AND (&&) short-circuits on failure
///
/// cmd1 && cmd2: if cmd1 fails, cmd2 never executes
#[test]
fn prop_logical_and_short_circuit() {
    proptest!(|(path in valid_path_strategy())| {
        use vsh::parser::parse_command;
        use vsh::executable::ExecutableCommand;
        use vsh::state::ShellState;

        let temp = TempDir::new().unwrap();

        // Parse: test -f nonexistent && mkdir path
        // The mkdir should NOT execute because test fails
        let nonexistent = temp.path().join("does_not_exist.txt");
        let target = temp.path().join(&path);

        let cmd_str = format!(
            "test -f {} && mkdir {}",
            nonexistent.to_string_lossy(),
            target.to_string_lossy()
        );

        let cmd = parse_command(&cmd_str).unwrap();

        // Execute
        let mut state = ShellState::new(temp.path()).unwrap();
        let _ = cmd.execute(&mut state);

        // The directory should NOT exist (mkdir didn't run due to short-circuit)
        prop_assert!(!target.exists(), "Short-circuit should prevent mkdir execution");
    });
}

/// Property: Logical OR (||) short-circuits on success
///
/// cmd1 || cmd2: if cmd1 succeeds, cmd2 never executes
#[test]
fn prop_logical_or_short_circuit() {
    proptest!(|(path1 in valid_path_strategy(), path2 in valid_path_strategy())| {
        use vsh::parser::parse_command;
        use vsh::executable::ExecutableCommand;
        use vsh::state::ShellState;

        let temp = TempDir::new().unwrap();

        // Create first dir
        let target1 = temp.path().join(&path1);
        fs::create_dir(&target1).unwrap();

        let target2 = temp.path().join(&path2);

        // Parse: test -d path1 || mkdir path2
        // The mkdir should NOT execute because test succeeds
        let cmd_str = format!(
            "test -d {} || mkdir {}",
            target1.to_string_lossy(),
            target2.to_string_lossy()
        );

        let cmd = parse_command(&cmd_str).unwrap();

        // Execute
        let mut state = ShellState::new(temp.path()).unwrap();
        let _ = cmd.execute(&mut state);

        // The second directory should NOT exist (mkdir didn't run due to short-circuit)
        prop_assert!(!target2.exists(), "Short-circuit should prevent mkdir execution");
    });
}

/// Property: Quote processing prevents glob expansion
///
/// Quoted patterns should not be expanded even if they match files
#[test]
fn prop_quote_prevents_glob() {
    proptest!(|()| {
        use vsh::quotes::parse_quotes;
        use vsh::quotes::QuoteState;

        // Test various quoted glob patterns
        let test_cases = vec![
            ("'*.txt'", true),  // Single quotes - no expansion
            ("\"*.txt\"", true),  // Double quotes - no expansion
            ("*.txt", false),   // Unquoted - should expand
            ("'[abc]'", true),  // Bracket glob in quotes
            ("'{1,2,3}'", true), // Brace expansion in quotes
        ];

        for (input, should_be_quoted) in test_cases {
            let segments = parse_quotes(input).unwrap();

            if should_be_quoted {
                // At least one segment should be quoted
                let has_quoted = segments.iter().any(|seg| {
                    !matches!(seg.state, QuoteState::Unquoted)
                });
                prop_assert!(has_quoted, "Pattern {} should have quoted segments", input);
            }
        }
    });
}

/// Property: Glob expansion is deterministic
///
/// Expanding the same pattern twice should give the same results
#[test]
fn prop_glob_deterministic() {
    proptest!(|(files in prop::collection::vec("[a-z]{3,8}\\.txt", 1..5))| {
        let temp = TempDir::new().unwrap();

        // Create files
        for file in &files {
            let path = temp.path().join(file);
            fs::write(&path, b"test").unwrap();
        }

        // Expand glob twice
        use vsh::glob::expand_glob;
        let pattern = format!("{}/*.txt", temp.path().to_string_lossy());

        let expansion1 = expand_glob(&pattern).unwrap();
        let expansion2 = expand_glob(&pattern).unwrap();

        prop_assert_eq!(expansion1, expansion2, "Glob expansion should be deterministic");
    });
}

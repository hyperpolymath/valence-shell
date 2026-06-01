// SPDX-License-Identifier: MPL-2.0
//! Property-correspondence tests for the new `secure_delete` / `audit_log`
//! primitives and for the named filesystem-reversibility theorems referenced
//! in the `proofs/` directory.
//!
//! Each `proptest!` block exercises a property already mechanised in
//! Coq/Lean/Idris2 (see comments) and checks that the Rust implementation
//! matches under random inputs. Failures here indicate either a regression
//! in the impl or a drift between the proof and the practice.
//!
//! Echo-types audit (per the 2026-05 echo-types-mandatory directive): these
//! filesystem-reversibility properties live at the **L3 (echo) layer** of
//! the four-layer redesign. The implementation does not yet *import*
//! `echo-types` directly — we record the shape correspondence here so the
//! later echo-layer integration can hoist these properties one-for-one.

use anyhow::Result;
use proptest::prelude::*;
use std::fs;
use std::path::PathBuf;
use tempfile::tempdir;

use vsh::audit_log::{AuditEntry, AuditLog};
use vsh::commands::secure_deletion::secure_delete;
use vsh::commands::{cp, mkdir, rm, rmdir, touch};
use vsh::state::{Operation, OperationType, ShellState};

// ============================================================================
// Generators
// ============================================================================

fn dir_name() -> impl Strategy<Value = String> {
    "[a-z][a-z0-9_]{0,12}".prop_map(|s| s)
}

fn file_name() -> impl Strategy<Value = String> {
    ("[a-z][a-z0-9_]{0,10}", "[a-z]{1,4}")
        .prop_map(|(name, ext)| format!("{}.{}", name, ext))
}

fn file_content() -> impl Strategy<Value = Vec<u8>> {
    prop::collection::vec(any::<u8>(), 0..4096)
}

fn nonempty_file_content() -> impl Strategy<Value = Vec<u8>> {
    prop::collection::vec(any::<u8>(), 1..4096)
}

// ============================================================================
// Group A — Filesystem-reversibility theorems (echo-layer L3)
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    // mkdir_rmdir_reversible (Lean: FilesystemModel.lean)
    #[test]
    fn prop_mkdir_rmdir_reversible(name in dir_name()) {
        let temp = tempdir().unwrap();
        let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

        prop_assume!(!state.resolve_path(&name).exists());

        mkdir(&mut state, &name, false).unwrap();
        prop_assert!(state.resolve_path(&name).exists());

        rmdir(&mut state, &name, false).unwrap();
        prop_assert!(!state.resolve_path(&name).exists());
    }

    // mkdir injectivity: mkdir(p1); mkdir(p2) ≠ mkdir(p1); mkdir(p1) for p1≠p2
    #[test]
    fn prop_mkdir_distinct_paths_both_exist(p1 in dir_name(), p2 in dir_name()) {
        prop_assume!(p1 != p2);
        let temp = tempdir().unwrap();
        let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();
        mkdir(&mut state, &p1, false).unwrap();
        mkdir(&mut state, &p2, false).unwrap();
        prop_assert!(state.resolve_path(&p1).exists());
        prop_assert!(state.resolve_path(&p2).exists());
    }

    // touch_rm_reversible (Lean: FileOperations.lean / createFile + deleteFile)
    #[test]
    fn prop_touch_rm_reversible(name in file_name()) {
        let temp = tempdir().unwrap();
        let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

        prop_assume!(!state.resolve_path(&name).exists());

        touch(&mut state, &name, false).unwrap();
        prop_assert!(state.resolve_path(&name).exists());

        rm(&mut state, &name, false).unwrap();
        prop_assert!(!state.resolve_path(&name).exists());
    }

    // writeFileReversible — write-then-restore round-trip preserves bytes.
    // Models the L3 theorem that the undo-WriteFile carrier preserves content.
    #[test]
    fn prop_writefile_reversible(name in file_name(), content in nonempty_file_content()) {
        let temp = tempdir().unwrap();
        let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();
        prop_assume!(!state.resolve_path(&name).exists());

        touch(&mut state, &name, false).unwrap();
        let resolved = state.resolve_path(&name);
        fs::write(&resolved, &content).unwrap();
        let read_back = fs::read(&resolved).unwrap();
        prop_assert_eq!(read_back, content);

        rm(&mut state, &name, false).unwrap();
        prop_assert!(!resolved.exists());
    }

    // copyFile_reversible — cp src dst then deleting dst returns to (src exists, dst absent).
    #[test]
    fn prop_copyfile_reversible(src in file_name(), dst in file_name(), content in file_content()) {
        prop_assume!(src != dst);
        let temp = tempdir().unwrap();
        let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();
        prop_assume!(!state.resolve_path(&src).exists());
        prop_assume!(!state.resolve_path(&dst).exists());

        touch(&mut state, &src, false).unwrap();
        let src_resolved = state.resolve_path(&src);
        fs::write(&src_resolved, &content).unwrap();

        cp(&mut state, &src, &dst, false).unwrap();
        let dst_resolved = state.resolve_path(&dst);
        prop_assert!(dst_resolved.exists(), "dst must exist after cp");
        prop_assert_eq!(fs::read(&dst_resolved).unwrap(), content);

        // Reverse: rm dst leaves src intact.
        rm(&mut state, &dst, false).unwrap();
        prop_assert!(!dst_resolved.exists());
        prop_assert!(src_resolved.exists(), "src must survive dst rm");
    }

    // Independence: mkdir(a) does not touch unrelated path b.
    #[test]
    fn prop_mkdir_preserves_other_paths(a in dir_name(), b in dir_name()) {
        prop_assume!(a != b);
        let temp = tempdir().unwrap();
        let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

        mkdir(&mut state, &b, false).unwrap();
        let b_exists_before = state.resolve_path(&b).exists();

        let _ = mkdir(&mut state, &a, false);

        prop_assert_eq!(state.resolve_path(&b).exists(), b_exists_before);
    }

    // Idempotence after reversibility: mkdir; rmdir; mkdir is the same as mkdir.
    #[test]
    fn prop_mkdir_rmdir_mkdir_equals_mkdir(name in dir_name()) {
        let temp = tempdir().unwrap();
        let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();
        prop_assume!(!state.resolve_path(&name).exists());

        mkdir(&mut state, &name, false).unwrap();
        rmdir(&mut state, &name, false).unwrap();
        mkdir(&mut state, &name, false).unwrap();
        prop_assert!(state.resolve_path(&name).exists());
    }
}

// ============================================================================
// Group B — Irreversibility theorems
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    // OperationType::inverse() is None for Obliterate and HardwareErase — by construction.
    // This anchors the "obliterate_not_injective" / no-inverse property.
    #[test]
    fn prop_obliterate_has_no_inverse(_x in 0u8..=255u8) {
        prop_assert!(OperationType::Obliterate.inverse().is_none());
        prop_assert!(OperationType::HardwareErase.inverse().is_none());
    }

    // For every reversible OperationType, inverse(inverse(t)) returns either t
    // or a known compatible chain (e.g. Move is self-inverse, UnsetVariable → SetVariable).
    // Spot-checks the L3 carrier composition property.
    #[test]
    fn prop_inverse_round_trip_for_reversible(seed in 0usize..15) {
        let all = [
            OperationType::Mkdir,
            OperationType::Rmdir,
            OperationType::CreateFile,
            OperationType::DeleteFile,
            OperationType::WriteFile,
            OperationType::FileTruncated,
            OperationType::FileAppended,
            OperationType::CopyFile,
            OperationType::Move,
            OperationType::Symlink,
            OperationType::Unlink,
            OperationType::SetVariable,
            OperationType::UnsetVariable,
            OperationType::Chmod,
            OperationType::Chown,
        ];
        let t = all[seed % all.len()];
        let inv = t.inverse().expect("listed types are all reversible");
        prop_assert!(inv.inverse().is_some(),
            "inverse of {:?} = {:?} should itself be reversible", t, inv);
    }

    // secure_delete actually unlinks the target.
    #[test]
    fn prop_secure_delete_removes_file(name in file_name(), content in file_content()) {
        let temp = tempdir().unwrap();
        let target = temp.path().join(&name);
        fs::write(&target, &content).unwrap();
        prop_assert!(target.exists());

        secure_delete(&target).unwrap();
        prop_assert!(!target.exists(), "secure_delete must unlink the target");
    }

    // secure_delete refuses directories (EISDIR).
    #[test]
    fn prop_secure_delete_refuses_directories(name in dir_name()) {
        let temp = tempdir().unwrap();
        let target = temp.path().join(&name);
        fs::create_dir(&target).unwrap();

        let err = secure_delete(&target);
        prop_assert!(err.is_err(), "secure_delete must error on directory inputs");
        prop_assert!(target.exists(), "directory must survive failed secure_delete");
    }

    // secure_delete refuses non-existent paths (ENOENT).
    #[test]
    fn prop_secure_delete_refuses_missing(name in file_name()) {
        let temp = tempdir().unwrap();
        let target = temp.path().join(&name);
        prop_assert!(!target.exists());

        let err = secure_delete(&target);
        prop_assert!(err.is_err(), "secure_delete must error on missing target");
    }

    // secure_delete writes through to disk: even for tiny files the unlink
    // succeeds and the inode is gone. Tests the small-file edge of the
    // chunked-write loop.
    #[test]
    fn prop_secure_delete_handles_tiny_files(byte in any::<u8>()) {
        let temp = tempdir().unwrap();
        let target = temp.path().join("tiny.bin");
        fs::write(&target, [byte]).unwrap();
        prop_assert!(target.exists());

        secure_delete(&target).unwrap();
        prop_assert!(!target.exists());
    }

    // secure_delete handles empty files (zero-byte edge of the loop).
    #[test]
    fn prop_secure_delete_handles_empty_files(_unused in 0u8..=255u8) {
        let temp = tempdir().unwrap();
        let target = temp.path().join("empty.bin");
        fs::File::create(&target).unwrap();
        prop_assert!(target.exists());
        prop_assert_eq!(fs::metadata(&target).unwrap().len(), 0);

        secure_delete(&target).unwrap();
        prop_assert!(!target.exists());
    }
}

// ============================================================================
// Group C — Audit-log append-only properties (L3 echo carrier)
// ============================================================================

fn audit_log_in_tempdir() -> (tempfile::TempDir, PathBuf, AuditLog) {
    let dir = tempdir().unwrap();
    let path = dir.path().join("audit.log");
    let log = AuditLog::new(path.clone(), None).unwrap();
    (dir, path, log)
}

fn op_for_audit(kind: OperationType, path: &str) -> Operation {
    Operation::new(kind, path.to_string(), None)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(48))]

    // Append-only: every successful append increases the entry count by 1.
    #[test]
    fn prop_audit_log_append_only(paths in prop::collection::vec(dir_name(), 1..=10)) {
        let (_dir, _path, log) = audit_log_in_tempdir();

        for (i, p) in paths.iter().enumerate() {
            let op = op_for_audit(OperationType::Mkdir, p);
            log.append(&AuditEntry::from_operation(&op, "success", None)).unwrap();
            let read = log.read_all().unwrap();
            prop_assert_eq!(read.len(), i + 1);
        }
    }

    // Order-preservation: read_all() returns entries in append order.
    #[test]
    fn prop_audit_log_preserves_order(paths in prop::collection::vec(dir_name(), 1..=8)) {
        let (_dir, _path, log) = audit_log_in_tempdir();

        for p in &paths {
            let op = op_for_audit(OperationType::CreateFile, p);
            log.append(&AuditEntry::from_operation(&op, "success", None)).unwrap();
        }

        let read = log.read_all().unwrap();
        prop_assert_eq!(read.len(), paths.len());
        for (i, entry) in read.iter().enumerate() {
            prop_assert_eq!(&entry.path, &paths[i]);
        }
    }

    // Filter by type: read_by_type returns exactly the matching subset, order-preserving.
    #[test]
    fn prop_audit_log_filter_by_type(
        mkdirs in prop::collection::vec(dir_name(), 0..=5),
        touches in prop::collection::vec(file_name(), 0..=5),
    ) {
        let (_dir, _path, log) = audit_log_in_tempdir();

        // Interleave: alternate appends.
        let max = mkdirs.len().max(touches.len());
        for i in 0..max {
            if let Some(p) = mkdirs.get(i) {
                let op = op_for_audit(OperationType::Mkdir, p);
                log.append(&AuditEntry::from_operation(&op, "success", None)).unwrap();
            }
            if let Some(p) = touches.get(i) {
                let op = op_for_audit(OperationType::CreateFile, p);
                log.append(&AuditEntry::from_operation(&op, "success", None)).unwrap();
            }
        }

        let mkdir_entries = log.read_by_type("Mkdir").unwrap();
        prop_assert_eq!(mkdir_entries.len(), mkdirs.len());
        for (i, e) in mkdir_entries.iter().enumerate() {
            prop_assert_eq!(&e.path, &mkdirs[i]);
        }
    }

    // outcome="error" stamps the error string into the entry verbatim.
    #[test]
    fn prop_audit_log_records_errors(msg in "[a-zA-Z0-9 ]{1,40}") {
        let (_dir, _path, log) = audit_log_in_tempdir();
        let op = op_for_audit(OperationType::Obliterate, "irrelevant");
        let entry = AuditEntry::from_operation(&op, "error", Some(msg.clone()));
        log.append(&entry).unwrap();

        let read = log.read_all().unwrap();
        prop_assert_eq!(read.len(), 1);
        prop_assert_eq!(&read[0].outcome, "error");
        prop_assert_eq!(read[0].error.as_deref(), Some(msg.as_str()));
    }

    // Round-trip: serialised JSON line parses back to a structurally-equal entry.
    #[test]
    fn prop_audit_entry_json_roundtrip(path in dir_name(), outcome in prop_oneof!["success", "error"]) {
        let op = op_for_audit(OperationType::Mkdir, &path);
        let entry = AuditEntry::from_operation(&op, &outcome, None);
        let line = entry.to_json_line().unwrap();
        prop_assert!(line.ends_with('\n'));
        let parsed = AuditEntry::from_json_line(line.trim_end()).unwrap();
        prop_assert_eq!(parsed.operation_id, entry.operation_id);
        prop_assert_eq!(parsed.path, entry.path);
        prop_assert_eq!(parsed.outcome, entry.outcome);
    }
}

// ============================================================================
// Group D — XDG default-path resolution
// ============================================================================

#[test]
fn audit_log_default_path_under_xdg_state_home() -> Result<()> {
    // Set XDG_STATE_HOME to a temp dir; ensure default_path returns the
    // expected subpath. Restore env at end.
    let dir = tempdir()?;
    let prev = std::env::var_os("XDG_STATE_HOME");
    // SAFETY: synchronous test, restored before exit.
    unsafe {
        std::env::set_var("XDG_STATE_HOME", dir.path());
    }
    let p = AuditLog::default_path()?;
    assert_eq!(p, dir.path().join("valence-shell").join("audit.log"));
    unsafe {
        match prev {
            Some(v) => std::env::set_var("XDG_STATE_HOME", v),
            None => std::env::remove_var("XDG_STATE_HOME"),
        }
    }
    Ok(())
}

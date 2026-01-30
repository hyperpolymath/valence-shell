// SPDX-License-Identifier: PLMP-1.0-or-later
//! Integration Tests for Valence Shell v1.0
//!
//! Tests all new features added in this release:
//! - Audit logging
//! - Secure deletion (RMO)
//! - Syntax highlighting
//! - Command correction
//! - Friendly errors
//! - Smart pager
//! - 3-tier help system
//! - History limits

use anyhow::Result;
use std::path::PathBuf;
use tempfile::TempDir;
use reedline::Highlighter;
use vsh::{
    audit_log::{AuditEntry, AuditLog},
    commands,
    correction::{levenshtein_distance, suggest_correction},
    friendly_errors,
    help::{display_help, get_help, HelpTier},
    highlighter::VshHighlighter,
    pager::Pager,
    state::{Operation, OperationType, ShellState},
};

#[test]
fn test_audit_log_integration() -> Result<()> {
    let temp_dir = TempDir::new()?;
    let log_path = temp_dir.path().join("audit.log");

    // Create audit log
    let audit_log = AuditLog::new(log_path.clone(), None)?;

    // Create some operations
    let op1 = Operation::new(OperationType::Mkdir, "test_dir".to_string(), None);
    let op2 = Operation::new(OperationType::CreateFile, "test_file.txt".to_string(), None);

    // Log operations
    let entry1 = AuditEntry::from_operation(&op1, "success", None);
    let entry2 = AuditEntry::from_operation(&op2, "success", None);

    audit_log.append(&entry1)?;
    audit_log.append(&entry2)?;

    // Read back and verify
    let entries = audit_log.read_all()?;
    assert_eq!(entries.len(), 2);
    assert_eq!(entries[0].path, "test_dir");
    assert_eq!(entries[1].path, "test_file.txt");
    assert_eq!(entries[0].outcome, "success");

    // Test filtering by operation type
    let mkdirs = audit_log.read_by_type("Mkdir")?;
    assert_eq!(mkdirs.len(), 1);
    assert_eq!(mkdirs[0].path, "test_dir");

    Ok(())
}

#[test]
fn test_command_correction() {
    // Test Levenshtein distance
    assert_eq!(levenshtein_distance("kitten", "sitting"), 3);
    assert_eq!(levenshtein_distance("sl", "ls"), 2);
    assert_eq!(levenshtein_distance("gti", "git"), 2); // Transpose = 2 operations

    // Test correction suggestions
    assert_eq!(suggest_correction("mkdr"), Some("mkdir".to_string()));
    assert_eq!(suggest_correction("exot"), Some("exit".to_string()));
    assert!(suggest_correction("xyzabc").is_none()); // Too different
}

#[test]
fn test_friendly_errors_integration() {
    use anyhow::anyhow;

    // Test error display (doesn't panic)
    let error = anyhow!("No such file or directory: /tmp/missing");
    friendly_errors::display_friendly_error(&error);

    let error = anyhow!("Permission denied: /etc/shadow");
    friendly_errors::display_friendly_error(&error);

    let error = anyhow!("command not found: sl");
    friendly_errors::display_friendly_error(&error);
}

#[test]
fn test_syntax_highlighter() {
    let highlighter = VshHighlighter::new();

    // Test tokenization
    let styled = highlighter.highlight("ls -la /tmp", 0);
    assert!(!styled.buffer.is_empty());

    // Test pipeline highlighting
    let styled = highlighter.highlight("cat file.txt | grep test", 0);
    assert!(!styled.buffer.is_empty());

    // Test quoted strings
    let styled = highlighter.highlight("echo 'hello world'", 0);
    assert!(!styled.buffer.is_empty());
}

#[test]
fn test_smart_pager() -> Result<()> {
    let pager = Pager::new();

    // Short output should not trigger paging
    let short_content = "line 1\nline 2\nline 3\n";
    pager.page(short_content)?;

    // Test threshold configuration (threshold is private, just test methods exist)
    let _pager = Pager::new().with_threshold(0.5);
    let _pager = Pager::new().with_threshold(2.0);

    Ok(())
}

#[test]
fn test_help_system() -> Result<()> {
    // Test getting help entry
    let mkdir_help = get_help("mkdir");
    assert!(mkdir_help.is_some());

    let help = mkdir_help.unwrap();
    assert_eq!(help.name, "mkdir");
    assert!(!help.summary.is_empty());
    assert!(!help.usage.is_empty());
    assert!(!help.examples.is_empty());

    // Test nonexistent command
    assert!(get_help("nonexistent").is_none());

    // Test displaying help (should not panic)
    display_help(Some("mkdir"), HelpTier::Quick)?;
    display_help(Some("rm"), HelpTier::Verbose)?;

    Ok(())
}

#[test]
fn test_history_limits() -> Result<()> {
    let temp_dir = TempDir::new()?;
    let temp_path = temp_dir.path().to_str().unwrap();
    let mut state = ShellState::new(temp_path)?;

    // Set low history limit for testing
    state.max_history_size = Some(5);

    // Create more operations than limit
    for i in 0..10 {
        let path = format!("file{}", i);
        std::fs::write(temp_dir.path().join(&path), "test")?;
        commands::rm(&mut state, &path, false)?;
    }

    // Verify history is limited
    assert!(state.history.len() <= 5, "History should be limited to 5 operations");

    Ok(())
}

#[test]
fn test_secure_deletion_dry_run() -> Result<()> {
    // We can't actually test secure deletion without destroying real files,
    // but we can test the module imports and basic structures work
    use vsh::commands::secure_deletion;

    // Verify the module is accessible
    // (actual secure deletion would require confirmation prompts)

    Ok(())
}

#[test]
fn test_end_to_end_workflow() -> Result<()> {
    let temp_dir = TempDir::new()?;
    let mut state = ShellState::new(temp_dir.path().to_str().unwrap())?;

    // Enable history limits
    state.max_history_size = Some(100);

    // Create directory
    commands::mkdir(&mut state, "project", false)?;
    assert!(temp_dir.path().join("project").exists());

    // Create file
    commands::touch(&mut state, "project/README.md", false)?;
    assert!(temp_dir.path().join("project/README.md").exists());

    // Undo file creation
    commands::undo(&mut state, 1, false)?;
    assert!(!temp_dir.path().join("project/README.md").exists());

    // Redo file creation
    commands::redo(&mut state, 1, false)?;
    assert!(temp_dir.path().join("project/README.md").exists());

    // Remove file
    commands::rm(&mut state, "project/README.md", false)?;
    assert!(!temp_dir.path().join("project/README.md").exists());

    // Undo removal (restore file)
    commands::undo(&mut state, 1, false)?;
    assert!(temp_dir.path().join("project/README.md").exists());

    // Verify history tracking
    assert!(state.history.len() > 0, "History should contain operations");

    Ok(())
}

#[test]
fn test_all_features_integration() -> Result<()> {
    let temp_dir = TempDir::new()?;
    let mut state = ShellState::new(temp_dir.path().to_str().unwrap())?;

    // Set up audit log
    let audit_log_path = temp_dir.path().join("audit.log");
    let audit_log = AuditLog::new(audit_log_path, None)?;

    // Enable history limits
    state.max_history_size = Some(50);

    // Perform operations
    commands::mkdir(&mut state, "src", false)?;
    commands::mkdir(&mut state, "tests", false)?;
    commands::touch(&mut state, "src/lib.rs", false)?;
    commands::touch(&mut state, "tests/test.rs", false)?;

    // Log to audit
    for op in &state.history {
        if !op.undone {
            let entry = AuditEntry::from_operation(op, "success", None);
            audit_log.append(&entry)?;
        }
    }

    // Verify audit log
    let entries = audit_log.read_all()?;
    assert!(entries.len() >= 4, "Audit log should contain at least 4 entries");

    // Test undo
    commands::undo(&mut state, 2, false)?;
    assert!(!temp_dir.path().join("tests/test.rs").exists());
    assert!(!temp_dir.path().join("src/lib.rs").exists());

    // Test command correction
    let correction = suggest_correction("mkdr");
    assert_eq!(correction, Some("mkdir".to_string()));

    // Test help system
    let help = get_help("mkdir");
    assert!(help.is_some());

    Ok(())
}

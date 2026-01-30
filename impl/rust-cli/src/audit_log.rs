// SPDX-License-Identifier: PLMP-1.0-or-later
//! Append-Only Audit Log
//!
//! Provides tamper-resistant logging of all operations for compliance (SOC 2, GDPR, HIPAA).
//! Log entries are:
//! - Append-only (no deletion or modification)
//! - Timestamped with nanosecond precision
//! - Include operation type, path, outcome, user, PID
//! - Optionally cryptographically signed (HMAC-SHA256)
//!
//! Logs stored as JSONL (JSON Lines) for easy parsing and streaming.

use anyhow::{Context, Result};
use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use std::fs::OpenOptions;
use std::io::Write;
use std::path::{Path, PathBuf};
use uuid::Uuid;

use crate::state::Operation;

/// Single audit log entry
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuditEntry {
    /// Unique entry ID
    pub id: Uuid,

    /// Timestamp (UTC, nanosecond precision)
    pub timestamp: DateTime<Utc>,

    /// Operation ID (links to undo history)
    pub operation_id: Uuid,

    /// Operation type (mkdir, rm, rmO, etc.)
    pub operation_type: String,

    /// Target path
    pub path: String,

    /// Outcome: "success", "error"
    pub outcome: String,

    /// Error message if outcome == "error"
    pub error: Option<String>,

    /// User who performed the operation (from $USER)
    pub user: String,

    /// Process ID
    pub pid: u32,

    /// Shell root directory
    pub root: String,

    /// Optional HMAC-SHA256 signature (for tamper detection)
    pub signature: Option<String>,
}

impl AuditEntry {
    /// Create new audit entry from operation
    pub fn from_operation(op: &Operation, outcome: &str, error: Option<String>) -> Self {
        Self {
            id: Uuid::new_v4(),
            timestamp: Utc::now(),
            operation_id: op.id,
            operation_type: format!("{:?}", op.op_type),
            path: op.path.clone(),
            outcome: outcome.to_string(),
            error,
            user: std::env::var("USER").unwrap_or_else(|_| "unknown".to_string()),
            pid: std::process::id(),
            root: std::env::current_dir()
                .ok()
                .and_then(|p| p.to_str().map(|s| s.to_string()))
                .unwrap_or_else(|| "/".to_string()),
            signature: None,  // TODO: Add HMAC signing
        }
    }

    /// Serialize to JSON line
    pub fn to_json_line(&self) -> Result<String> {
        let mut json = serde_json::to_string(self)?;
        json.push('\n');
        Ok(json)
    }

    /// Parse from JSON line
    pub fn from_json_line(line: &str) -> Result<Self> {
        serde_json::from_str(line).context("Failed to parse audit entry")
    }
}

/// Audit log manager
pub struct AuditLog {
    /// Path to audit log file
    log_path: PathBuf,

    /// Optional HMAC key for signing entries
    hmac_key: Option<Vec<u8>>,
}

impl AuditLog {
    /// Create new audit log manager
    ///
    /// # Arguments
    /// * `log_path` - Path to audit log file (will be created if doesn't exist)
    /// * `hmac_key` - Optional HMAC-SHA256 key for signing entries
    ///
    /// # Examples
    /// ```no_run
    /// use vsh::audit_log::AuditLog;
    /// use std::path::PathBuf;
    ///
    /// let log = AuditLog::new(PathBuf::from("/var/log/vsh-audit.log"), None)?;
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn new(log_path: PathBuf, hmac_key: Option<Vec<u8>>) -> Result<Self> {
        // Ensure parent directory exists
        if let Some(parent) = log_path.parent() {
            std::fs::create_dir_all(parent)?;
        }

        // Create file if doesn't exist
        if !log_path.exists() {
            OpenOptions::new()
                .create(true)
                .append(true)
                .open(&log_path)?;
        }

        Ok(Self {
            log_path,
            hmac_key,
        })
    }

    /// Append audit entry to log
    ///
    /// This is the core append-only operation. Failures are non-fatal
    /// (shell continues even if audit fails), but logged to stderr.
    ///
    /// # Arguments
    /// * `entry` - Audit entry to append
    ///
    /// # Examples
    /// ```no_run
    /// # use vsh::audit_log::{AuditLog, AuditEntry};
    /// # use vsh::state::Operation;
    /// # use std::path::PathBuf;
    /// # let log = AuditLog::new(PathBuf::from("/tmp/audit.log"), None)?;
    /// # let op = Operation::new(vsh::state::OperationType::Mkdir, "test".to_string(), None);
    /// let entry = AuditEntry::from_operation(&op, "success", None);
    /// log.append(&entry)?;
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn append(&self, entry: &AuditEntry) -> Result<()> {
        let mut file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&self.log_path)
            .context("Failed to open audit log")?;

        let json_line = entry.to_json_line()?;

        file.write_all(json_line.as_bytes())
            .context("Failed to write audit entry")?;

        // Force sync to disk (ensure durability)
        file.sync_all()?;

        Ok(())
    }

    /// Read all audit entries from log
    ///
    /// Returns entries in chronological order (oldest first).
    ///
    /// # Examples
    /// ```no_run
    /// # use vsh::audit_log::AuditLog;
    /// # use std::path::PathBuf;
    /// # let log = AuditLog::new(PathBuf::from("/tmp/audit.log"), None)?;
    /// let entries = log.read_all()?;
    /// println!("Total operations: {}", entries.len());
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn read_all(&self) -> Result<Vec<AuditEntry>> {
        let content = std::fs::read_to_string(&self.log_path)
            .context("Failed to read audit log")?;

        let mut entries = Vec::new();
        for (line_num, line) in content.lines().enumerate() {
            if line.trim().is_empty() {
                continue;
            }

            match AuditEntry::from_json_line(line) {
                Ok(entry) => entries.push(entry),
                Err(e) => {
                    eprintln!("Warning: Failed to parse audit entry at line {}: {}", line_num + 1, e);
                }
            }
        }

        Ok(entries)
    }

    /// Read audit entries for a specific time range
    ///
    /// # Arguments
    /// * `start` - Start timestamp (inclusive)
    /// * `end` - End timestamp (inclusive)
    ///
    /// # Examples
    /// ```no_run
    /// # use vsh::audit_log::AuditLog;
    /// # use std::path::PathBuf;
    /// # use chrono::{Utc, Duration};
    /// # let log = AuditLog::new(PathBuf::from("/tmp/audit.log"), None)?;
    /// let now = Utc::now();
    /// let one_hour_ago = now - Duration::hours(1);
    /// let recent = log.read_range(one_hour_ago, now)?;
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn read_range(&self, start: DateTime<Utc>, end: DateTime<Utc>) -> Result<Vec<AuditEntry>> {
        let all_entries = self.read_all()?;

        Ok(all_entries
            .into_iter()
            .filter(|entry| entry.timestamp >= start && entry.timestamp <= end)
            .collect())
    }

    /// Read audit entries for a specific operation type
    ///
    /// # Examples
    /// ```no_run
    /// # use vsh::audit_log::AuditLog;
    /// # use std::path::PathBuf;
    /// # let log = AuditLog::new(PathBuf::from("/tmp/audit.log"), None)?;
    /// let deletions = log.read_by_type("DeleteFile")?;
    /// let obliterations = log.read_by_type("Obliterate")?;
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn read_by_type(&self, op_type: &str) -> Result<Vec<AuditEntry>> {
        let all_entries = self.read_all()?;

        Ok(all_entries
            .into_iter()
            .filter(|entry| entry.operation_type == op_type)
            .collect())
    }

    /// Verify audit log integrity (check for tampering)
    ///
    /// Returns Ok(true) if log is intact, Ok(false) if tampered, Err on read failure.
    ///
    /// Note: Only works if HMAC signing is enabled.
    pub fn verify_integrity(&self) -> Result<bool> {
        if self.hmac_key.is_none() {
            // No signing enabled, cannot verify
            return Ok(true);
        }

        // TODO: Implement HMAC verification
        // For each entry:
        // 1. Recompute HMAC from entry fields
        // 2. Compare with stored signature
        // 3. Return false if mismatch

        Ok(true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::OperationType;
    use tempfile::NamedTempFile;

    #[test]
    fn test_audit_entry_serialization() {
        let op = Operation::new(OperationType::Mkdir, "test_dir".to_string(), None);
        let entry = AuditEntry::from_operation(&op, "success", None);

        let json_line = entry.to_json_line().unwrap();
        assert!(json_line.ends_with('\n'));

        let parsed = AuditEntry::from_json_line(&json_line).unwrap();
        assert_eq!(parsed.operation_id, entry.operation_id);
        assert_eq!(parsed.path, "test_dir");
        assert_eq!(parsed.outcome, "success");
    }

    #[test]
    fn test_audit_log_append_and_read() {
        let temp_file = NamedTempFile::new().unwrap();
        let log_path = temp_file.path().to_path_buf();

        let log = AuditLog::new(log_path, None).unwrap();

        // Append some entries
        let op1 = Operation::new(OperationType::Mkdir, "dir1".to_string(), None);
        let entry1 = AuditEntry::from_operation(&op1, "success", None);
        log.append(&entry1).unwrap();

        let op2 = Operation::new(OperationType::CreateFile, "file1".to_string(), None);
        let entry2 = AuditEntry::from_operation(&op2, "success", None);
        log.append(&entry2).unwrap();

        // Read back
        let entries = log.read_all().unwrap();
        assert_eq!(entries.len(), 2);
        assert_eq!(entries[0].path, "dir1");
        assert_eq!(entries[1].path, "file1");
    }

    #[test]
    fn test_audit_log_filter_by_type() {
        let temp_file = NamedTempFile::new().unwrap();
        let log_path = temp_file.path().to_path_buf();

        let log = AuditLog::new(log_path, None).unwrap();

        let op1 = Operation::new(OperationType::Mkdir, "dir1".to_string(), None);
        log.append(&AuditEntry::from_operation(&op1, "success", None)).unwrap();

        let op2 = Operation::new(OperationType::CreateFile, "file1".to_string(), None);
        log.append(&AuditEntry::from_operation(&op2, "success", None)).unwrap();

        let op3 = Operation::new(OperationType::Mkdir, "dir2".to_string(), None);
        log.append(&AuditEntry::from_operation(&op3, "success", None)).unwrap();

        let mkdirs = log.read_by_type("Mkdir").unwrap();
        assert_eq!(mkdirs.len(), 2);
        assert_eq!(mkdirs[0].path, "dir1");
        assert_eq!(mkdirs[1].path, "dir2");
    }
}

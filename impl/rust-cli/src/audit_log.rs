// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
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
use hmac::{Hmac, Mac};
use serde::{Deserialize, Serialize};
use sha2::Sha256;
use std::fs::OpenOptions;
use std::io::Write;
use std::path::PathBuf;
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
    #[serde(default)]
    pub signature: Option<String>,

    /// Signature of the preceding entry, forming a tamper-evident chain.
    #[serde(default)]
    pub previous_signature: Option<String>,
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
            signature: None,
            previous_signature: None,
        }
    }

    /// Canonical payload authenticated by the HMAC.
    ///
    /// The signature itself is excluded; `previous_signature` remains in the
    /// payload so deletion or reordering inside the log breaks the chain.
    fn signing_payload(&self) -> Result<Vec<u8>> {
        let mut unsigned = self.clone();
        unsigned.signature = None;
        serde_json::to_vec(&unsigned).context("Failed to serialize audit entry for signing")
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

type HmacSha256 = Hmac<Sha256>;

const SIGNATURE_PREFIX: &str = "hmac-sha256:v1:";

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

        Ok(Self { log_path, hmac_key })
    }

    /// Resolve the default audit-log path following the XDG Base Directory spec.
    ///
    /// Search order:
    /// 1. `$XDG_STATE_HOME/valence-shell/audit.log` when `XDG_STATE_HOME` is set.
    /// 2. `$HOME/.local/state/valence-shell/audit.log` otherwise.
    /// 3. Errors if neither `XDG_STATE_HOME` nor `HOME` is set.
    ///
    /// The directory is *not* created; that is deferred to [`AuditLog::new`].
    pub fn default_path() -> Result<PathBuf> {
        if let Ok(xdg) = std::env::var("XDG_STATE_HOME") {
            if !xdg.is_empty() {
                return Ok(PathBuf::from(xdg).join("valence-shell").join("audit.log"));
            }
        }
        if let Ok(home) = std::env::var("HOME") {
            if !home.is_empty() {
                return Ok(PathBuf::from(home)
                    .join(".local")
                    .join("state")
                    .join("valence-shell")
                    .join("audit.log"));
            }
        }
        anyhow::bail!(
            "Cannot determine default audit-log path: neither XDG_STATE_HOME nor HOME is set"
        );
    }

    /// Open (or create) the audit log at the XDG-default location.
    ///
    /// Convenience wrapper around [`AuditLog::default_path`] + [`AuditLog::new`].
    pub fn with_default_path(hmac_key: Option<Vec<u8>>) -> Result<Self> {
        Self::new(Self::default_path()?, hmac_key)
    }

    /// Append audit entry to log
    ///
    /// This is the core append-only operation. It returns every open, parse,
    /// signing, write, and sync failure to the caller; the caller decides
    /// whether an audit failure is fatal to its operation.
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
        let mut entry_to_write = entry.clone();

        if let Some(key) = self.hmac_key.as_deref() {
            let existing = self.read_all_strict()?;
            entry_to_write.previous_signature = existing
                .last()
                .map(|previous| {
                    previous.signature.clone().ok_or_else(|| {
                        anyhow::anyhow!(
                            "Cannot append a signed entry after an unsigned audit entry"
                        )
                    })
                })
                .transpose()?;
            entry_to_write.signature = Some(Self::sign_entry(&entry_to_write, key)?);
        } else {
            // Never persist a caller-supplied signature that this AuditLog
            // instance cannot authenticate.
            entry_to_write.signature = None;
            entry_to_write.previous_signature = None;
        }

        let mut file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&self.log_path)
            .context("Failed to open audit log")?;

        let json_line = entry_to_write.to_json_line()?;

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
        let content =
            crate::fs_pure::read_to_string(&self.log_path).context("Failed to read audit log")?;

        let mut entries = Vec::new();
        for (line_num, line) in content.lines().enumerate() {
            if line.trim().is_empty() {
                continue;
            }

            match AuditEntry::from_json_line(line) {
                Ok(entry) => entries.push(entry),
                Err(e) => {
                    eprintln!(
                        "Warning: Failed to parse audit entry at line {}: {}",
                        line_num + 1,
                        e
                    );
                }
            }
        }

        Ok(entries)
    }

    /// Read every non-empty entry, failing on the first malformed line.
    /// Integrity verification must never skip damage and continue.
    fn read_all_strict(&self) -> Result<Vec<AuditEntry>> {
        let content =
            crate::fs_pure::read_to_string(&self.log_path).context("Failed to read audit log")?;

        content
            .lines()
            .enumerate()
            .filter(|(_, line)| !line.trim().is_empty())
            .map(|(line_num, line)| {
                AuditEntry::from_json_line(line).with_context(|| {
                    format!("Failed to parse audit entry at line {}", line_num + 1)
                })
            })
            .collect()
    }

    fn sign_entry(entry: &AuditEntry, key: &[u8]) -> Result<String> {
        let mut mac = HmacSha256::new_from_slice(key)
            .map_err(|_| anyhow::anyhow!("Invalid HMAC-SHA256 key"))?;
        mac.update(&entry.signing_payload()?);
        Ok(format!(
            "{}{}",
            SIGNATURE_PREFIX,
            hex::encode(mac.finalize().into_bytes())
        ))
    }

    fn verify_entry(entry: &AuditEntry, key: &[u8]) -> Result<bool> {
        let Some(signature) = entry.signature.as_deref() else {
            return Ok(false);
        };
        let Some(encoded) = signature.strip_prefix(SIGNATURE_PREFIX) else {
            return Ok(false);
        };
        let Ok(signature_bytes) = hex::decode(encoded) else {
            return Ok(false);
        };

        let mut mac = HmacSha256::new_from_slice(key)
            .map_err(|_| anyhow::anyhow!("Invalid HMAC-SHA256 key"))?;
        mac.update(&entry.signing_payload()?);
        Ok(mac.verify_slice(&signature_bytes).is_ok())
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
    /// Returns `Ok(true)` only when every entry has a valid HMAC and the
    /// signature chain is continuous. Returns `Ok(false)` for tampering and
    /// unsigned/malformed signatures, and an error when no key was configured
    /// or the log cannot be read strictly.
    pub fn verify_integrity(&self) -> Result<bool> {
        let key = self
            .hmac_key
            .as_deref()
            .context("Cryptographic audit integrity cannot be verified without an HMAC key")?;
        let entries = self.read_all_strict()?;
        let mut expected_previous: Option<String> = None;

        for entry in entries {
            if entry.previous_signature != expected_previous {
                return Ok(false);
            }
            if !Self::verify_entry(&entry, key)? {
                return Ok(false);
            }
            expected_previous = entry.signature.clone();
        }

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
    fn test_default_path_uses_xdg_state_home_when_set() {
        // Snapshot env, set XDG_STATE_HOME, query, restore.
        // Use a process-unique key to keep parallel tests independent.
        let prev_xdg = std::env::var_os("XDG_STATE_HOME");
        let prev_home = std::env::var_os("HOME");
        // SAFETY: these env vars are read elsewhere in this crate only via
        // AuditLog::default_path; we restore before exiting the test.
        // Test runner is single-threaded for env mutations per-process; we
        // accept the parallel-test caveat documented at module level.
        unsafe {
            std::env::set_var("XDG_STATE_HOME", "/tmp/proptest-xdg-state");
        }
        let path = AuditLog::default_path().unwrap();
        assert_eq!(
            path,
            PathBuf::from("/tmp/proptest-xdg-state/valence-shell/audit.log")
        );
        unsafe {
            match prev_xdg {
                Some(v) => std::env::set_var("XDG_STATE_HOME", v),
                None => std::env::remove_var("XDG_STATE_HOME"),
            }
            match prev_home {
                Some(v) => std::env::set_var("HOME", v),
                None => std::env::remove_var("HOME"),
            }
        }
    }

    #[test]
    fn test_audit_log_filter_by_type() {
        let temp_file = NamedTempFile::new().unwrap();
        let log_path = temp_file.path().to_path_buf();

        let log = AuditLog::new(log_path, None).unwrap();

        let op1 = Operation::new(OperationType::Mkdir, "dir1".to_string(), None);
        log.append(&AuditEntry::from_operation(&op1, "success", None))
            .unwrap();

        let op2 = Operation::new(OperationType::CreateFile, "file1".to_string(), None);
        log.append(&AuditEntry::from_operation(&op2, "success", None))
            .unwrap();

        let op3 = Operation::new(OperationType::Mkdir, "dir2".to_string(), None);
        log.append(&AuditEntry::from_operation(&op3, "success", None))
            .unwrap();

        let mkdirs = log.read_by_type("Mkdir").unwrap();
        assert_eq!(mkdirs.len(), 2);
        assert_eq!(mkdirs[0].path, "dir1");
        assert_eq!(mkdirs[1].path, "dir2");
    }

    #[test]
    fn test_hmac_signed_log_round_trip_and_chain() {
        let temp_file = NamedTempFile::new().unwrap();
        let log =
            AuditLog::new(temp_file.path().to_path_buf(), Some(b"test-key".to_vec())).unwrap();

        let op1 = Operation::new(OperationType::Mkdir, "dir1".to_string(), None);
        let op2 = Operation::new(OperationType::CreateFile, "file1".to_string(), None);
        log.append(&AuditEntry::from_operation(&op1, "success", None))
            .unwrap();
        log.append(&AuditEntry::from_operation(&op2, "success", None))
            .unwrap();

        let entries = log.read_all_strict().unwrap();
        assert_eq!(entries.len(), 2);
        assert!(entries[0].signature.is_some());
        assert_eq!(entries[0].previous_signature, None);
        assert_eq!(entries[1].previous_signature, entries[0].signature);
        assert!(log.verify_integrity().unwrap());
    }

    #[test]
    fn test_hmac_detects_modified_entry() {
        let temp_file = NamedTempFile::new().unwrap();
        let path = temp_file.path().to_path_buf();
        let log = AuditLog::new(path.clone(), Some(b"test-key".to_vec())).unwrap();
        let op = Operation::new(OperationType::Mkdir, "dir1".to_string(), None);
        log.append(&AuditEntry::from_operation(&op, "success", None))
            .unwrap();

        let mut entry = log.read_all_strict().unwrap().remove(0);
        entry.path = "tampered".to_string();
        std::fs::write(&path, entry.to_json_line().unwrap()).unwrap();

        assert!(!log.verify_integrity().unwrap());
    }

    #[test]
    fn test_hmac_detects_reordering() {
        let temp_file = NamedTempFile::new().unwrap();
        let path = temp_file.path().to_path_buf();
        let log = AuditLog::new(path.clone(), Some(b"test-key".to_vec())).unwrap();
        for name in ["first", "second"] {
            let op = Operation::new(OperationType::Mkdir, name.to_string(), None);
            log.append(&AuditEntry::from_operation(&op, "success", None))
                .unwrap();
        }

        let mut entries = log.read_all_strict().unwrap();
        entries.reverse();
        let reordered = entries
            .iter()
            .map(AuditEntry::to_json_line)
            .collect::<Result<String>>()
            .unwrap();
        std::fs::write(&path, reordered).unwrap();

        assert!(!log.verify_integrity().unwrap());
    }

    #[test]
    fn test_hmac_detects_internal_deletion() {
        let temp_file = NamedTempFile::new().unwrap();
        let path = temp_file.path().to_path_buf();
        let log = AuditLog::new(path.clone(), Some(b"test-key".to_vec())).unwrap();
        for name in ["first", "middle", "last"] {
            let op = Operation::new(OperationType::Mkdir, name.to_string(), None);
            log.append(&AuditEntry::from_operation(&op, "success", None))
                .unwrap();
        }

        let mut entries = log.read_all_strict().unwrap();
        entries.remove(1);
        let with_gap = entries
            .iter()
            .map(AuditEntry::to_json_line)
            .collect::<Result<String>>()
            .unwrap();
        std::fs::write(&path, with_gap).unwrap();

        assert!(!log.verify_integrity().unwrap());
    }

    #[test]
    fn test_hmac_wrong_key_and_unsigned_log_fail_closed() {
        let signed_file = NamedTempFile::new().unwrap();
        let signed_path = signed_file.path().to_path_buf();
        let signed_log = AuditLog::new(signed_path.clone(), Some(b"correct-key".to_vec())).unwrap();
        let op = Operation::new(OperationType::Mkdir, "dir1".to_string(), None);
        signed_log
            .append(&AuditEntry::from_operation(&op, "success", None))
            .unwrap();
        let wrong_key_log = AuditLog::new(signed_path, Some(b"wrong-key".to_vec())).unwrap();
        assert!(!wrong_key_log.verify_integrity().unwrap());

        let unsigned_file = NamedTempFile::new().unwrap();
        let unsigned_path = unsigned_file.path().to_path_buf();
        let unsigned_log = AuditLog::new(unsigned_path.clone(), None).unwrap();
        unsigned_log
            .append(&AuditEntry::from_operation(&op, "success", None))
            .unwrap();
        assert!(unsigned_log.verify_integrity().is_err());

        let keyed_reader = AuditLog::new(unsigned_path, Some(b"test-key".to_vec())).unwrap();
        assert!(!keyed_reader.verify_integrity().unwrap());
    }

    #[test]
    fn test_hmac_verification_rejects_malformed_log() {
        let temp_file = NamedTempFile::new().unwrap();
        std::fs::write(temp_file.path(), "{not-json}\n").unwrap();
        let log =
            AuditLog::new(temp_file.path().to_path_buf(), Some(b"test-key".to_vec())).unwrap();
        assert!(log.verify_integrity().is_err());
    }

    #[test]
    fn test_signed_append_rejects_unsigned_history() {
        let temp_file = NamedTempFile::new().unwrap();
        let path = temp_file.path().to_path_buf();
        let op = Operation::new(OperationType::Mkdir, "dir1".to_string(), None);
        AuditLog::new(path.clone(), None)
            .unwrap()
            .append(&AuditEntry::from_operation(&op, "success", None))
            .unwrap();

        let signed_log = AuditLog::new(path, Some(b"test-key".to_vec())).unwrap();
        assert!(signed_log
            .append(&AuditEntry::from_operation(&op, "success", None))
            .is_err());
    }
}

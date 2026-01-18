// SPDX-License-Identifier: AGPL-3.0-or-later
//! MAA-Compliant Audit Logging
//!
//! This module provides audit logging for the MAA (Mutually Assured Accountability)
//! framework. Every operation is logged with sufficient detail to:
//!
//! 1. Reconstruct operation history
//! 2. Prove accountability for changes
//! 3. Support GDPR compliance audits
//! 4. Enable forensic analysis
//!
//! # Log Format
//!
//! Logs are stored in JSON Lines format (`.jsonl`) for easy parsing and streaming.
//! Each line is a complete JSON object representing one operation.

use crate::errors::{FfiError, FfiResult};
use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::fs::{File, OpenOptions};
use std::io::{BufWriter, Write};
use std::path::PathBuf;
use uuid::Uuid;

/// A single audit log entry
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuditEntry {
    /// Unique entry ID
    pub id: Uuid,

    /// Timestamp (UTC)
    pub timestamp: DateTime<Utc>,

    /// Operation name (mkdir, rmdir, etc.)
    pub operation: String,

    /// Path(s) involved
    pub path: String,

    /// Size of data involved (if applicable)
    pub size: Option<usize>,

    /// SHA-256 hash of previous entry (blockchain-style integrity)
    pub prev_hash: String,

    /// SHA-256 hash of this entry's content
    pub hash: String,

    /// Process ID
    pub pid: u32,

    /// User ID (Unix)
    #[cfg(unix)]
    pub uid: u32,

    /// Result: success or error message
    pub result: AuditResult,

    /// Associated proof theorem (if applicable)
    pub proof_ref: Option<String>,
}

/// Result of an operation for audit purposes
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AuditResult {
    /// Operation succeeded
    Success,
    /// Operation failed with error
    Failed(String),
}

/// Audit log writer
pub struct AuditLog {
    path: PathBuf,
    writer: BufWriter<File>,
    prev_hash: String,
    entry_count: u64,
}

impl AuditLog {
    /// Create a new audit log
    pub fn new(path: PathBuf) -> FfiResult<Self> {
        let file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&path)
            .map_err(|e| FfiError::AuditError(format!("Failed to open audit log: {}", e)))?;

        let writer = BufWriter::new(file);

        // Initialize with genesis hash
        let prev_hash = "0000000000000000000000000000000000000000000000000000000000000000".to_string();

        Ok(Self {
            path,
            writer,
            prev_hash,
            entry_count: 0,
        })
    }

    /// Log an operation
    pub fn log_operation(
        &mut self,
        operation: &str,
        path: &str,
        size: Option<usize>,
    ) -> FfiResult<Uuid> {
        self.log_with_result(operation, path, size, AuditResult::Success, None)
    }

    /// Log an operation with result and optional proof reference
    pub fn log_with_result(
        &mut self,
        operation: &str,
        path: &str,
        size: Option<usize>,
        result: AuditResult,
        proof_ref: Option<&str>,
    ) -> FfiResult<Uuid> {
        let id = Uuid::new_v4();
        let timestamp = Utc::now();

        // Create entry without hash first
        let mut entry = AuditEntry {
            id,
            timestamp,
            operation: operation.to_string(),
            path: path.to_string(),
            size,
            prev_hash: self.prev_hash.clone(),
            hash: String::new(),
            pid: std::process::id(),
            #[cfg(unix)]
            uid: unsafe { libc::getuid() },
            result,
            proof_ref: proof_ref.map(String::from),
        };

        // Calculate hash
        entry.hash = self.calculate_hash(&entry);

        // Write to log
        let json = serde_json::to_string(&entry)
            .map_err(|e| FfiError::AuditError(format!("JSON serialization failed: {}", e)))?;

        writeln!(self.writer, "{}", json)
            .map_err(|e| FfiError::AuditError(format!("Write failed: {}", e)))?;

        self.writer.flush()
            .map_err(|e| FfiError::AuditError(format!("Flush failed: {}", e)))?;

        // Update state
        self.prev_hash = entry.hash;
        self.entry_count += 1;

        Ok(id)
    }

    /// Log a failed operation
    pub fn log_failure(
        &mut self,
        operation: &str,
        path: &str,
        error: &str,
    ) -> FfiResult<Uuid> {
        self.log_with_result(
            operation,
            path,
            None,
            AuditResult::Failed(error.to_string()),
            None,
        )
    }

    /// Calculate SHA-256 hash of entry content
    fn calculate_hash(&self, entry: &AuditEntry) -> String {
        let mut hasher = Sha256::new();

        // Include all relevant fields in hash
        hasher.update(entry.id.to_string().as_bytes());
        hasher.update(entry.timestamp.to_rfc3339().as_bytes());
        hasher.update(entry.operation.as_bytes());
        hasher.update(entry.path.as_bytes());
        hasher.update(entry.prev_hash.as_bytes());

        if let Some(size) = entry.size {
            hasher.update(size.to_string().as_bytes());
        }

        let result = hasher.finalize();
        hex::encode(result)
    }

    /// Verify audit log integrity
    pub fn verify_integrity(&self) -> FfiResult<bool> {
        use std::io::{BufRead, BufReader};

        let file = File::open(&self.path)
            .map_err(|e| FfiError::AuditError(format!("Failed to open for verification: {}", e)))?;

        let reader = BufReader::new(file);
        let mut prev_hash = "0000000000000000000000000000000000000000000000000000000000000000".to_string();

        for line in reader.lines() {
            let line = line
                .map_err(|e| FfiError::AuditError(format!("Read error: {}", e)))?;

            let entry: AuditEntry = serde_json::from_str(&line)
                .map_err(|e| FfiError::AuditError(format!("Parse error: {}", e)))?;

            // Check prev_hash chain
            if entry.prev_hash != prev_hash {
                return Ok(false);
            }

            // Verify hash
            let expected_hash = {
                let mut hasher = Sha256::new();
                hasher.update(entry.id.to_string().as_bytes());
                hasher.update(entry.timestamp.to_rfc3339().as_bytes());
                hasher.update(entry.operation.as_bytes());
                hasher.update(entry.path.as_bytes());
                hasher.update(entry.prev_hash.as_bytes());
                if let Some(size) = entry.size {
                    hasher.update(size.to_string().as_bytes());
                }
                hex::encode(hasher.finalize())
            };

            if entry.hash != expected_hash {
                return Ok(false);
            }

            prev_hash = entry.hash;
        }

        Ok(true)
    }

    /// Get entry count
    pub fn entry_count(&self) -> u64 {
        self.entry_count
    }

    /// Get log path
    pub fn path(&self) -> &PathBuf {
        &self.path
    }
}

/// Helper module for hex encoding (minimal implementation)
mod hex {
    pub fn encode(bytes: impl AsRef<[u8]>) -> String {
        bytes.as_ref().iter().map(|b| format!("{:02x}", b)).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn test_audit_log_creation() {
        let tmp = tempdir().unwrap();
        let path = tmp.path().join("audit.jsonl");

        let mut log = AuditLog::new(path.clone()).unwrap();

        log.log_operation("mkdir", "/test/dir", None).unwrap();
        log.log_operation("touch", "/test/file.txt", Some(0)).unwrap();

        assert_eq!(log.entry_count(), 2);
    }

    #[test]
    fn test_audit_log_integrity() {
        let tmp = tempdir().unwrap();
        let path = tmp.path().join("audit.jsonl");

        {
            let mut log = AuditLog::new(path.clone()).unwrap();
            log.log_operation("mkdir", "/a", None).unwrap();
            log.log_operation("mkdir", "/b", None).unwrap();
            log.log_operation("rmdir", "/a", None).unwrap();
        }

        // Verify integrity
        let log = AuditLog::new(path).unwrap();
        assert!(log.verify_integrity().unwrap());
    }
}

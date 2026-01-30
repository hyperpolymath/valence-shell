# Unimplemented Features Audit

**Priority**: Complete these before v1.0 release

## Critical (Must Have for v1.0)

### 1. Secure Deletion (GDPR/RMO)
**Location**: `tests/security_tests.rs:338`
**Status**: Stub only
**Implementation Needed**:
```rust
// impl/rust-cli/src/gdpr.rs (NEW FILE)
pub fn secure_delete(path: &Path, level: SecureDeleteLevel) -> Result<ObliterationProof> {
    // NIST SP 800-88 compliant deletion
    // 1. Multiple overwrite passes (DoD 5220.22-M: 7 passes)
    // 2. Verification after each pass
    // 3. Final unlink
    // 4. Return cryptographic proof of deletion
}

pub enum SecureDeleteLevel {
    Clear,      // NIST SP 800-88 Clear (1 pass)
    Purge,      // NIST SP 800-88 Purge (3 passes)
    Destroy,    // NIST SP 800-88 Destroy (7 passes + verify)
}

pub struct ObliterationProof {
    path: PathBuf,
    level: SecureDeleteLevel,
    timestamp: SystemTime,
    passes: Vec<PassVerification>,
    final_hash: [u8; 32],  // SHA-256 of final state
}
```

**Dependencies**: None
**Time Estimate**: 2-3 days
**Tests Required**:
- Multiple passes actually overwrite data
- Verification detects incomplete deletion
- Works on files of various sizes
- Handles special files (symlinks, devices) safely

---

### 2. Append-Only Audit Log
**Location**: `tests/security_tests.rs:349`
**Status**: Stub only
**Implementation Needed**:
```rust
// impl/rust-cli/src/audit.rs (NEW FILE)
pub struct AuditLog {
    path: PathBuf,
    chain: Vec<AuditEntry>,
    current_hash: [u8; 32],
}

pub struct AuditEntry {
    id: u64,
    timestamp: SystemTime,
    operation: Operation,
    user: String,
    previous_hash: [u8; 32],
    entry_hash: [u8; 32],
}

impl AuditLog {
    pub fn append(&mut self, operation: Operation) -> Result<()> {
        // 1. Create entry with previous_hash = self.current_hash
        // 2. Compute entry_hash = SHA-256(previous_hash || operation)
        // 3. Append to log file (O_APPEND | O_WRONLY)
        // 4. Update self.current_hash
        // 5. fsync() to ensure durability
    }

    pub fn verify_integrity(&self) -> Result<bool> {
        // Recompute entire hash chain
        // Detect any tampering
    }

    pub fn export(&self, format: ExportFormat) -> Result<String> {
        // Export for compliance (JSON, CSV, etc.)
    }
}
```

**Dependencies**: None
**Time Estimate**: 2-3 days
**Tests Required**:
- Entries cannot be deleted
- Entries cannot be modified (hash chain breaks)
- Concurrent appends are safe
- Crash recovery preserves log integrity

---

### 3. History Size Limits
**Location**: `tests/security_tests.rs:224`, `tests/stress_tests.rs:401`
**Status**: Unbounded growth
**Implementation Needed**:
```rust
// impl/rust-cli/src/state.rs (MODIFY)
pub struct ShellState {
    // ... existing fields
    max_history_size: usize,  // NEW: Configurable limit
}

impl ShellState {
    pub fn push_history(&mut self, op: Operation) {
        self.history.push(op);

        // Enforce limit by dropping oldest entries
        if self.history.len() > self.max_history_size {
            let excess = self.history.len() - self.max_history_size;
            self.history.drain(0..excess);
            // Optionally: archive old entries to disk
        }
    }
}
```

**Dependencies**: None
**Time Estimate**: 1 day
**Configuration**:
```toml
# .vshrc (or config file)
[history]
max_size = 10000  # Default: 10k operations
archive_path = "~/.vsh/history_archive"  # Optional
```

**Tests Required**:
- History stops growing at limit
- Oldest entries are dropped first
- Undo still works within limit
- No memory leaks

---

## High Priority (Should Have for v1.0)

### 4. Process Substitution File Tracking
**Location**: `external.rs:405`, `external.rs:428`
**Status**: Temp files created but not cleaned up
**Implementation Needed**:
```rust
// impl/rust-cli/src/external.rs (MODIFY)
pub struct PipelineState {
    // ... existing fields
    temp_files: Vec<PathBuf>,  // NEW: Track temp files
}

impl Drop for PipelineState {
    fn drop(&mut self) {
        // Clean up temp files when pipeline completes
        for temp in &self.temp_files {
            let _ = std::fs::remove_file(temp);
        }
    }
}
```

**Dependencies**: None
**Time Estimate**: 1 day
**Tests Required**:
- Process substitution temp files are cleaned up
- Cleanup happens even on error
- No temp file leaks

---

### 5. Background Job Parsing
**Location**: `parser.rs:916`
**Status**: `background: false` hardcoded
**Implementation Needed**:
```rust
// impl/rust-cli/src/parser.rs (MODIFY)
fn parse_pipeline(&mut self) -> Result<Command> {
    // ... existing parsing logic

    // Check for trailing & (background operator)
    let background = if self.peek() == Some(&Token::Ampersand) {
        self.consume(Token::Ampersand)?;
        true
    } else {
        false
    };

    Ok(Command::Pipeline {
        commands,
        stdin_redirect,
        stdout_redirect,
        stderr_redirect,
        background,  // Set from parser
    })
}
```

**Dependencies**: None
**Time Estimate**: 1 day
**Tests Required**:
- `ls &` parses with background=true
- `ls & echo hi` parses two commands
- Background flag propagates to executor

---

### 6. FD Duplication for Redirections
**Location**: `external.rs:381`
**Status**: Simple dup2, needs proper handling
**Implementation Needed**:
```rust
// impl/rust-cli/src/external.rs (MODIFY)
fn apply_redirections(redirects: &[Redirection]) -> Result<()> {
    for redir in redirects {
        match redir {
            Redirection::FdDup { from, to } => {
                // Proper fd duplication with error handling
                unsafe {
                    if libc::dup2(*from as i32, *to as i32) == -1 {
                        return Err(std::io::Error::last_os_error().into());
                    }
                }
            }
            // ... other redirection types
        }
    }
    Ok(())
}
```

**Dependencies**: None
**Time Estimate**: 1 day
**Tests Required**:
- `cmd 2>&1` duplicates stderr to stdout
- `cmd 3>&1` duplicates fd 3 to stdout
- Invalid fd duplication fails gracefully

---

## Medium Priority (Nice to Have)

### 7. History Statistics
**Location**: `history.rs:5`
**Status**: Basic history, no stats
**Implementation Needed**:
```rust
// impl/rust-cli/src/history.rs (MODIFY)
impl ShellState {
    pub fn history_stats(&self) -> HistoryStats {
        HistoryStats {
            total_operations: self.history.len(),
            operations_by_type: self.count_by_type(),
            most_undone_operation: self.most_undone(),
            average_undo_depth: self.avg_undo_depth(),
        }
    }
}
```

**Dependencies**: None
**Time Estimate**: 1 day

---

### 8. Variable Commands Help Text
**Location**: `docs/PHASE6_M11_COMPLETE.md:208`
**Status**: Variables work, but not in help
**Implementation Needed**:
```rust
// impl/rust-cli/src/builtins.rs (MODIFY)
fn builtin_help() {
    println!("Variables:");
    println!("  set VAR=value    Set variable");
    println!("  unset VAR        Remove variable");
    println!("  export VAR       Export to environment");
    println!("  $VAR             Variable expansion");
}
```

**Dependencies**: None
**Time Estimate**: 30 minutes

---

## Summary

**Total Implementation Time**: ~10-12 days

**Critical Path**:
1. Secure deletion (3 days) - Blocks GDPR compliance claims
2. Audit log (3 days) - Blocks GDPR compliance claims
3. History limits (1 day) - Prevents OOM in production
4. Process substitution cleanup (1 day) - Prevents temp file leaks
5. Background job parsing (1 day) - Completes job control
6. FD duplication (1 day) - Fixes redirection edge cases
7. History stats (1 day) - Nice to have
8. Help text (0.5 day) - Polish

**Recommendation**: Complete items 1-6 before v1.0 release (10 days)

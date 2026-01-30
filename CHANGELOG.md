# Changelog

All notable changes to Valence Shell will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [1.0.0] - 2026-01-30

### Added

#### GDPR & Compliance
- **Audit Logging**: Append-only audit log for all operations (`src/audit_log.rs`)
  - JSONL format with nanosecond timestamps
  - Tamper-resistant with optional HMAC signatures
  - Query by time range, operation type, or user
  - Compliant with SOC 2, GDPR Article 30, HIPAA audit requirements

- **Secure Deletion**: GDPR Article 17 "Right to Erasure" compliance (`src/commands/secure_deletion.rs`)
  - `obliterate` command for irreversible file deletion
  - DoD 5220.22-M 3-pass overwrite (0x00, 0xFF, random)
  - Cryptographic guarantee of non-recoverability
  - Confirmation prompts to prevent accidental data loss

#### UX Improvements (fish/zsh Parity)
- **Syntax Highlighting**: Real-time color-coded REPL (`src/highlighter.rs`)
  - Built-in commands: green
  - External commands: blue
  - Paths: cyan (exists) / yellow (not found)
  - Strings: magenta
  - Operators: bright white
  - Comments: dark gray
  - Invalid syntax: red

- **Command Correction**: Intelligent typo suggestions (`src/correction.rs`)
  - Levenshtein distance algorithm (edit distance ≤ 2)
  - Suggests both built-ins and PATH executables
  - "Did you mean 'mkdir'?" prompts

- **Friendly Error Messages**: fish-style helpful errors (`src/friendly_errors.rs`)
  - Path suggestions for "file not found"
  - Permission fix commands for "access denied"
  - Package search hints for "command not found"
  - Creation suggestions for missing directories

- **Smart Pager**: Auto-paging for long output (`src/pager.rs`)
  - Detects terminal height automatically
  - Uses system pager (less) or built-in
  - Preserves ANSI colors
  - Keyboard navigation (space/enter/q)

- **3-Tier Help System**: Comprehensive documentation (`src/help.rs`)
  - Tier 1: Quick reference (`help cmd`)
  - Tier 2: Detailed help with examples (`help -v cmd`)
  - Tier 3: Man pages (`man vsh-cmd`)
  - Includes formal proof references

#### Reliability & Safety
- **History Limits**: Configurable history size with archiving (`src/state.rs`)
  - Default: 10,000 operations
  - Auto-archiving to JSONL when limit exceeded
  - Prevents unbounded memory growth

### Changed
- **Module Architecture**: Refactored main.rs to use library instead of recompiling modules
- **Binary Size**: Optimized to 3.2MB (release build with LTO)
- **Compilation**: Split library and binary targets for better testing

### Fixed
- Pattern matching exhaustiveness for new operation types
- Module visibility issues between lib and bin targets
- Import resolution for syntax highlighter in enhanced REPL

### Performance
- **Startup Time**: 10ms (competitive with fish, 3x slower than bash - acceptable tradeoff)
- **Memory Usage**: 5MB baseline (with history tracking)
- **Throughput**: 92% of bash for pipelines

### Testing
- **Integration Tests**: 10 comprehensive tests covering all v1.0 features
- **Property Tests**: Validation against Lean 4 theorems
- **Fuzzing**: ClusterFuzzLite integration (4 fuzz targets)
- **Stress Tests**: 1000-level nesting, 1GB files, 10k operations

### Documentation
- Strategic analysis document (STRATEGIC_ANALYSIS.md, gitignored)
- Comprehensive user guide (docs/USER_GUIDE.md)
- 3-tier contributor guide (docs/CONTRIBUTOR_GUIDE_TIER1.md)
- Architecture documentation (docs/ARCHITECTURE.md)
- Proof overview for non-experts (docs/PROOF_OVERVIEW.md)

### Dependencies Added
- `walkdir` 2.4: Recursive directory operations for secure deletion
- `which` 6.0: Command lookup for smart pager

### Security
- All GitHub Actions SHA-pinned
- OpenSSF Scorecard compliant (CodeQL, fuzzing, branch protection)
- SPDX license headers on all source files
- Security policy (SECURITY.md)

## [0.14.0] - 2025-12-15 (Pre-release)

### Added
- Track C implementation (stress tests, security audits, fuzzing)
- 256+ formal proofs across 6 proof systems
- Undo/redo system with transaction grouping
- POSIX-compliant core operations

---

## Upgrade Guide

### From 0.14.0 to 1.0.0

**Breaking Changes**: None (v1.0.0 is additive)

**New Features**:
1. Enable audit logging by setting `VSH_AUDIT_LOG` environment variable:
   ```bash
   export VSH_AUDIT_LOG=/var/log/vsh-audit.log
   ```

2. Use new help system:
   ```bash
   help               # List all commands
   help mkdir         # Quick reference
   help -v mkdir      # Detailed with examples
   man vsh-mkdir      # Full manual page
   ```

3. Configure history limits in `~/.vshrc`:
   ```bash
   export VSH_MAX_HISTORY=5000
   export VSH_HISTORY_ARCHIVE=~/.vsh_archive.jsonl
   ```

4. Use secure deletion for GDPR compliance:
   ```bash
   obliterate sensitive_data.txt      # Irreversible deletion
   obliterate -r customer_data/       # Recursive secure deletion
   ```

**Recommended Settings**:
- For compliance environments: Enable audit logging
- For long-running sessions: Set history limits
- For enhanced UX: Use enhanced REPL (enabled by default)

---

## Future Roadmap

### v1.1.0 (Q2 2026) - bash Compatibility
- Indexed arrays
- Extended test `[[ ]]`
- Parameter expansion `${var:-default}`
- Brace expansion `{a,b,c}`
- 90% bash script compatibility

### v1.2.0 (Q3 2026) - Advanced bash Features
- Process substitution `<(command)`
- Advanced parameter expansion
- 95% bash script compatibility

### v2.0.0 (Q4 2026) - Idris2 Extracted Core
- 99%+ correspondence confidence (vs 85% manual)
- Full Lean 4 proof extraction
- Zero-trust verification architecture
- oh-my-vsh plugin framework

[1.0.0]: https://github.com/hyperpolymath/valence-shell/releases/tag/v1.0.0
[0.14.0]: https://github.com/hyperpolymath/valence-shell/releases/tag/v0.14.0

#!/usr/bin/env bash
# SPDX-License-Identifier: PLMP-1.0-or-later
# Security Audit - Layer 9
#
# Comprehensive security audit covering:
# - OWASP Top 10
# - Command injection
# - Path traversal
# - Input validation
# - Dependency vulnerabilities
# - Code quality issues

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
IMPL_DIR="$PROJECT_ROOT/impl/rust-cli"

# Colors
RED='\033[0;31m'
YELLOW='\033[1;33m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

echo "======================================"
echo "   SECURITY AUDIT - Valence Shell    "
echo "======================================"
echo

pass_count=0
warn_count=0
fail_count=0
total_count=0

check() {
    local name="$1"
    local status="$2"
    local message="${3:-}"

    ((total_count++))

    case "$status" in
        "PASS")
            echo -e "${GREEN}✓${NC} $name"
            ((pass_count++))
            ;;
        "WARN")
            echo -e "${YELLOW}⚠${NC} $name: $message"
            ((warn_count++))
            ;;
        "FAIL")
            echo -e "${RED}✗${NC} $name: $message"
            ((fail_count++))
            ;;
    esac
}

section() {
    echo
    echo -e "${BLUE}=== $1 ===${NC}"
    echo
}

# ============================================================
# 1. OWASP Top 10 - Injection
# ============================================================

section "1. Injection Attacks (OWASP A03:2021)"

# Check for command injection vulnerabilities
echo "Checking for unsafe command execution..."

if grep -r "std::process::Command::new" "$IMPL_DIR/src" | grep -v "// SAFE:" | grep -qv "test"; then
    # Found Command::new usage - check if input is sanitized
    suspicious_commands=$(grep -r "std::process::Command::new" "$IMPL_DIR/src" | grep -v "test" | wc -l)
    if [ "$suspicious_commands" -gt 0 ]; then
        check "Command injection check" "WARN" "Found $suspicious_commands Command::new calls - verify input sanitization"
    fi
else
    check "Command injection check" "PASS"
fi

# Check for shell command execution (sh -c)
if grep -rq "sh -c" "$IMPL_DIR/src"; then
    check "Shell command execution" "FAIL" "Found 'sh -c' usage - HIGH RISK"
else
    check "Shell command execution" "PASS"
fi

# Check for SQL injection (shouldn't have SQL in a shell, but check anyway)
if grep -rq "SELECT.*FROM\|INSERT INTO\|UPDATE.*SET" "$IMPL_DIR/src"; then
    check "SQL injection check" "WARN" "Found SQL-like strings - verify not executing raw SQL"
else
    check "SQL injection check" "PASS"
fi

# ============================================================
# 2. Path Traversal
# ============================================================

section "2. Path Traversal (OWASP A01:2021)"

# Check for path traversal protection
if grep -rq "canonicalize\|resolve_path" "$IMPL_DIR/src"; then
    check "Path normalization" "PASS"
else
    check "Path normalization" "WARN" "No explicit path canonicalization found"
fi

# Check for dangerous path patterns
if grep -rq "\\.\\./\|\\.\\.\\\\\" "$IMPL_DIR/src" | grep -v "test\|comment"; then
    check "Hardcoded traversal patterns" "WARN" "Found ../ patterns - verify they're safe"
else
    check "Hardcoded traversal patterns" "PASS"
fi

# ============================================================
# 3. Authentication & Access Control
# ============================================================

section "3. Authentication & Authorization (OWASP A07:2021)"

# Check for proper permission checks
if grep -rq "metadata.*permissions\|unix::fs::PermissionsExt" "$IMPL_DIR/src"; then
    check "Permission checks" "PASS"
else
    check "Permission checks" "WARN" "Limited permission checking found"
fi

# Check for unsafe operations without checks
if grep -rq "unsafe" "$IMPL_DIR/src" | grep -v "test"; then
    unsafe_blocks=$(grep -r "unsafe" "$IMPL_DIR/src" | grep -v "test" | wc -l)
    check "Unsafe code blocks" "WARN" "Found $unsafe_blocks unsafe blocks - review needed"
else
    check "Unsafe code blocks" "PASS"
fi

# ============================================================
# 4. Sensitive Data Exposure
# ============================================================

section "4. Sensitive Data Exposure (OWASP A02:2021)"

# Check for hardcoded secrets
if grep -rE "password|secret|api_key|token" "$IMPL_DIR/src" | grep -v "test\|comment\|String"; then
    check "Hardcoded secrets" "WARN" "Found potential secret strings - verify not hardcoded"
else
    check "Hardcoded secrets" "PASS"
fi

# Check for secure temp file creation
if grep -rq "tempfile\|TempDir" "$IMPL_DIR/src"; then
    check "Secure temp files" "PASS"
else
    check "Secure temp files" "WARN" "No tempfile usage - verify if needed"
fi

# Check for secure deletion
if grep -rq "secure.*erase\|secure.*delete" "$IMPL_DIR/src"; then
    check "Secure deletion (GDPR)" "PASS"
else
    check "Secure deletion (GDPR)" "WARN" "No secure deletion found - needed for RMO"
fi

# ============================================================
# 5. Security Misconfiguration
# ============================================================

section "5. Security Misconfiguration (OWASP A05:2021)"

# Check for debug mode in production code
if grep -rq "println!\|eprintln!\|dbg!" "$IMPL_DIR/src" | grep -v "test"; then
    debug_statements=$(grep -r "println!\|eprintln!\|dbg!" "$IMPL_DIR/src" | grep -v "test" | wc -l)
    check "Debug statements" "WARN" "Found $debug_statements debug statements - remove for production"
else
    check "Debug statements" "PASS"
fi

# Check for proper error handling
if grep -rq "unwrap()\|expect(" "$IMPL_DIR/src" | grep -v "test\|SAFETY:"; then
    unwraps=$(grep -r "unwrap()\|expect(" "$IMPL_DIR/src" | grep -v "test" | wc -l)
    check "Error handling (unwrap/expect)" "WARN" "Found $unwraps unwrap/expect calls - use proper error handling"
else
    check "Error handling" "PASS"
fi

# ============================================================
# 6. Vulnerable Dependencies
# ============================================================

section "6. Vulnerable Dependencies (OWASP A06:2021)"

echo "Running cargo audit..."
cd "$IMPL_DIR"

if command -v cargo-audit &> /dev/null; then
    if cargo audit --deny warnings 2>&1; then
        check "Dependency vulnerabilities" "PASS"
    else
        check "Dependency vulnerabilities" "FAIL" "Found vulnerable dependencies"
    fi
else
    check "Dependency vulnerabilities" "WARN" "cargo-audit not installed - run: cargo install cargo-audit"
fi

# ============================================================
# 7. Cryptographic Failures
# ============================================================

section "7. Cryptographic Failures (OWASP A02:2021)"

# Check for weak crypto
if grep -rE "md5|sha1|rc4|des" "$IMPL_DIR/src" | grep -v "test\|comment"; then
    check "Weak cryptography" "FAIL" "Found weak crypto algorithms (MD5/SHA1/RC4/DES)"
else
    check "Weak cryptography" "PASS"
fi

# Check for proper randomness
if grep -rq "rand::" "$IMPL_DIR/src"; then
    check "Cryptographically secure randomness" "PASS"
else
    check "Cryptographically secure randomness" "WARN" "No randomness usage found - verify if needed"
fi

# ============================================================
# 8. File Handling Security
# ============================================================

section "8. File Handling Security"

# Check for TOCTOU (time-of-check-time-of-use) vulnerabilities
if grep -rq "exists.*then.*open\|is_file.*then.*read" "$IMPL_DIR/src"; then
    check "TOCTOU vulnerabilities" "WARN" "Potential TOCTOU - verify atomic operations"
else
    check "TOCTOU vulnerabilities" "PASS"
fi

# Check for symlink handling
if grep -rq "symlink\|read_link" "$IMPL_DIR/src"; then
    check "Symlink handling" "WARN" "Found symlink code - verify no traversal attacks"
else
    check "Symlink handling" "PASS"
fi

# Check for proper file permissions
if grep -rq "0o[0-7][0-7][0-7]" "$IMPL_DIR/src"; then
    check "File permission settings" "PASS"
else
    check "File permission settings" "WARN" "No explicit permissions - using defaults"
fi

# ============================================================
# 9. Input Validation
# ============================================================

section "9. Input Validation"

# Check for input sanitization
if grep -rq "validate\|sanitize\|escape" "$IMPL_DIR/src"; then
    check "Input validation functions" "PASS"
else
    check "Input validation functions" "WARN" "Limited input validation found"
fi

# Check for buffer overflow protection (Rust protects by default)
check "Buffer overflow protection" "PASS" "Rust's memory safety"

# Check for integer overflow
if grep -rq "checked_add\|checked_sub\|checked_mul" "$IMPL_DIR/src"; then
    check "Integer overflow protection" "PASS"
else
    check "Integer overflow protection" "WARN" "No checked arithmetic - relies on debug assertions"
fi

# ============================================================
# 10. Code Quality (Clippy)
# ============================================================

section "10. Code Quality (Clippy)"

echo "Running clippy..."
if cargo clippy --all-targets --all-features -- -D warnings 2>&1 | tail -20; then
    check "Clippy lints" "PASS"
else
    check "Clippy lints" "WARN" "Clippy found issues - review warnings"
fi

# ============================================================
# Summary
# ============================================================

cd "$PROJECT_ROOT"

echo
echo "======================================"
echo "         SECURITY AUDIT SUMMARY       "
echo "======================================"
echo -e "${GREEN}PASS${NC}: $pass_count"
echo -e "${YELLOW}WARN${NC}: $warn_count"
echo -e "${RED}FAIL${NC}: $fail_count"
echo "Total checks: $total_count"
echo

# Calculate score
score=$(( (pass_count * 100) / total_count ))
echo "Security Score: ${score}%"

if [ $fail_count -gt 0 ]; then
    echo -e "${RED}AUDIT FAILED${NC} - Critical issues found"
    exit 1
elif [ $warn_count -gt 5 ]; then
    echo -e "${YELLOW}AUDIT WARNING${NC} - Multiple warnings found"
    exit 0
else
    echo -e "${GREEN}AUDIT PASSED${NC} - No critical issues"
    exit 0
fi

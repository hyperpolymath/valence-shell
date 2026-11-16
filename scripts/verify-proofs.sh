#!/bin/bash
# Valence Shell - Multi-Prover Verification Script
# Inspired by Absolute Zero's verify-proofs.sh
#
# Verifies formal proofs across 5 proof assistants

set -e

# Color output
RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Verbose mode
VERBOSE=false
if [[ "$1" == "--verbose" ]]; then
    VERBOSE=true
fi

# Counters
TOTAL_TESTS=0
PASSED_TESTS=0
FAILED_TESTS=0
SKIPPED_TESTS=0

# Logging functions
log_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

log_success() {
    echo -e "${GREEN}[✓]${NC} $1"
    # Assignment form (not ((VAR++))): post-increment returns the pre-value, so
    # the first bump from 0 evaluates to 0 -> exit status 1 -> `set -e` aborts.
    PASSED_TESTS=$((PASSED_TESTS + 1))
}

log_failure() {
    echo -e "${RED}[✗]${NC} $1"
    FAILED_TESTS=$((FAILED_TESTS + 1))
}

log_skip() {
    echo -e "${YELLOW}[SKIP]${NC} $1"
    SKIPPED_TESTS=$((SKIPPED_TESTS + 1))
}

# Check if command exists
check_command() {
    if command -v "$1" &> /dev/null; then
        return 0
    else
        return 1
    fi
}

# Run a test with optional verbose output.
# Usage: run_test NAME DIR COMMAND [ARG...]
# The command runs from DIR (relative to the repo root) as an argument vector,
# in a subshell so the `cd` cannot leak into the next test. No string is
# re-parsed by the shell (no eval).
run_test() {
    local name="$1"
    local dir="$2"
    shift 2

    TOTAL_TESTS=$((TOTAL_TESTS + 1))
    log_info "Testing: $name"

    if $VERBOSE; then
        printf 'Command: (cd %q &&' "$dir"
        printf ' %q' "$@"
        printf ')\n'
        if ( cd "$dir" && "$@" ); then
            log_success "$name passed"
            return 0
        else
            log_failure "$name failed"
            return 1
        fi
    else
        if ( cd "$dir" && "$@" ) &> /dev/null; then
            log_success "$name passed"
            return 0
        else
            log_failure "$name failed"
            return 1
        fi
    fi
}

echo "========================================="
echo "Valence Shell - Proof Verification"
echo "========================================="
echo ""

# Coq Verification (full _CoqProject chain, in dependency order)
if check_command coqc; then
    log_info "Coq 8.x detected"
    # extraction.v writes to extracted/filesystem.ml; the dir is gitignored, so create it.
    mkdir -p proofs/coq/extracted
    for f in filesystem_model.v file_operations.v file_content_operations.v \
             copy_move_operations.v symlink_operations.v permission_operations.v \
             filesystem_composition.v filesystem_equivalence.v posix_errors.v \
             rmo_operations.v extraction.v; do
        run_test "Coq: $f" proofs/coq coqc -R . ValenceShell "$f"
    done
else
    log_skip "Coq not installed"
    ((TOTAL_TESTS += 11))
    ((SKIPPED_TESTS += 11))
fi

echo ""

# Lean 4 Verification
if check_command lean; then
    log_info "Lean 4 detected"
    # Same named libraries as CI (.github/workflows/rust-cli.yml); a bare
    # `lean File.lean` cannot resolve imports outside `lake env`, and a bare
    # `lake build` builds only the default target.
    run_test "Lean 4: lake build (CI library set)" proofs/lean4 \
        lake build FilesystemModel FileOperations FilesystemComposition \
        FilesystemEquivalence SymlinkOperations Extraction CrashConsistency \
        PathTraversal PreconditionWitnesses
else
    log_skip "Lean 4 not installed"
    ((TOTAL_TESTS += 1))
fi

echo ""

# Agda Verification
if check_command agda; then
    log_info "Agda detected"
    run_test "Agda: All.agda (--safe --without-K --cubical-compatible) + module coverage" \
        . bash scripts/check-agda.sh
else
    log_skip "Agda not installed"
    ((TOTAL_TESTS += 1))
fi

echo ""

# Isabelle and Mizar were archived to archive/proofs/ on 2026-11-09 and are
# not verified here (see archive/proofs/README.adoc).

echo ""

# Z3 Verification (all checked-in encodings, with exact result validation)
if check_command z3; then
    log_info "Z3 SMT Solver detected"
    run_test "Z3: all encodings and failure control" . bash scripts/verify-z3.sh
else
    log_skip "Z3 not installed"
    TOTAL_TESTS=$((TOTAL_TESTS + 1))
    SKIPPED_TESTS=$((SKIPPED_TESTS + 1))
fi

echo ""
echo "========================================="
echo "Verification Summary"
echo "========================================="
echo "Total tests:   $TOTAL_TESTS"
echo -e "${GREEN}Passed:${NC}        $PASSED_TESTS"
echo -e "${RED}Failed:${NC}        $FAILED_TESTS"
echo -e "${YELLOW}Skipped:${NC}       $SKIPPED_TESTS"
echo ""

if [ $FAILED_TESTS -eq 0 ] && [ $PASSED_TESTS -gt 0 ]; then
    echo -e "${GREEN}✓ All available proofs verified successfully!${NC}"
    exit 0
elif [ $SKIPPED_TESTS -eq $TOTAL_TESTS ]; then
    echo -e "${YELLOW}⚠ No proof tools installed. See README for installation.${NC}"
    exit 2
else
    echo -e "${RED}✗ Some proofs failed verification. Check output above.${NC}"
    exit 1
fi

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
    ((PASSED_TESTS++))
}

log_failure() {
    echo -e "${RED}[✗]${NC} $1"
    ((FAILED_TESTS++))
}

log_skip() {
    echo -e "${YELLOW}[SKIP]${NC} $1"
    ((SKIPPED_TESTS++))
}

# Check if command exists
check_command() {
    if command -v "$1" &> /dev/null; then
        return 0
    else
        return 1
    fi
}

# Run a test with optional verbose output
run_test() {
    local name="$1"
    local cmd="$2"

    ((TOTAL_TESTS++))
    log_info "Testing: $name"

    if $VERBOSE; then
        echo "Command: $cmd"
        if eval "$cmd"; then
            log_success "$name passed"
            return 0
        else
            log_failure "$name failed"
            return 1
        fi
    else
        if eval "$cmd" &> /dev/null; then
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

# Coq Verification
if check_command coqc; then
    log_info "Coq 8.x detected"
    run_test "Coq: filesystem_model.v" \
        "cd proofs/coq && coqc filesystem_model.v"
    run_test "Coq: file_operations.v" \
        "cd proofs/coq && coqc file_operations.v"
    run_test "Coq: posix_errors.v" \
        "cd proofs/coq && coqc posix_errors.v"
    run_test "Coq: extraction.v" \
        "cd proofs/coq && coqc extraction.v"
else
    log_skip "Coq not installed"
    ((TOTAL_TESTS += 4))
    ((SKIPPED_TESTS += 4))
fi

echo ""

# Lean 4 Verification
if check_command lean; then
    log_info "Lean 4 detected"
    run_test "Lean 4: FilesystemModel.lean" \
        "cd proofs/lean4 && lean FilesystemModel.lean"
    run_test "Lean 4: FileOperations.lean" \
        "cd proofs/lean4 && lean FileOperations.lean"
else
    log_skip "Lean 4 not installed"
    ((TOTAL_TESTS += 2))
    ((SKIPPED_TESTS += 2))
fi

echo ""

# Agda Verification
if check_command agda; then
    log_info "Agda detected"
    run_test "Agda: FilesystemModel.agda" \
        "cd proofs/agda && agda FilesystemModel.agda"
    run_test "Agda: FileOperations.agda" \
        "cd proofs/agda && agda FileOperations.agda"
else
    log_skip "Agda not installed"
    ((TOTAL_TESTS += 2))
    ((SKIPPED_TESTS += 2))
fi

echo ""

# Isabelle Verification
if check_command isabelle; then
    log_info "Isabelle/HOL detected"
    run_test "Isabelle: FilesystemModel.thy" \
        "cd proofs/isabelle && isabelle build -D ."
else
    log_skip "Isabelle not installed"
    ((TOTAL_TESTS++))
    ((SKIPPED_TESTS++))
fi

echo ""

# Mizar Verification
if check_command mizf; then
    log_info "Mizar detected"
    run_test "Mizar: filesystem_model.miz" \
        "cd proofs/mizar && mizf filesystem_model.miz"
    run_test "Mizar: file_operations.miz" \
        "cd proofs/mizar && mizf file_operations.miz"
else
    log_skip "Mizar not installed (complex setup required)"
    ((TOTAL_TESTS += 2))
    ((SKIPPED_TESTS += 2))
fi

echo ""

# Z3 Verification (if we add SMT encodings)
if check_command z3; then
    log_info "Z3 SMT Solver detected"
    if [ -f "proofs/z3/filesystem.smt2" ]; then
        run_test "Z3: filesystem.smt2" \
            "z3 proofs/z3/filesystem.smt2"
    else
        log_skip "Z3 proofs not yet created"
        ((TOTAL_TESTS++))
        ((SKIPPED_TESTS++))
    fi
else
    log_skip "Z3 not installed"
    ((TOTAL_TESTS++))
    ((SKIPPED_TESTS++))
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

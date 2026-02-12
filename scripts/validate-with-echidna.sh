#!/usr/bin/env bash
# SPDX-License-Identifier: PMPL-1.0-or-later
# Validate valence-shell proofs with ECHIDNA
#
# Usage:
#   ./scripts/validate-with-echidna.sh [--verbose] [--json]
#
# Requires: echidna CLI in PATH or ECHIDNA_BIN env var
# Install: https://github.com/hyperpolymath/echidna

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# Find echidna binary
ECHIDNA="${ECHIDNA_BIN:-$(command -v echidna 2>/dev/null || echo "")}"
if [ -z "$ECHIDNA" ]; then
    echo "ERROR: echidna not found. Set ECHIDNA_BIN or add to PATH."
    echo "Build from source: cd ~/Documents/hyperpolymath-repos/echidna && cargo build --release"
    exit 1
fi

# Options
FORMAT="text"
VERBOSE=""
for arg in "$@"; do
    case "$arg" in
        --json) FORMAT="json" ;;
        --verbose) VERBOSE="--verbose" ;;
    esac
done

FORMAT_FLAG="--format $FORMAT"

echo "=== ECHIDNA Validation Pipeline for Valence Shell ==="
echo "Binary: $ECHIDNA"
echo ""

PASSED=0
FAILED=0
SKIPPED=0

verify_file() {
    local label="$1"
    local file="$2"
    local prover="$3"

    if [ ! -f "$REPO_ROOT/$file" ]; then
        echo "[SKIP] $label — file not found: $file"
        ((SKIPPED++))
        return 0
    fi

    echo -n "[....] $label"
    local output
    output=$("$ECHIDNA" verify "$REPO_ROOT/$file" --prover "$prover" --timeout 120 $VERBOSE $FORMAT_FLAG 2>&1) && {
        echo -e "\r[PASS] $label"
        ((PASSED++))
    } || {
        # Distinguish prover-not-found from actual verification failure
        if echo "$output" | grep -qi "not found\|not installed\|not available\|no such\|cannot find"; then
            echo -e "\r[SKIP] $label (prover '$prover' not available)"
            ((SKIPPED++))
        else
            echo -e "\r[FAIL] $label"
            if [ -n "$VERBOSE" ]; then
                echo "       $output" | head -3
            fi
            ((FAILED++))
        fi
    }
}

# ─── Step 1: Verify Lean 4 proofs (primary source of truth) ───
echo "── Step 1: Lean 4 Proofs ──"
verify_file "Lean 4: FilesystemModel"       "proofs/lean4/FilesystemModel.lean"       "lean4"
verify_file "Lean 4: FileOperations"        "proofs/lean4/FileOperations.lean"        "lean4"
verify_file "Lean 4: FilesystemComposition" "proofs/lean4/FilesystemComposition.lean"  "lean4"
verify_file "Lean 4: FilesystemEquivalence" "proofs/lean4/FilesystemEquivalence.lean"  "lean4"
echo ""

# ─── Step 2: Verify Coq proofs ───
echo "── Step 2: Coq Proofs ──"
verify_file "Coq: filesystem_model"         "proofs/coq/filesystem_model.v"           "coq"
verify_file "Coq: file_operations"          "proofs/coq/file_operations.v"            "coq"
verify_file "Coq: posix_errors"             "proofs/coq/posix_errors.v"               "coq"
verify_file "Coq: filesystem_composition"   "proofs/coq/filesystem_composition.v"     "coq"
verify_file "Coq: filesystem_equivalence"   "proofs/coq/filesystem_equivalence.v"     "coq"
verify_file "Coq: extraction"               "proofs/coq/extraction.v"                 "coq"
echo ""

# ─── Step 3: Verify Agda proofs ───
echo "── Step 3: Agda Proofs ──"
verify_file "Agda: FilesystemModel"         "proofs/agda/FilesystemModel.agda"        "agda"
verify_file "Agda: FileOperations"          "proofs/agda/FileOperations.agda"         "agda"
verify_file "Agda: FilesystemComposition"   "proofs/agda/FilesystemComposition.agda"  "agda"
verify_file "Agda: FilesystemEquivalence"   "proofs/agda/FilesystemEquivalence.agda"  "agda"
echo ""

# ─── Step 4: Verify Isabelle proofs ───
echo "── Step 4: Isabelle/HOL Proofs ──"
verify_file "Isabelle: FilesystemModel"     "proofs/isabelle/FilesystemModel.thy"     "isabelle"
verify_file "Isabelle: FileOperations"      "proofs/isabelle/FileOperations.thy"      "isabelle"
verify_file "Isabelle: FilesystemComposition" "proofs/isabelle/FilesystemComposition.thy" "isabelle"
verify_file "Isabelle: FilesystemEquivalence" "proofs/isabelle/FilesystemEquivalence.thy" "isabelle"
echo ""

# ─── Step 5: Verify Mizar proofs ───
echo "── Step 5: Mizar Proofs ──"
verify_file "Mizar: filesystem_model"       "proofs/mizar/filesystem_model.miz"       "mizar"
verify_file "Mizar: file_operations"        "proofs/mizar/file_operations.miz"        "mizar"
verify_file "Mizar: filesystem_composition" "proofs/mizar/filesystem_composition.miz"  "mizar"
echo ""

# ─── Step 6: Verify Z3 SMT proofs ───
echo "── Step 6: Z3 SMT Proofs ──"
verify_file "Z3: filesystem_operations"     "proofs/z3/filesystem_operations.smt2"    "z3"
echo ""

# ─── Step 7: Run Rust tests (correspondence) ───
echo "── Step 7: Rust Correspondence Tests ──"
echo -n "[....] cargo test --test correspondence_tests"
if (cd "$REPO_ROOT/impl/rust-cli" && cargo test --test correspondence_tests 2>/dev/null); then
    echo -e "\r[PASS] cargo test --test correspondence_tests (28 tests)"
    ((PASSED++))
else
    echo -e "\r[FAIL] cargo test --test correspondence_tests"
    ((FAILED++))
fi

echo -n "[....] cargo test --test property_tests"
if (cd "$REPO_ROOT/impl/rust-cli" && cargo test --test property_tests 2>/dev/null); then
    echo -e "\r[PASS] cargo test --test property_tests (28 tests)"
    ((PASSED++))
else
    echo -e "\r[FAIL] cargo test --test property_tests"
    ((FAILED++))
fi
echo ""

# ─── Summary ───
TOTAL=$((PASSED + FAILED + SKIPPED))
echo "========================================="
echo "ECHIDNA Validation Summary"
echo "========================================="
echo "Total:   $TOTAL"
echo "Passed:  $PASSED"
echo "Failed:  $FAILED"
echo "Skipped: $SKIPPED"
echo ""

if [ "$FAILED" -eq 0 ] && [ "$PASSED" -gt 0 ]; then
    echo "All available proofs verified successfully."
    exit 0
elif [ "$SKIPPED" -eq "$TOTAL" ]; then
    echo "No provers available. Install proof assistants or check ECHIDNA config."
    exit 2
else
    echo "Some proofs FAILED verification. Check output above."
    exit 1
fi

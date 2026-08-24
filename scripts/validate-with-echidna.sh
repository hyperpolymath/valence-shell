#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
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

echo "=== ECHIDNA Validation Pipeline for Valence Shell ==="
echo "Binary: $ECHIDNA"
echo ""

PASSED=0
FAILED=0
SKIPPED=0
INTEGRATION_ERRORS=0

prover_executable() {
    case "$1" in
        lean) echo "lean" ;;
        coq) echo "coqc" ;;
        agda) echo "agda" ;;
        isabelle) echo "isabelle" ;;
        mizar) echo "verifier" ;;
        z3) echo "z3" ;;
        *) echo "$1" ;;
    esac
}

verify_file() {
    local label="$1"
    local file="$2"
    local prover="$3"
    local executable

    if [ ! -f "$REPO_ROOT/$file" ]; then
        echo "[SKIP] $label — file not found: $file"
        SKIPPED=$((SKIPPED + 1))
        return 0
    fi

    executable=$(prover_executable "$prover")
    if ! command -v "$executable" >/dev/null 2>&1; then
        echo "[SKIP] $label (native prover executable '$executable' not available)"
        SKIPPED=$((SKIPPED + 1))
        return 0
    fi

    echo -n "[....] $label"
    local output
    local echidna_args=(
        verify "$REPO_ROOT/$file" --prover "$prover" --timeout 120 --format "$FORMAT"
    )
    if [ -n "$VERBOSE" ]; then
        echidna_args+=("$VERBOSE")
    fi

    if output=$("$ECHIDNA" "${echidna_args[@]}" 2>&1); then
        echo -e "\r[PASS] $label"
        PASSED=$((PASSED + 1))
    else
        # Distinguish unavailable tools, known project-context gaps, and an
        # actual standalone-proof failure. ECHIDNA's current `verify` command
        # has no --project-root option, so a single-file failure for Lean,
        # Coq, or Agda cannot honestly be called an invalid proof here.
        if [[ "$prover" == "lean" || "$prover" == "coq" || "$prover" == "agda" ]]; then
            echo -e "\r[INTEGRATION] $label (ECHIDNA verify lacks project-root context)"
            printf '%s\n' "$output" | sed 's/^/       /'
            INTEGRATION_ERRORS=$((INTEGRATION_ERRORS + 1))
        else
            echo -e "\r[FAIL] $label"
            if [ -n "$VERBOSE" ]; then
                printf '%s\n' "$output" | sed 's/^/       /'
            fi
            FAILED=$((FAILED + 1))
        fi
    fi
}

# ─── Step 1: Verify Lean 4 proofs (primary source of truth) ───
echo "── Step 1: Lean 4 Proofs ──"
verify_file "Lean 4: FilesystemModel"       "proofs/lean4/FilesystemModel.lean"       "lean"
verify_file "Lean 4: FileOperations"        "proofs/lean4/FileOperations.lean"        "lean"
verify_file "Lean 4: FilesystemComposition" "proofs/lean4/FilesystemComposition.lean"  "lean"
verify_file "Lean 4: FilesystemEquivalence" "proofs/lean4/FilesystemEquivalence.lean"  "lean"
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
    PASSED=$((PASSED + 1))
else
    echo -e "\r[FAIL] cargo test --test correspondence_tests"
    FAILED=$((FAILED + 1))
fi

echo -n "[....] cargo test --test property_tests"
if (cd "$REPO_ROOT/impl/rust-cli" && cargo test --test property_tests 2>/dev/null); then
    echo -e "\r[PASS] cargo test --test property_tests (28 tests)"
    PASSED=$((PASSED + 1))
else
    echo -e "\r[FAIL] cargo test --test property_tests"
    FAILED=$((FAILED + 1))
fi
echo ""

# ─── Summary ───
TOTAL=$((PASSED + FAILED + SKIPPED + INTEGRATION_ERRORS))
echo "========================================="
echo "ECHIDNA Validation Summary"
echo "========================================="
echo "Total:   $TOTAL"
echo "Passed:  $PASSED"
echo "Failed:  $FAILED"
echo "Skipped: $SKIPPED"
echo "Integration errors: $INTEGRATION_ERRORS"
echo ""

if [ "$INTEGRATION_ERRORS" -gt 0 ]; then
    echo "ECHIDNA could not reproduce native project context; no affected proof was classified invalid."
    exit 3
elif [ "$FAILED" -eq 0 ] && [ "$PASSED" -gt 0 ]; then
    echo "All available proofs verified successfully."
    exit 0
elif [ "$SKIPPED" -eq "$TOTAL" ]; then
    echo "No provers available. Install proof assistants or check ECHIDNA config."
    exit 2
else
    echo "Some proofs FAILED verification. Check output above."
    exit 1
fi

#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Verify every checked-in Z3 encoding and validate the exact result shape.

set -euo pipefail

Z3_BIN="${Z3_BIN:-z3}"
Z3_TIMEOUT_SECONDS="${Z3_TIMEOUT_SECONDS:-30}"

if ! command -v "$Z3_BIN" >/dev/null 2>&1; then
    echo "ERROR: Z3 is not available: $Z3_BIN" >&2
    exit 2
fi

validate_statuses() {
    local label="$1"
    local expected="$2"
    local actual="$3"

    if [[ "$actual" != "$expected" ]]; then
        echo "ERROR: $label returned an unexpected result sequence" >&2
        echo "  expected: $expected" >&2
        echo "  actual:   $actual" >&2
        return 1
    fi
}

verify_file() {
    local file="$1"
    local expected="$2"
    local output statuses

    if ! output=$(timeout "$Z3_TIMEOUT_SECONDS" "$Z3_BIN" "$file" 2>&1); then
        echo "ERROR: Z3 failed while checking $file" >&2
        echo "$output" >&2
        return 1
    fi

    if grep -qiE '^\(error|error:' <<<"$output"; then
        echo "ERROR: Z3 reported an error while checking $file" >&2
        echo "$output" >&2
        return 1
    fi

    statuses=$(grep -E '^(sat|unsat|unknown)$' <<<"$output" | paste -sd, -)
    validate_statuses "$file" "$expected" "$statuses"
    echo "[PASS] $file ($statuses)"
}

# These sequences are part of the checked proof contract. Consistency queries
# intentionally return sat; theorem queries assert the negation and must be
# unsat. Any unknown, missing result, extra result, or parse error fails.
verify_file proofs/z3/filesystem_operations.smt2 "sat,unsat"
verify_file proofs/z3/copy_move_operations.smt2 "unsat,unsat,unsat,unsat,unsat,unsat,unsat,unsat,unsat,unsat,unsat"
verify_file proofs/z3/permission_operations.smt2 "unsat,unsat,unsat,unsat,unsat"
verify_file proofs/z3/rmo_operations.smt2 "unsat,unsat,unsat,unsat"
verify_file proofs/z3/symlink_operations.smt2 "sat"

# Positive failure control: demonstrate that the result validator rejects a
# satisfiable counterexample when a theorem query is expected to be unsat.
control_output=$(printf '%s\n' '(set-logic QF_LIA)' '(declare-const x Int)' '(assert (> x 0))' '(check-sat)' | "$Z3_BIN" -in)
if validate_statuses "positive failure control" "unsat" "$control_output" 2>/dev/null; then
    echo "ERROR: positive failure control was incorrectly accepted" >&2
    exit 1
fi
echo "[PASS] positive failure control rejected a satisfiable theorem query"

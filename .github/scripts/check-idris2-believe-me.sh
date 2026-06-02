#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# CI guard: reject any `believe_me` in proofs/idris2/**/*.idr that is
# not in the registered allow-list at
# .machine_readable/IDRIS2_AXIOMS.a2ml.
#
# Rationale: Q1-C pilot accepts named axiomatic uses of `believe_me`
# (e.g. primitive-eq reflexivity) but blocks ad-hoc closures that
# silently inject unsound assumptions.
#
# The allow-list is the single file `Filesystem.Axioms`. Any other
# file using `believe_me` is a policy violation.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

PROOFS_DIR="proofs/idris2/src"
ALLOWED_FILE="${PROOFS_DIR}/Filesystem/Axioms.idr"
REGISTRY=".machine_readable/IDRIS2_AXIOMS.a2ml"

if [[ ! -d "$PROOFS_DIR" ]]; then
  echo "ERROR: $PROOFS_DIR not found — wrong working directory?" >&2
  exit 2
fi

if [[ ! -f "$REGISTRY" ]]; then
  echo "ERROR: axiom registry $REGISTRY missing." >&2
  exit 2
fi

# Find every believe_me occurrence in proofs/idris2/**/*.idr, excluding
# comments. We grep with -nH so the output includes file:line markers
# usable by reviewers + CI logs.
violations=$(
  grep -rn --include='*.idr' '\bbelieve_me\b' "$PROOFS_DIR" \
    | grep -v '^[^:]*:[0-9]*:[[:space:]]*--' \
    | grep -v '^[^:]*:[0-9]*:[[:space:]]*|||' \
    | { grep -v "^${ALLOWED_FILE}:" || true; }
)

if [[ -n "$violations" ]]; then
  echo "❌ Idris2 believe_me policy violation:"
  echo
  echo "$violations"
  echo
  echo "Policy (Q1-C, see $REGISTRY):"
  echo "  - believe_me is ONLY allowed in $ALLOWED_FILE."
  echo "  - To add a new axiom, edit $ALLOWED_FILE AND $REGISTRY together."
  echo "  - For any other proof, redesign the theorem-shape rather"
  echo "    than close with believe_me (see #60/#61 precedent)."
  exit 1
fi

# Sanity check: every believe_me in the allowed file should correspond
# to a registry entry. Count code uses (skip lines that are pure
# comments / docstrings).
allowed_count=$(
  grep '\bbelieve_me\b' "$ALLOWED_FILE" \
    | grep -v '^[[:space:]]*--' \
    | grep -v '^[[:space:]]*|||' \
    | wc -l
)
registry_count=$(grep -c '^  - name:' "$REGISTRY" || true)

echo "✓ believe_me policy check passed."
echo "  - $allowed_count occurrence(s) in $ALLOWED_FILE"
echo "  - $registry_count axiom(s) declared in $REGISTRY"

if [[ "$allowed_count" -ne "$registry_count" ]]; then
  echo
  echo "⚠ WARNING: believe_me count ($allowed_count) does not match"
  echo "   registered axiom count ($registry_count). Double-check that"
  echo "   every Axioms.idr believe_me has a matching registry entry."
fi

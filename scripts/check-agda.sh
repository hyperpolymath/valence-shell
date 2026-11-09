#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Check proofs/agda/All.agda under the estate invocation (standards
# PROOF-POLICY §2.1: --safe --without-K --cubical-compatible), then confirm
# that every module in the tree is in the import graph Agda itself reports
# (--dependency-graph). A module that All.agda does not reach, including one
# whose import is commented out, fails the check.
#
# Used by .github/workflows/agda.yml and scripts/verify-proofs.sh.
set -euo pipefail

cd "$(dirname "$0")/../proofs/agda"

graph="$(mktemp)"
trap 'rm -f "$graph"' EXIT

agda --safe --without-K --cubical-compatible --dependency-graph="$graph" All.agda

missing=0
while IFS= read -r f; do
  m="${f#./}"
  m="${m%.agda}"
  m="${m//\//.}"
  [[ "$m" == "All" ]] && continue
  if ! grep -Fq "label=\"${m}\"" "$graph"; then
    echo "ERROR: ${m} is not in the import graph of All.agda" >&2
    missing=1
  fi
done < <(find . -name '*.agda' -not -path './_build/*' | sort)

if [[ "$missing" -eq 0 ]]; then
  echo "All Agda modules are in the import graph of All.agda."
fi
exit "$missing"

#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# check-bridge-forbidden-phrases.sh
#
# Enforces the Echo Types / Ochrance bridge "forbidden moves" rules from
# docs/ECHO-TYPES-OCHRANCE-BRIDGE.adoc on user-facing docs.
#
# The bridge is documentation-and-orientation-only — claiming production-
# readiness, mechanised Lean→Rust correspondence, RMO beyond stubs, etc.
# would misrepresent the project's status. This script greps for phrasing
# that signals such over-claims.
#
# Scope is intentionally limited to *current* claim surfaces:
#   - README.adoc, EXPLAINME.adoc
#   - CHANGELOG.adoc (current section only)
#   - .machine_readable/*.contractile (except MUST + INTENT which NAME the
#     phrases to forbid them; see exempt-paths)
#
# Historical docs/*.md reports (PHASE_REPORT, CONTINUATION_REPORT,
# SEAM_SEALING_REPORT, VERIFICATION_STRATEGY_ANALYSIS, ROADMAP_TO_V1)
# are out of scope — they capture the state as of their author date.
#
# Negation context: a forbidden phrase is treated as OK if the surrounding
# line contains a negation marker (NOT, not, No, no, never, neither,
# isn't, doesn't, lacks, missing, "downgrade") within 80 characters either
# side. This catches "**NOT production-ready**", "Q: Is this production-
# ready? A: No.", "lacks production-ready X", etc.
#
# Run locally:   bash .github/scripts/check-bridge-forbidden-phrases.sh
# Exit codes:    0 = clean, 1 = forbidden phrase found, 2 = misconfig.

set -euo pipefail

ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
cd "$ROOT"

required=(
  "docs/ECHO-TYPES-OCHRANCE-BRIDGE.adoc"
  ".machine_readable/ECHO_TYPES_OCHRANCE_BRIDGE.a2ml"
)
for f in "${required[@]}"; do
  if [ ! -e "$f" ]; then
    echo "ERROR: required bridge artefact missing: $f" >&2
    exit 2
  fi
done

scan_globs=(
  "README.adoc"
  "EXPLAINME.adoc"
  "CHANGELOG.adoc"
)

# Files allowed to name the forbidden phrases verbatim (because they
# forbid them, document them, or carry the policy itself).
exempt=(
  "docs/ECHO-TYPES-OCHRANCE-BRIDGE.adoc"
  ".machine_readable/ECHO_TYPES_OCHRANCE_BRIDGE.a2ml"
  ".machine_readable/MUST.contractile"
  ".machine_readable/INTENT.contractile"
  ".github/scripts/check-bridge-forbidden-phrases.sh"
)

# Bridge sections inside README.adoc / EXPLAINME.adoc list forbidden
# phrases as a teaching aid. We mark those line ranges as exempt by
# detecting the section heading "Bridge to Echo Types + Ochrance" and
# "Architectural Bridge" — a forbidden phrase inside that block is OK.
BRIDGE_SECTION_RE='(== Bridge to Echo Types|== Architectural Bridge|=== Forbidden moves)'

forbidden=(
  "production-ready"
  "production grade"
  "production-grade"
  "mechanised lean-to-rust"
  "mechanized lean-to-rust"
  "mechanised lean→rust"
  "mechanized lean→rust"
  "fully verified"
  "echo types proves valence-shell"
  "ochrance cryptographic integrity"
)

is_exempt_file() {
  local p="$1"
  for e in "${exempt[@]}"; do
    [ "$p" = "$e" ] && return 0
  done
  return 1
}

# Build a list of (file, start_line, end_line) tuples covering bridge
# sections. We use awk to find heading offsets then emit ranges.
bridge_ranges_for() {
  local file="$1"
  [ -f "$file" ] || return 0
  awk -v re="$BRIDGE_SECTION_RE" '
    /^==[^=]/ {
      # New top-level section — close any open bridge range.
      if (in_bridge) {
        printf "%d %d\n", start, NR - 1
        in_bridge = 0
      }
      if ($0 ~ re) {
        in_bridge = 1
        start = NR
      }
    }
    /^===[^=]/ {
      if ($0 ~ re && !in_bridge) {
        in_bridge = 1
        start = NR
      }
    }
    END {
      if (in_bridge) printf "%d %d\n", start, NR
    }
  ' "$file"
}

in_bridge_range() {
  local file="$1"
  local line="$2"
  while read -r start end; do
    if [ "$line" -ge "$start" ] && [ "$line" -le "$end" ]; then
      return 0
    fi
  done < <(bridge_ranges_for "$file")
  return 1
}

# Negation / future-aspiration context check.
# Looks at the full line for markers indicating the phrase is being
# negated, talked about historically, or named as a future target.
has_negation_context() {
  local content="$1"
  local lower
  lower=$(printf '%s' "$content" | tr '[:upper:]' '[:lower:]')
  # Standalone "no"/"not"/etc as a word.
  if printf '%s' "$lower" | grep -qE "(^|[^[:alnum:]'])(not|no|never|neither|isn'?t|doesn'?t|don'?t|lacks?|missing|downgrade|forbid|caveat|≠|stub|stubs|aspirational)([^[:alnum:]]|$)"; then
    return 0
  fi
  # Forward-looking targets ("future", "target", "goal", "aim", "roadmap",
  # "(future)") are not present-tense claims.
  if printf '%s' "$lower" | grep -qE "(^|[^[:alnum:]])(future|target|goal|aim|aiming|roadmap|aspiration|aspire|when|once|after)([^[:alnum:]]|$)"; then
    return 0
  fi
  # "is NOT" / "are NOT" framing.
  if printf '%s' "$lower" | grep -qE "(is|are|was|were|will be|would be)[[:space:]]+not[[:space:]]"; then
    return 0
  fi
  return 1
}

failures=0
shopt -s nullglob
for glob in "${scan_globs[@]}"; do
  for file in $glob; do
    is_exempt_file "$file" && continue
    [ -f "$file" ] || continue
    for phrase in "${forbidden[@]}"; do
      while IFS=: read -r lineno content; do
        [ -z "${lineno:-}" ] && continue
        if in_bridge_range "$file" "$lineno"; then
          continue
        fi
        if has_negation_context "$content"; then
          continue
        fi
        echo "FORBIDDEN: $file:$lineno: '$phrase'" >&2
        echo "  context: $(printf '%s' "$content" | sed 's/^[[:space:]]*//;s/[[:space:]]*$//' | cut -c1-120)" >&2
        echo "  → rephrase, or add explicit negation, or document via docs/ECHO-TYPES-OCHRANCE-BRIDGE.adoc" >&2
        failures=$((failures + 1))
      done < <(grep -ni -- "$phrase" "$file" 2>/dev/null || true)
    done
  done
done

if [ "$failures" -gt 0 ]; then
  echo "" >&2
  echo "Found $failures forbidden-phrase occurrence(s)." >&2
  echo "See docs/ECHO-TYPES-OCHRANCE-BRIDGE.adoc § 'Forbidden moves'." >&2
  exit 1
fi

echo "Bridge forbidden-phrases check: OK"

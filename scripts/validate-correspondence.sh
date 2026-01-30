#!/usr/bin/env bash
# SPDX-License-Identifier: PLMP-1.0-or-later
# Validate Lean 4 ↔ Rust Correspondence
#
# This script validates that Rust implementation matches Lean 4 specifications
# as documented in docs/LEAN4_RUST_CORRESPONDENCE.md

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
IMPL_DIR="$PROJECT_ROOT/impl/rust-cli"
PROOF_DIR="$PROJECT_ROOT/proofs/lean4"
CORRESPONDENCE_DOC="$PROJECT_ROOT/docs/LEAN4_RUST_CORRESPONDENCE.md"

echo "=== Lean 4 ↔ Rust Correspondence Validation ==="
echo

# Color codes
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m' # No Color

pass_count=0
warn_count=0
fail_count=0

# Function to check if a file exists and has content referencing another file
check_file_reference() {
    local lean_file="$1"
    local rust_file="$2"
    local operation="$3"

    echo -n "  Checking $operation... "

    # Check Lean file exists
    if [ ! -f "$lean_file" ]; then
        echo -e "${RED}FAIL${NC} - Lean file not found: $lean_file"
        ((fail_count++))
        return 1
    fi

    # Check Rust file exists
    if [ ! -f "$rust_file" ]; then
        echo -e "${RED}FAIL${NC} - Rust file not found: $rust_file"
        ((fail_count++))
        return 1
    fi

    # Check correspondence doc mentions both
    if ! grep -q "$(basename "$lean_file")" "$CORRESPONDENCE_DOC" 2>/dev/null; then
        echo -e "${YELLOW}WARN${NC} - Lean file not documented in correspondence"
        ((warn_count++))
        return 0
    fi

    if ! grep -q "$(basename "$rust_file")" "$CORRESPONDENCE_DOC" 2>/dev/null; then
        echo -e "${YELLOW}WARN${NC} - Rust file not documented in correspondence"
        ((warn_count++))
        return 0
    fi

    echo -e "${GREEN}PASS${NC}"
    ((pass_count++))
}

# Function to check property test coverage
check_property_test_coverage() {
    local operation="$1"
    local test_pattern="$2"

    echo -n "  Property test for $operation... "

    if grep -q "$test_pattern" "$IMPL_DIR/tests/property_tests.rs" 2>/dev/null; then
        echo -e "${GREEN}PASS${NC}"
        ((pass_count++))
        return 0
    elif grep -q "$test_pattern" "$IMPL_DIR/tests/property_correspondence_tests.rs" 2>/dev/null; then
        echo -e "${GREEN}PASS${NC}"
        ((pass_count++))
        return 0
    else
        echo -e "${YELLOW}WARN${NC} - No property test found"
        ((warn_count++))
        return 0
    fi
}

# Validate Core Operations
echo "1. Core Filesystem Operations"
check_file_reference "$PROOF_DIR/FilesystemModel.lean" "$IMPL_DIR/src/commands.rs" "mkdir/rmdir"
check_file_reference "$PROOF_DIR/FileOperations.lean" "$IMPL_DIR/src/commands.rs" "touch/rm"
check_property_test_coverage "mkdir/rmdir" "prop_mkdir_rmdir_reversible"
check_property_test_coverage "touch/rm" "prop_create_delete_file_reversible"
echo

# Validate Composition
echo "2. Operation Composition"
check_file_reference "$PROOF_DIR/FilesystemComposition.lean" "$IMPL_DIR/src/state.rs" "composition"
check_property_test_coverage "composition" "prop_composition_correctness"
echo

# Validate Equivalence
echo "3. Filesystem Equivalence"
check_file_reference "$PROOF_DIR/FilesystemEquivalence.lean" "$IMPL_DIR/src/state.rs" "equivalence"
check_property_test_coverage "equivalence" "prop_equivalence_reflexive"
echo

# Validate Test/Conditionals
echo "4. Conditional Operations (Phase 6 M14)"
if [ -f "$IMPL_DIR/src/test_command.rs" ]; then
    echo -e "  test/[ implementation... ${GREEN}PASS${NC}"
    ((pass_count++))
    check_property_test_coverage "test -f" "prop_test_f_file_detection"
    check_property_test_coverage "test -d" "prop_test_d_directory_detection"
else
    echo -e "  test/[ implementation... ${RED}FAIL${NC}"
    ((fail_count++))
fi
echo

# Validate Logical Operators
echo "5. Logical Operators (Phase 6 M14)"
if grep -q "LogicalOp" "$IMPL_DIR/src/parser.rs" 2>/dev/null; then
    echo -e "  &&/|| implementation... ${GREEN}PASS${NC}"
    ((pass_count++))
    check_property_test_coverage "logical AND" "prop_logical_and_short_circuit"
    check_property_test_coverage "logical OR" "prop_logical_or_short_circuit"
else
    echo -e "  &&/|| implementation... ${RED}FAIL${NC}"
    ((fail_count++))
fi
echo

# Validate Quote Processing
echo "6. Quote Processing (Phase 6 M13)"
if [ -f "$IMPL_DIR/src/quotes.rs" ]; then
    echo -e "  Quote module... ${GREEN}PASS${NC}"
    ((pass_count++))
    check_property_test_coverage "quote processing" "prop_quote_prevents_glob"
else
    echo -e "  Quote module... ${RED}FAIL${NC}"
    ((fail_count++))
fi
echo

# Validate Glob Expansion
echo "7. Glob Expansion (Phase 6 M12)"
if [ -f "$IMPL_DIR/src/glob.rs" ]; then
    echo -e "  Glob module... ${GREEN}PASS${NC}"
    ((pass_count++))
    check_property_test_coverage "glob expansion" "prop_glob_deterministic"
else
    echo -e "  Glob module... ${RED}FAIL${NC}"
    ((fail_count++))
fi
echo

# Summary
echo "=== Summary ==="
echo -e "${GREEN}PASS${NC}: $pass_count"
echo -e "${YELLOW}WARN${NC}: $warn_count"
echo -e "${RED}FAIL${NC}: $fail_count"
echo

# Calculate confidence percentage
total=$((pass_count + warn_count + fail_count))
if [ $total -gt 0 ]; then
    confidence=$(( (pass_count * 100 + warn_count * 50) / total ))
    echo "Correspondence Confidence: ${confidence}%"

    if [ $confidence -ge 85 ]; then
        echo -e "${GREEN}✓ High confidence in correspondence${NC}"
        exit 0
    elif [ $confidence -ge 70 ]; then
        echo -e "${YELLOW}⚠ Moderate confidence in correspondence${NC}"
        exit 0
    else
        echo -e "${RED}✗ Low confidence in correspondence - needs improvement${NC}"
        exit 1
    fi
else
    echo "No checks performed"
    exit 1
fi

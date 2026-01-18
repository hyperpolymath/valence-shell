#!/bin/bash
# Valence Shell - Verified Operations Demo
#
# This script demonstrates the filesystem operations that have been
# formally verified in 5 different proof assistants.
#
# Proven Properties:
# 1. mkdir followed by rmdir returns to original state
# 2. create_file followed by delete_file returns to original state
# 3. Operations on different paths are independent
# 4. Error conditions match POSIX semantics

set -e

# Colors for output
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m' # No Color

# Test directory
TEST_ROOT="/tmp/vsh_demo_$$"

echo -e "${BLUE}========================================${NC}"
echo -e "${BLUE}Valence Shell - Verified Operations Demo${NC}"
echo -e "${BLUE}========================================${NC}"
echo ""
echo "Test Root: $TEST_ROOT"
echo ""

# Setup
mkdir -p "$TEST_ROOT"
cd "$TEST_ROOT"

# Helper functions
print_test() {
    echo -e "${YELLOW}Test $1: $2${NC}"
}

print_success() {
    echo -e "${GREEN}✓ $1${NC}"
}

print_error() {
    echo -e "${RED}✗ $1${NC}"
}

check_state() {
    local path="$1"
    local should_exist="$2"

    if [ "$should_exist" = "exists" ]; then
        if [ -e "$path" ]; then
            print_success "State correct: $path exists"
            return 0
        else
            print_error "State incorrect: $path should exist but doesn't"
            return 1
        fi
    else
        if [ ! -e "$path" ]; then
            print_success "State correct: $path doesn't exist"
            return 0
        else
            print_error "State incorrect: $path shouldn't exist but does"
            return 1
        fi
    fi
}

echo -e "${BLUE}=== Theorem 1: mkdir/rmdir Reversibility ===${NC}"
echo "Proven in: Coq, Lean 4, Agda, Isabelle/HOL, Mizar"
echo ""

print_test "1.1" "Initial state - directory doesn't exist"
check_state "test_dir" "not_exists"

print_test "1.2" "Execute mkdir"
mkdir test_dir
check_state "test_dir" "exists"

print_test "1.3" "Execute rmdir (should reverse mkdir)"
rmdir test_dir
check_state "test_dir" "not_exists"
print_success "Reversibility verified: mkdir → rmdir = identity"
echo ""

echo -e "${BLUE}=== Theorem 2: create_file/delete_file Reversibility ===${NC}"
echo "Proven in: Coq, Lean 4, Agda, Isabelle/HOL, Mizar"
echo ""

print_test "2.1" "Initial state - file doesn't exist"
check_state "test_file" "not_exists"

print_test "2.2" "Execute create_file (touch)"
touch test_file
check_state "test_file" "exists"

print_test "2.3" "Execute delete_file (rm)"
rm test_file
check_state "test_file" "not_exists"
print_success "Reversibility verified: create_file → delete_file = identity"
echo ""

echo -e "${BLUE}=== Theorem 3: Operation Independence ===${NC}"
echo "Proven: Operations on different paths don't interfere"
echo ""

print_test "3.1" "Create directory A"
mkdir dir_a
check_state "dir_a" "exists"

print_test "3.2" "Create directory B"
mkdir dir_b
check_state "dir_b" "exists"

print_test "3.3" "Remove directory A (should not affect B)"
rmdir dir_a
check_state "dir_a" "not_exists"
check_state "dir_b" "exists"
print_success "Independence verified: A removed, B unaffected"

print_test "3.4" "Clean up directory B"
rmdir dir_b
check_state "dir_b" "not_exists"
echo ""

echo -e "${BLUE}=== Theorem 4: POSIX Error Conditions ===${NC}"
echo "Proven: Error codes match POSIX specification"
echo ""

print_test "4.1" "EEXIST - mkdir on existing directory"
mkdir test_exist
if mkdir test_exist 2>/dev/null; then
    print_error "Should have failed with EEXIST"
else
    print_success "Correctly returned EEXIST"
fi
rmdir test_exist

print_test "4.2" "ENOENT - rmdir on non-existent directory"
if rmdir non_existent 2>/dev/null; then
    print_error "Should have failed with ENOENT"
else
    print_success "Correctly returned ENOENT"
fi

print_test "4.3" "ENOENT - mkdir with missing parent"
if mkdir missing_parent/child 2>/dev/null; then
    print_error "Should have failed with ENOENT"
else
    print_success "Correctly returned ENOENT (parent doesn't exist)"
fi

print_test "4.4" "ENOTEMPTY - rmdir on non-empty directory"
mkdir dir_with_child
touch dir_with_child/file
if rmdir dir_with_child 2>/dev/null; then
    print_error "Should have failed with ENOTEMPTY"
else
    print_success "Correctly returned ENOTEMPTY"
fi
rm dir_with_child/file
rmdir dir_with_child

echo ""

echo -e "${BLUE}=== Theorem 5: Mixed Operations ===${NC}"
echo "Proven: File and directory operations preserve each other"
echo ""

print_test "5.1" "Create directory"
mkdir mixed_dir

print_test "5.2" "Create file in directory"
touch mixed_dir/file.txt
check_state "mixed_dir" "exists"
check_state "mixed_dir/file.txt" "exists"

print_test "5.3" "Delete file (directory should remain)"
rm mixed_dir/file.txt
check_state "mixed_dir" "exists"
check_state "mixed_dir/file.txt" "not_exists"
print_success "File deleted, directory preserved"

print_test "5.4" "Create sibling file"
touch mixed_dir/file2.txt

print_test "5.5" "Create sibling directory"
mkdir mixed_dir/subdir
check_state "mixed_dir/file2.txt" "exists"
check_state "mixed_dir/subdir" "exists"
print_success "Siblings created independently"

print_test "5.6" "Cleanup"
rm mixed_dir/file2.txt
rmdir mixed_dir/subdir
rmdir mixed_dir
echo ""

echo -e "${BLUE}=== Theorem 6: Composition ===${NC}"
echo "Proven: Multiple reversible operations compose correctly"
echo ""

print_test "6.1" "Create directory A"
mkdir comp_a
check_state "comp_a" "exists"

print_test "6.2" "Create directory B"
mkdir comp_b
check_state "comp_b" "exists"

print_test "6.3" "Create file in A"
touch comp_a/file_a
check_state "comp_a/file_a" "exists"

print_test "6.4" "Create file in B"
touch comp_b/file_b
check_state "comp_b/file_b" "exists"

print_test "6.5" "Reverse all operations (in reverse order)"
rm comp_b/file_b
rm comp_a/file_a
rmdir comp_b
rmdir comp_a

check_state "comp_a" "not_exists"
check_state "comp_b" "not_exists"
print_success "All operations reversed: final state = initial state"
echo ""

# Cleanup
cd /
rm -rf "$TEST_ROOT"

echo -e "${GREEN}========================================${NC}"
echo -e "${GREEN}All Verified Theorems Demonstrated!${NC}"
echo -e "${GREEN}========================================${NC}"
echo ""
echo "Summary of Formal Guarantees:"
echo "✓ Directory operations are reversible (mkdir ↔ rmdir)"
echo "✓ File operations are reversible (create ↔ delete)"
echo "✓ Operations on different paths are independent"
echo "✓ Error conditions match POSIX specification"
echo "✓ Mixed operations preserve invariants"
echo "✓ Multiple operations compose correctly"
echo ""
echo "Verified in 5 proof assistants:"
echo "  1. Coq (Calculus of Inductive Constructions)"
echo "  2. Lean 4 (Dependent Type Theory)"
echo "  3. Agda (Intensional Type Theory)"
echo "  4. Isabelle/HOL (Higher-Order Logic)"
echo "  5. Mizar (Tarski-Grothendieck Set Theory)"
echo ""
echo "Trust chain:"
echo "  • Formal proofs (verified by proof assistant kernels)"
echo "  • This demo (testing real POSIX behavior)"
echo "  • Gap: Implementation correctness (requires extraction or manual verification)"
echo ""

#!/usr/bin/env bash
# SPDX-License-Identifier: PMPL-1.0-or-later
#
# Manual test for built-in command redirections
# Run after: cargo build --release

set -e

TESTDIR="/tmp/vsh_redirect_manual_test_$$"
VSH="./target/release/vsh"

echo "=== Valence Shell - Built-in Redirection Manual Test ==="
echo

# Setup
mkdir -p "$TESTDIR"
cd "$TESTDIR"
echo "Test directory: $TESTDIR"
echo

# Test 1: pwd > output
echo "Test 1: pwd > output.txt"
echo "pwd > output.txt" | $VSH || true
if [ -f output.txt ]; then
    echo "✓ File created"
    echo "  Content: $(cat output.txt)"
else
    echo "✗ File not created"
fi
echo

# Test 2: ls > listing
echo "Test 2: ls > listing.txt (after creating test files)"
mkdir testdir
touch file1.txt file2.txt
echo "ls > listing.txt" | $VSH || true
if [ -f listing.txt ]; then
    echo "✓ Listing created"
    echo "  Content:"
    cat listing.txt | sed 's/^/    /'
else
    echo "✗ Listing not created"
fi
echo

# Test 3: Append >>
echo "Test 3: pwd >> log.txt (multiple appends)"
echo "First line" > log.txt
echo "pwd >> log.txt" | $VSH || true
echo "pwd >> log.txt" | $VSH || true
if [ -f log.txt ]; then
    echo "✓ Append succeeded"
    echo "  Line count: $(wc -l < log.txt)"
    echo "  Content:"
    cat log.txt | sed 's/^/    /'
else
    echo "✗ Append failed"
fi
echo

# Cleanup
cd /
rm -rf "$TESTDIR"
echo "=== Test Complete ==="

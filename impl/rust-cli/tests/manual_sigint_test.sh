#!/bin/bash
# SPDX-License-Identifier: PLMP-1.0-or-later
# Manual test for SIGINT (Ctrl+C) handling
#
# Expected behavior:
# 1. Shell starts
# 2. sleep 5 command runs
# 3. Ctrl+C interrupts sleep (not shell)
# 4. Shell remains responsive
# 5. No zombie processes

set -e

echo "=== SIGINT Handling Manual Test ==="
echo
echo "This test will:"
echo "1. Start vsh in interactive mode"
echo "2. Run 'sleep 10' command"
echo "3. Send SIGINT (Ctrl+C) after 2 seconds"
echo "4. Verify shell is still alive"
echo "5. Check for zombie processes"
echo
echo "Starting test in 3 seconds..."
sleep 3

# Build release binary
echo "Building vsh..."
cargo build --release --quiet

# Create test script
TEST_SCRIPT=$(mktemp)
cat > "$TEST_SCRIPT" <<'EOF'
sleep 10
echo "Shell is still alive after interrupt"
exit
EOF

# Run vsh with test script, send SIGINT after 2 seconds
echo
echo "Running vsh with 'sleep 10' command..."
echo "Will send Ctrl+C after 2 seconds..."
echo

(
    sleep 2
    pkill -INT -f "sleep 10" || true
    echo "  [Sent SIGINT]"
) &

timeout 15 ./target/release/vsh < "$TEST_SCRIPT" || true

# Check for zombie processes
echo
echo "Checking for zombie processes..."
ZOMBIES=$(ps aux | grep -E "defunct|Z" | grep -v grep || true)

if [ -n "$ZOMBIES" ]; then
    echo "❌ FAIL: Found zombie processes:"
    echo "$ZOMBIES"
    exit 1
else
    echo "✅ PASS: No zombie processes"
fi

# Cleanup
rm -f "$TEST_SCRIPT"

echo
echo "=== Test Complete ==="
echo "Manual verification:"
echo "1. Sleep command should have been interrupted"
echo "2. Shell should have printed 'Shell is still alive after interrupt'"
echo "3. No zombie processes found"

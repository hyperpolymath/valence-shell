#!/usr/bin/env bash
# Install Git hooks for Valence Shell
#
# Usage: ./scripts/install-hooks.sh
#
# This installs the pre-commit hook that:
# 1. Protects sacred files from accidental modification
# 2. Blocks Python/TypeScript contamination (RSR policy)

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(dirname "$SCRIPT_DIR")"
HOOKS_DIR="$REPO_ROOT/.git/hooks"
SOURCE_HOOK="$REPO_ROOT/hooks/pre-commit"

echo "Installing Valence Shell Git hooks..."
echo ""

# Check we're in a git repo
if [ ! -d "$REPO_ROOT/.git" ]; then
    echo "❌ Error: Not a git repository"
    exit 1
fi

# Check source hook exists
if [ ! -f "$SOURCE_HOOK" ]; then
    echo "❌ Error: hooks/pre-commit not found"
    exit 1
fi

# Create hooks directory if needed
mkdir -p "$HOOKS_DIR"

# Install pre-commit hook
cp "$SOURCE_HOOK" "$HOOKS_DIR/pre-commit"
chmod +x "$HOOKS_DIR/pre-commit"

echo "✅ Installed: pre-commit"
echo "   - Protects sacred files (README.adoc, STATE.adoc, META.scm, ARCHITECTURE.md)"
echo "   - Blocks Python/TypeScript contamination"
echo ""
echo "Hooks installed successfully!"
echo ""
echo "To uninstall: rm .git/hooks/pre-commit"

# Parameter Expansion

**Since:** v1.1.0
**Spec:** bash-compatible parameter expansion syntax

## Overview

Parameter expansion allows you to manipulate variables inline using the `${VAR...}` syntax. This provides powerful text manipulation capabilities without external tools.

## Syntax Summary

| Syntax | Description | Example |
|--------|-------------|---------|
| `${VAR}` | Simple expansion | `${HOME}` → `/home/user` |
| `${VAR:-default}` | Use default if unset/null | `${MISSING:-fallback}` → `fallback` |
| `${VAR-default}` | Use default if unset only | `${EMPTY-fallback}` → `` (empty) |
| `${VAR:=default}` | Assign default if unset/null | Returns default value* |
| `${VAR=default}` | Assign default if unset only | Returns default value* |
| `${VAR:+value}` | Use value if set/non-null | `${VAR:+yes}` → `yes` (if VAR set) |
| `${VAR+value}` | Use value if set | `${EMPTY+yes}` → `yes` |
| `${VAR:?message}` | Error if unset/null | Prints error, returns empty |
| `${VAR?message}` | Error if unset | Prints error, returns empty |
| `${#VAR}` | String length | `${#PATH}` → `42` |
| `${VAR:offset}` | Substring from offset | `${VAR:5}` → substring from index 5 |
| `${VAR:offset:length}` | Substring with length | `${VAR:5:3}` → 3 chars from index 5 |
| `${VAR: -offset}` | Substring from end | `${VAR: -5}` → last 5 characters |

*Note: Assignment (`:=`, `=`) deferred to v1.1.1 - currently returns value without persisting assignment*

## Detailed Examples

### Default Values

Use default values when variables might be unset:

```bash
# Use default if VAR is unset or empty
echo "${VAR:-default value}"  # → "default value" (if VAR unset/empty)

# Use default only if VAR is unset (not if empty)
VAR=""
echo "${VAR-default}"   # → "" (empty, because VAR is set)
echo "${VAR:-default}"  # → "default" (checks for null too)
```

**With colon (`:`)**: Checks for both unset AND null (empty)
**Without colon**: Only checks for unset

### Assign Default (v1.1.1)

```bash
# Returns default but doesn't persist (v1.1.0 limitation)
echo "${CONFIG:=/etc/default}"  # → "/etc/default"
# In v1.1.1, CONFIG will also be set to "/etc/default"
```

### Use Alternative Value

Return a value only if variable is set:

```bash
VERBOSE=1
echo "${VERBOSE:+--verbose}"  # → "--verbose" (because VERBOSE is set)

unset QUIET
echo "${QUIET:+--quiet}"  # → "" (empty, because QUIET is unset)
```

Useful for optional flags:

```bash
# Only add flag if DEBUG is set
command ${DEBUG:+--debug} input.txt
```

### Error if Unset

Enforce required variables:

```bash
echo "${REQUIRED:?Error: REQUIRED must be set}"
# If REQUIRED is unset: prints to stderr, returns empty
# vsh: REQUIRED: Error: REQUIRED must be set

# Default error message
echo "${REQUIRED:?}"
# vsh: REQUIRED: parameter null or not set
```

### String Length

Get character count (Unicode-aware):

```bash
VAR="hello world"
echo "${#VAR}"  # → "11"

# Unicode characters counted correctly
VAR="hello 世界"
echo "${#VAR}"  # → "8" (not byte count)

# Works with special variables
echo "${#PATH}"  # Length of PATH variable
echo "${#?}"     # Length of exit code string
```

### Substring Extraction

Extract portions of strings:

```bash
VAR="hello world"

# From offset (0-indexed)
echo "${VAR:6}"     # → "world" (from index 6 to end)
echo "${VAR:0:5}"   # → "hello" (5 chars from start)

# Negative offset (from end) - REQUIRES SPACE before minus
echo "${VAR: -5}"   # → "world" (last 5 chars)
echo "${VAR: -5:3}" # → "wor" (3 chars, 5 from end)

# Advanced
echo "${VAR:0:1}"   # → "h" (first character)
echo "${VAR: -1}"   # → "d" (last character)
```

**Important**: Negative offset requires space: `${VAR: -5}` not `${VAR:-5}` (which is default value)

### Nested Expansion

Expansions can be nested for complex logic:

```bash
# Multi-level fallback
echo "${PRIMARY:-${SECONDARY:-${FALLBACK}}}"

# Use alternative based on another variable
DEFAULT="production"
echo "${ENV:-${DEFAULT}}"  # → value of DEFAULT if ENV unset

# Three levels deep
echo "${A:-${B:-${C:-default}}}"
```

## Special Variables

Parameter expansion works with special variables:

```bash
# Exit code
echo "${#?}"  # Length of last exit code (e.g., "3" for "127")

# Positional parameters
echo "${1:0:3}"  # First 3 chars of first argument

# Process ID
echo "${#$}"  # Length of process ID string
```

## Bash Compatibility

### Fully Compatible

- ✅ `${VAR:-default}` - Default value (with/without null check)
- ✅ `${VAR:+value}` - Alternative value
- ✅ `${VAR:?message}` - Error if unset
- ✅ `${#VAR}` - String length (Unicode-aware)
- ✅ `${VAR:offset}` - Substring extraction
- ✅ `${VAR: -offset}` - Negative offset (space required)
- ✅ Nested expansions

### Partially Compatible

- ⚠️ `${VAR:=default}` - **Returns default but doesn't assign in v1.1.0**
  - Assignment deferred to v1.1.1 (requires mutable state in expand_variables)
  - Currently behaves like `${VAR:-default}` (returns default without assigning)

### Not Yet Implemented

- ❌ `${VAR#pattern}` - Remove shortest prefix pattern
- ❌ `${VAR##pattern}` - Remove longest prefix pattern
- ❌ `${VAR%pattern}` - Remove shortest suffix pattern
- ❌ `${VAR%%pattern}` - Remove longest suffix pattern
- ❌ `${VAR/pattern/replacement}` - Pattern substitution
- ❌ `${VAR^}` / `${VAR,}` - Case conversion
- ❌ Array expansions (`${arr[@]}`, `${!arr[@]}`, etc.) - Coming in v1.1.0

## Edge Cases

### Empty vs Unset

```bash
unset VAR      # VAR is unset
VAR=""         # VAR is set but empty (null)

echo "${VAR-default}"   # → "" (VAR is set, even if empty)
echo "${VAR:-default}"  # → "default" (VAR is null)
```

### Quote Interaction

```bash
# Expansion happens inside double quotes
echo "${VAR:-default value}"  # Spaces preserved

# Variable in default value gets expanded
echo "${A:-$B}"  # $B is expanded if A is unset
```

### Very Long Strings

```bash
# Length and substring work with large strings
LARGE=$(cat huge_file.txt)
echo "${#LARGE}"       # Character count
echo "${LARGE:0:100}"  # First 100 chars
```

### Unicode Safety

All operations are Unicode-aware (character-based, not byte-based):

```bash
VAR="日本語"
echo "${#VAR}"      # → "3" (not 9 bytes)
echo "${VAR:1:1}"   # → "本" (second character)
```

## Common Patterns

### Configuration with Defaults

```bash
# Use environment variable or default
PORT="${PORT:-8080}"
HOST="${HOST:-localhost}"
DEBUG="${DEBUG:-false}"
```

### Optional Flags

```bash
# Only add flags if variables are set
curl ${VERBOSE:+-v} ${TIMEOUT:+--max-time $TIMEOUT} "$URL"
```

### Required Variables

```bash
# Ensure critical variables are set
: "${API_KEY:?Error: API_KEY must be set}"
: "${DATABASE_URL:?Error: DATABASE_URL required}"
```

### String Manipulation

```bash
# Extract filename extension
FILENAME="document.pdf"
echo "${FILENAME: -3}"  # → "pdf"

# Get first N characters
echo "${FILENAME:0:8}"  # → "document"

# Check string length
if [ "${#PASSWORD}" -lt 8 ]; then
    echo "Password too short"
fi
```

## Performance Notes

- Expansion is O(n) where n is the string length
- Nested expansions are evaluated recursively
- Unicode character counting may be slower than byte counting for very large strings
- Length operation: O(n) to count characters
- Substring operation: O(n) to extract characters

## Testing

Run parameter expansion tests:

```bash
cargo test --test parameter_expansion_tests
```

Current test coverage: 67+ tests covering all operators, edge cases, Unicode, and special variables.

## See Also

- [Bash Reference Manual - Shell Parameter Expansion](https://www.gnu.org/software/bash/manual/html_node/Shell-Parameter-Expansion.html)
- [POSIX Parameter Expansion](https://pubs.opengroup.org/onlinepubs/9699919799/utilities/V3_chap02.html#tag_18_06_02)
- STATE.scm - v1.1.0 roadmap
- CHANGELOG.md - Version history

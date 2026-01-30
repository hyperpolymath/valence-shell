# Valence Shell: User Guide

**Version**: 0.14.0
**Last Updated**: 2026-01-30

---

## What is Valence Shell?

Valence Shell (vsh) is a **formally verified shell** with mathematical guarantees about correctness. Think of it as:
- **bash** (familiar shell features)
- **+** **undo/redo** (like a text editor)
- **+** **formal proofs** (mathematically verified correctness)

### Why would I use this?

**Security-critical environments**: Finance, healthcare, government
- Every operation is logged and auditable
- Mistakes can be undone without data loss
- GDPR-compliant secure deletion (coming in v1.0)

**Learning**: Understand how formally verified software works
- See how proofs relate to code
- Property-based testing examples
- Study verified systems design

---

## Installation

### From Release (Recommended)

```bash
# Linux x86_64
curl -L https://github.com/hyperpolymath/valence-shell/releases/latest/download/vsh-linux-x64 -o vsh
chmod +x vsh
sudo mv vsh /usr/local/bin/

# macOS x86_64
curl -L https://github.com/hyperpolymath/valence-shell/releases/latest/download/vsh-macos-x64 -o vsh
chmod +x vsh
sudo mv vsh /usr/local/bin/

# Windows x64
# Download vsh-windows-x64.exe from releases page
```

### From Source

```bash
# Prerequisites: Rust 1.70.0+
git clone https://github.com/hyperpolymath/valence-shell
cd valence-shell/impl/rust-cli
cargo build --release
sudo cp target/release/vsh /usr/local/bin/
```

---

## Quick Start

### Launch the shell

```bash
$ vsh
vsh>
```

### Basic commands

```bash
# Create directory
vsh> mkdir projects
✓ Created directory: projects

# Create file
vsh> touch projects/readme.txt
✓ Created file: projects/readme.txt

# List files
vsh> ls projects
readme.txt

# Undo last operation
vsh> undo
⟲ Undoing: touch projects/readme.txt
✓ Removed file: projects/readme.txt

# Redo
vsh> redo
⟳ Redoing: touch projects/readme.txt
✓ Created file: projects/readme.txt
```

### External commands

```bash
# Run any Unix command
vsh> echo "Hello, world!"
Hello, world!

# Pipelines
vsh> ls -la | grep .txt | wc -l
5

# Redirections
vsh> ls > files.txt
vsh> cat < input.txt > output.txt 2> errors.log
```

---

## Core Features

### 1. Reversible Operations

Every filesystem operation can be undone:

```bash
vsh> mkdir temp
vsh> touch temp/file.txt
vsh> echo "content" > temp/file.txt

vsh> history
1. mkdir temp
2. touch temp/file.txt
3. write temp/file.txt

vsh> undo
⟲ Undoing: write temp/file.txt
✓ Restored file: temp/file.txt

vsh> undo
⟲ Undoing: touch temp/file.txt
✓ Removed file: temp/file.txt

vsh> undo
⟲ Undoing: mkdir temp
✓ Removed directory: temp
```

**What's reversible**:
- ✅ mkdir / rmdir
- ✅ touch / rm
- ✅ File writes (> and >>)
- ✅ Truncate / append operations
- ✅ Operation sequences

**What's NOT reversible** (by design):
- 🚫 Secure deletion (GDPR compliance)
- 🚫 Hardware erase

### 2. Transaction Grouping

Group operations to undo/redo together:

```bash
vsh> begin-transaction "Setup project"
vsh> mkdir src tests docs
vsh> touch src/main.rs tests/test.rs docs/README.md
vsh> end-transaction

vsh> undo
⟲ Undoing transaction: Setup project
✓ Removed 3 files, 3 directories
```

### 3. Conditionals and Logical Operators

POSIX-compliant test operators:

```bash
# File tests
vsh> if test -f README.md; then echo "File exists"; fi
File exists

# Bracket syntax
vsh> [ -d /tmp ] && echo "Directory exists"
Directory exists

# String tests
vsh> [ "abc" = "abc" ] && echo "Equal"
Equal

# Integer comparisons
vsh> [ 5 -gt 3 ] && echo "Greater"
Greater

# Logical operators
vsh> [ -f file.txt ] && echo "Found" || echo "Not found"
Not found

# Chained conditions
vsh> [ -f input.txt ] && [ -r input.txt ] && cat input.txt
```

**Supported test operators**:

| File Tests | Description |
|------------|-------------|
| `-f PATH` | Is regular file |
| `-d PATH` | Is directory |
| `-e PATH` | Exists |
| `-r PATH` | Is readable |
| `-w PATH` | Is writable |
| `-x PATH` | Is executable |
| `-s PATH` | Is non-empty |

| String Tests | Description |
|--------------|-------------|
| `-z STR` | Is empty |
| `-n STR` | Is non-empty |
| `STR1 = STR2` | Equal |
| `STR1 != STR2` | Not equal |

| Integer Tests | Description |
|---------------|-------------|
| `N1 -eq N2` | Equal |
| `N1 -ne N2` | Not equal |
| `N1 -lt N2` | Less than |
| `N1 -le N2` | Less or equal |
| `N1 -gt N2` | Greater than |
| `N1 -ge N2` | Greater or equal |

### 4. Glob Expansion

Standard glob patterns:

```bash
# Wildcards
vsh> ls *.txt          # All .txt files
vsh> ls file?.rs       # file1.rs, file2.rs
vsh> ls [abc]*         # Files starting with a, b, or c
vsh> ls {1,2,3}.txt    # 1.txt, 2.txt, 3.txt

# Recursive
vsh> ls **/*.rs        # All .rs files in subdirectories
```

### 5. Quote Processing

POSIX-compliant quoting:

```bash
# Single quotes: literal
vsh> echo 'Stars: *.txt'
Stars: *.txt

# Double quotes: expansion, no glob
vsh> echo "Stars: *.txt"
Stars: *.txt

# Unquoted: both expansion and glob
vsh> echo *.txt
file1.txt file2.txt
```

### 6. Job Control

Background jobs and management:

```bash
# Run in background
vsh> sleep 10 &
[1] 12345

# List jobs
vsh> jobs
[1]  Running  sleep 10

# Bring to foreground
vsh> fg %1

# Send to background
vsh> bg %1

# Kill job
vsh> kill %1
```

---

## Advanced Features

### Pipelines

```bash
# Simple pipeline
vsh> cat file.txt | grep "error" | wc -l

# Multi-stage pipeline
vsh> find . -name "*.rs" | xargs grep "TODO" | sort | uniq
```

**Pipeline undo**: Final redirections are reversible

```bash
vsh> ls | grep .txt > results.txt
vsh> undo
⟲ Undoing: write results.txt
✓ Restored file: results.txt
```

### Redirections

```bash
# Output redirection
vsh> echo "hello" > file.txt      # Truncate and write
vsh> echo "world" >> file.txt     # Append

# Input redirection
vsh> cat < input.txt

# Error redirection
vsh> cmd 2> errors.log            # Stderr to file
vsh> cmd 2>&1                     # Stderr to stdout
vsh> cmd &> all.log               # Both stdout and stderr

# Undo redirections
vsh> echo "new" > important.txt
vsh> undo
⟲ Undoing: write important.txt
✓ Restored original content
```

### Process Substitution

```bash
# Input process substitution
vsh> diff <(ls dir1) <(ls dir2)

# Output process substitution
vsh> tee >(gzip > backup.gz) < input.txt > output.txt
```

### Arithmetic Expansion

```bash
vsh> echo $((2 + 3))
5

vsh> echo $((10 * 5 / 2))
25

# Operators: +, -, *, /, %, **
vsh> echo $((2 ** 10))
1024
```

### Here Documents

```bash
vsh> cat <<EOF
Line 1
Line 2
EOF
Line 1
Line 2

# With tab stripping
vsh> cat <<-EOF
	Indented line
	EOF
Indented line
```

---

## Configuration

### Shell Options

Create `~/.vshrc`:

```bash
# History settings
set history-size 10000
set history-archive ~/.vsh/history

# Undo settings
set max-undo-depth 1000

# Verification mode (v2.0+)
set verification-level validated  # tested|validated|proven|extracted

# Prompt
set prompt "vsh \W > "
```

### Aliases

```bash
# In ~/.vshrc
alias ll='ls -la'
alias gs='git status'
```

---

## Verification Levels

Valence Shell shows verification confidence for each operation:

```bash
vsh> help

Operations:
  mkdir      Create directory            [PROVEN]    ✓✓
  rmdir      Remove directory            [PROVEN]    ✓✓
  touch      Create file                 [PROVEN]    ✓✓
  test/[     Conditional testing         [VALIDATED] ✓

Legend:
  [EXTRACTED] - 99%+ confidence (v2.0+, extracted from verified code)
  [PROVEN]    - 95% confidence (proven in Lean 4)
  [VALIDATED] - 90% confidence (property tests + correspondence)
  [TESTED]    - 85% confidence (unit + integration tests)
```

---

## Comparison to Other Shells

| Feature | vsh | bash | zsh | fish |
|---------|-----|------|-----|------|
| **Undo/Redo** | ✅ | ❌ | ❌ | ❌ |
| **Formal Verification** | ✅ | ❌ | ❌ | ❌ |
| **Audit Logging** | ✅ | ⚠️ (manual) | ⚠️ (manual) | ⚠️ (manual) |
| **GDPR Compliance** | ✅ (v1.0) | ❌ | ❌ | ❌ |
| **Pipelines** | ✅ | ✅ | ✅ | ✅ |
| **Job Control** | ✅ | ✅ | ✅ | ✅ |
| **Plugins** | ❌ | ✅ | ✅✅ | ✅ |
| **Syntax Highlighting** | ⏳ | via plugin | ✅ | ✅ |

**When to use vsh**:
- ✅ Security-critical environments
- ✅ Compliance requirements (GDPR, SOC2, HIPAA)
- ✅ Operations requiring audit trails
- ✅ Learning formal verification

**When to use bash/zsh**:
- ✅ General-purpose shell scripting
- ✅ Maximum compatibility
- ✅ Rich plugin ecosystem

---

## Getting Help

```bash
# Built-in help
vsh> help

# Command-specific help
vsh> help mkdir

# Show verification status
vsh> verify-status

# Show operation history
vsh> history

# Check correspondence
vsh> verify-correspondence  # Developers only
```

---

## Troubleshooting

### Undo doesn't work

**Problem**: Undo says "Nothing to undo"

**Solution**: Some operations aren't tracked in history:
- Read-only operations (ls, cat, echo)
- External commands (unless they modify files)
- Aliased commands

### Performance is slow

**Problem**: Shell feels sluggish

**Solution**: Disable runtime verification:
```bash
vsh --no-verify  # Start without runtime checks
# OR in ~/.vshrc:
set verification-level tested
```

### Permission denied errors

**Problem**: Can't undo operations outside sandbox

**Solution**: vsh operates in a sandbox for safety. To disable:
```bash
vsh --no-sandbox  # WARNING: Disables safety guarantees
```

---

## Reporting Bugs

Found a bug? Check if it's a proof violation:

```bash
vsh> verify-correspondence
Checking correspondence between proofs and implementation...
✓ All operations match formal specifications

# If verification fails:
⚠ WARNING: Implementation diverges from proof!
  Operation: mkdir
  Expected: creates directory
  Actual: creates file (BUG!)

Please report at: https://github.com/hyperpolymath/valence-shell/issues
```

---

## What's Next?

- **v1.0** (Q2 2026): GDPR compliance, audit logging, history limits
- **v2.0** (Q4 2026): Idris2-extracted core (99%+ verification confidence)
- **v3.0** (2027): Plugin system, advanced scripting

---

## Learn More

- **Architecture**: See docs/ARCHITECTURE.md
- **Proofs**: See docs/PROOF_OVERVIEW.md
- **Contributing**: See docs/CONTRIBUTOR_GUIDE_TIER1.md
- **Verification**: See docs/VERIFICATION_GUIDE.md

---

**Valence Shell**: Because your filesystem operations should be correct. Provably.

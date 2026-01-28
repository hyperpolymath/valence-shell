# Getting Started with Valence Shell

**Version**: 0.7.2 (candidate)
**Status**: Research prototype with formally verified operations

---

## What is Valence Shell?

Valence Shell (vsh) is a POSIX-like shell where **every filesystem operation is mathematically proven reversible**. Each command has a corresponding Lean 4 theorem guaranteeing correctness.

### Key Features

- **Reversible Operations**: Undo/redo any filesystem change
- **Transactional Execution**: Group operations and rollback atomically
- **I/O Redirections**: Standard shell redirections (>, >>, <, 2>, etc.)
- **Formal Verification**: 256+ theorems across 6 proof systems
- **Proof-Backed**: Every operation references its correctness theorem

---

## Installation

### Prerequisites

- **Rust 1.70+** - Install via [rustup](https://rustup.rs/)
- **Linux or macOS** - Windows WSL2 also supported
- **Git** - For cloning the repository

### Build from Source

```bash
# Clone repository
git clone https://github.com/hyperpolymath/valence-shell.git
cd valence-shell/impl/rust-cli

# Build release binary
cargo build --release

# Run the shell
./target/release/vsh
```

### Development Build

```bash
# Build with debug symbols
cargo build

# Run tests
cargo test

# Run with verbose output
cargo run -- --verbose
```

---

## Quick Start

### Interactive Mode

Start the shell:

```bash
$ vsh
vsh>
```

### Basic Operations

Create directories and files:

```bash
vsh> mkdir project
[op:a3b2c1d0] mkdir project

vsh> touch project/README.md
[op:b4c5d6e7] touch project/README.md

vsh> touch project/main.rs
[op:c5d6e7f8] touch project/main.rs
```

Each operation gets a unique ID (`op:a3b2c1d0`) for tracking.

### List Files

```bash
vsh> ls
📁 project/
[op:d6e7f8g9] ls

vsh> ls project
📄 README.md
📄 main.rs
[op:e7f8g9h0] ls project
```

---

## Undo and Redo

### Undo Operations

Reverse the last operation:

```bash
vsh> mkdir temp
[op:12345678] mkdir temp

vsh> undo
[op:23456789] undo [op:12345678] rmdir temp
# Directory removed - like it never happened

vsh> ls
# temp/ is gone
```

Undo multiple operations:

```bash
vsh> undo 3
# Reverses last 3 operations
```

### Redo Operations

Re-apply undone operations:

```bash
vsh> redo
[op:34567890] redo temp
# Directory recreated

vsh> redo 2
# Re-applies next 2 undone operations
```

### View History

```bash
vsh> history
═══ Operation History ═══

[12345678] 14:23:15 mkdir project
[23456789] 14:23:20 touch project/README.md
[34567890] 14:23:25 touch project/main.rs

Total: 3 operations shown
```

With proof references:

```bash
vsh> history --proofs
═══ Operation History ═══

[12345678] 14:23:15 mkdir project
    Theorem: mkdir_rmdir_reversible (FilesystemModel.lean:158)

[23456789] 14:23:20 touch project/README.md
    Theorem: createFile_deleteFile_reversible (FileOperations.lean:42)
```

---

## I/O Redirections

### Output Redirection

```bash
vsh> ls > files.txt
[op:45678901] ls
# Output written to files.txt

vsh> cat files.txt
project/
README.md
```

### Append Redirection

```bash
vsh> echo "log entry" >> log.txt
[op:56789012] echo
# Appends to log.txt (creates if doesn't exist)
```

### Input Redirection

```bash
vsh> cat < input.txt
# Reads from input.txt
```

### Error Redirection

```bash
vsh> command-that-fails 2> errors.txt
# Stderr redirected to errors.txt

vsh> noisy-command &> all-output.txt
# Both stdout and stderr to all-output.txt
```

### Redirection Undo

Redirections are reversible:

```bash
vsh> echo "test" > newfile.txt
[op:67890123] echo
# Creates newfile.txt

vsh> undo
[op:78901234] undo [op:67890123] DeleteFile newfile.txt
# File deleted - creation undone

vsh> ls newfile.txt
# File not found
```

---

## Transactions

### Group Operations

```bash
vsh> begin project-setup
[txn:89012345] begin project-setup

vsh> mkdir src
[op:90123456] mkdir src

vsh> touch src/main.rs
[op:01234567] touch src/main.rs

vsh> ls > files.txt
[op:12345678] ls
```

### Commit Transaction

```bash
vsh> commit
Transaction committed: 3 operations
```

All operations are now permanent.

### Rollback Transaction

If something goes wrong:

```bash
vsh> begin cleanup
[txn:23456789] begin cleanup

vsh> rmdir old-dir
[op:34567890] rmdir old-dir

vsh> rm old-file.txt
[op:45678901] rm old-file.txt

vsh> rollback cleanup
Transaction rolled back: 2 operations
# Both operations reversed atomically
```

---

## Operation Graph

Visualize operation history as a DAG:

```bash
vsh> graph
═══ Operation DAG ═══

┌─────────────────────────────────────┐
│ [initial state]                     │
└───────────────┬─────────────────────┘
                │
                │ op:1 mkdir project
                ▼
┌─────────────────────────────────────┐
│ ○ state_1                           │
└───────────────┬─────────────────────┘
                │
                │ op:2 touch main.rs
                ▼
┌─────────────────────────────────────┐
│ ○ state_2 ◄── YOU ARE HERE         │
└─────────────────────────────────────┘

Undo path: rm main.rs → rmdir project → [initial]
```

---

## External Commands

Run any installed program:

```bash
vsh> echo "Hello, World!"
Hello, World!

vsh> date
Tue Jan 28 14:30:00 UTC 2026

vsh> grep "pattern" file.txt > matches.txt
# External commands support all redirections
```

### Exit Codes

Check last command's exit code:

```bash
vsh> true
vsh> echo $?
0

vsh> false
vsh> echo $?
1
```

Signal terminations:

```bash
vsh> sleep 10
^C  # Press Ctrl+C
# Returns exit code 130 (128 + SIGINT)
```

---

## Interrupt Handling

### Ctrl+C Behavior

Valence Shell handles interrupts gracefully:

```bash
vsh> sleep 30
# Press Ctrl+C
^C
vsh> # Shell is still alive, sleep command was killed
```

The shell:
- ✅ Kills the running external command
- ✅ Returns control to the prompt
- ✅ Cleans up zombie processes
- ✅ Returns exit code 130 (SIGINT)

---

## Configuration

### State Persistence

Shell state is saved to:
```
~/.cache/vsh/state.json
```

Contains:
- Operation history
- Undo/redo stacks
- Transactions
- Last exit code

### State File Format

```json
{
  "history": [
    {
      "id": "uuid",
      "op_type": "Mkdir",
      "path": "project",
      "timestamp": "2026-01-28T14:30:00Z",
      "undone": false
    }
  ],
  "redo_stack": [],
  "active_transaction": null,
  "transactions": []
}
```

---

## Tips and Best Practices

### 1. Use Transactions for Multi-Step Operations

```bash
vsh> begin feature
vsh> mkdir src/feature
vsh> touch src/feature/mod.rs
vsh> commit
# All or nothing - rollback if something fails
```

### 2. Check History Before Undo

```bash
vsh> history 5
# See last 5 operations before undoing
```

### 3. Redirections are Undoable

```bash
vsh> echo "data" > important.txt
vsh> undo
# File creation reversed - no orphaned files
```

### 4. External Commands are NOT Reversible

```bash
vsh> rm -rf project/
# vsh cannot undo external command side effects!
# Use built-in rm instead:
vsh> rm project/file.txt
[op:...] rm project/file.txt
vsh> undo  # This works
```

---

## Troubleshooting

### "Command not found"

```bash
vsh> my-program
Error: Command not found: my-program
```

Check your PATH:
```bash
vsh> echo $PATH
/usr/local/bin:/usr/bin:/bin
```

### "Parent directory does not exist"

```bash
vsh> mkdir foo/bar/baz
Error: Parent directory does not exist (ENOENT)
```

Create parent first:
```bash
vsh> mkdir foo
vsh> mkdir foo/bar
vsh> mkdir foo/bar/baz
```

### "Path already exists"

```bash
vsh> mkdir existing
Error: Path already exists (EEXIST)
```

Check with ls first, or use a different name.

### State File Warnings

If you see:
```
Warning: Failed to save state: Permission denied
Operation succeeded but may not persist across restarts
```

Check permissions on `~/.cache/vsh/`:
```bash
chmod 755 ~/.cache/vsh/
chmod 644 ~/.cache/vsh/state.json
```

---

## What's Next?

### Learn More

- **Examples**: See [EXAMPLES.md](EXAMPLES.md) for real-world usage
- **Architecture**: See [PHASE6_M2_COMPLETE.md](PHASE6_M2_COMPLETE.md) for technical details
- **Proofs**: Browse `proofs/lean4/` for formal verification

### Current Limitations

- ✅ Filesystem operations fully supported
- ✅ I/O redirections working
- ⏳ Pipelines not yet implemented (Phase 6 M3)
- ⏳ Shell scripting not supported
- ⏳ Variables and globs not supported

This is a research prototype. Use for experimentation and learning, not production workloads.

---

## Support

- **Issues**: https://github.com/hyperpolymath/valence-shell/issues
- **Discussions**: https://github.com/hyperpolymath/valence-shell/discussions
- **License**: Perpetual, Limited, Modifiable with Posterity (PLMP-1.0-or-later)

---

**Welcome to formally verified computing!** 🎉

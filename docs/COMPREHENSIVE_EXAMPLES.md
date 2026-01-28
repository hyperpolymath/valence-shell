# Valence Shell: Comprehensive Examples Guide

**Version**: 0.7.1 (Phase 0 Sealing)
**Date**: 2026-01-28
**Author**: Jonathan D.A. Jewell <jonathan.jewell@open.ac.uk>
**License**: PMPL-1.0-or-later

---

## Table of Contents

1. [Getting Started](#getting-started)
2. [Built-in Commands](#built-in-commands)
3. [External Commands](#external-commands)
4. [Navigation](#navigation)
5. [Undo/Redo](#undoredo)
6. [Transactions](#transactions)
7. [Proof References](#proof-references)
8. [Common Workflows](#common-workflows)
9. [Error Handling](#error-handling)
10. [Advanced Usage](#advanced-usage)

---

## Getting Started

### Installation

```bash
cd /var/home/hyper/Documents/hyperpolymath-repos/valence-shell/impl/rust-cli
cargo build --release
./target/release/vsh
```

### Your First Session

```bash
$ vsh
╔═══════════════════════════════════════════════════════════╗
║  ██╗   ██╗ █████╗ ██╗     ███████╗███╗   ██╗ ██████╗███████╗ ║
║  The Thermodynamic Shell - Every operation is reversible     ║
║  Backed by 256 formal proofs across 6 verification systems   ║
╚═══════════════════════════════════════════════════════════╝

vsh> help
# ... help output ...

vsh> mkdir my_project
vsh> cd my_project
vsh> touch README.md
vsh> ls
README.md

vsh> history
1. mkdir my_project [mkdir_rmdir_reversible]
2. touch README.md [create_delete_file_reversible]

vsh> undo 2
# Everything reversed!

vsh> exit
Goodbye!
```

---

## Built-in Commands

### Filesystem Operations (Reversible)

#### mkdir - Create Directory
```bash
vsh> mkdir projects
[op:a1b2c3d4] mkdir projects

vsh> mkdir projects/web
[op:e5f6g7h8] mkdir projects/web

vsh> mkdir /tmp/vsh_test
[op:i9j0k1l2] mkdir /tmp/vsh_test
```

**Errors**:
```bash
vsh> mkdir projects
Error: EEXIST: File exists

vsh> mkdir nonexistent/child
Error: ENOENT: Parent directory does not exist
```

#### rmdir - Remove Directory
```bash
vsh> rmdir projects/web
[op:m3n4o5p6] rmdir projects/web

vsh> rmdir projects
[op:q7r8s9t0] rmdir projects
```

**Errors**:
```bash
vsh> rmdir projects
Error: ENOTEMPTY: Directory not empty

vsh> rmdir file.txt
Error: ENOTDIR: Not a directory
```

#### touch - Create Empty File
```bash
vsh> touch notes.txt
[op:u1v2w3x4] touch notes.txt

vsh> touch docs/design.md
[op:y5z6a7b8] touch docs/design.md
```

**Errors**:
```bash
vsh> touch existing.txt
Error: EEXIST: File exists

vsh> touch nonexistent/file.txt
Error: ENOENT: Parent directory does not exist
```

#### rm - Remove File
```bash
vsh> rm notes.txt
[op:c9d0e1f2] rm notes.txt

vsh> rm docs/design.md
[op:g3h4i5j6] rm docs/design.md
```

**Errors**:
```bash
vsh> rm nonexistent.txt
Error: ENOENT: File does not exist

vsh> rm projects
Error: EISDIR: Is a directory (use rmdir)
```

---

## External Commands

### Common Unix Tools

#### ls - List Directory
```bash
vsh> ls
README.md  src/  target/

vsh> ls -la
total 24
drwxr-xr-x  4 hyper hyper 4096 Jan 28 10:00 .
drwxr-xr-x 12 hyper hyper 4096 Jan 28 09:45 ..
-rw-r--r--  1 hyper hyper  234 Jan 28 10:00 README.md

vsh> ls src/*.rs
src/main.rs  src/lib.rs  src/commands.rs
```

#### cat - Display File Contents
```bash
vsh> cat README.md
# Valence Shell
...

vsh> cat -n file.txt
     1  Line one
     2  Line two
```

#### echo - Print Text
```bash
vsh> echo Hello World
Hello World

vsh> echo "Multiple   spaces   preserved"
Multiple   spaces   preserved

vsh> echo $HOME
$HOME
# Note: Variable expansion not implemented yet (Phase 6 M4)
```

#### grep, wc, head, tail
```bash
vsh> grep "TODO" src/*.rs
src/main.rs:// TODO: Add readline support

vsh> wc -l README.md
42 README.md

vsh> head -5 LICENSE
Palimpsest-MPL-1.0-or-later
...

vsh> tail -3 CHANGELOG.md
## [0.7.0] - 2026-01-28
...
```

### External vs Built-in

**Key Difference**: External commands execute but don't create undo history.

```bash
vsh> touch file.txt       # Built-in: creates undo entry
[op:k7l8m9n0] touch file.txt

vsh> cat file.txt         # External: no undo entry
# (empty file)

vsh> undo                 # Undoes the touch, not the cat
[op:o1p2q3r4] undo [op:k7l8m9n0] rm file.txt
```

---

## Navigation

### pwd - Print Working Directory
```bash
vsh> pwd
/var/home/hyper/Documents/hyperpolymath-repos/valence-shell
```

### cd - Change Directory

#### Absolute Paths
```bash
vsh> cd /tmp
vsh> pwd
/tmp

vsh> cd /var/home/hyper
vsh> pwd
/var/home/hyper
```

#### Relative Paths
```bash
vsh> cd Documents
vsh> pwd
/var/home/hyper/Documents

vsh> cd ../Downloads
vsh> pwd
/var/home/hyper/Downloads

vsh> cd ../../tmp
vsh> pwd
/tmp
```

#### Home Directory
```bash
vsh> cd ~
vsh> pwd
/var/home/hyper

vsh> cd ~/Documents/repos
vsh> pwd
/var/home/hyper/Documents/repos

vsh> cd
vsh> pwd
/var/home/hyper
# cd with no arguments goes home
```

#### Previous Directory (cd -)
```bash
vsh> cd /tmp
vsh> pwd
/tmp

vsh> cd /var/home/hyper
vsh> pwd
/var/home/hyper

vsh> cd -
/tmp
vsh> pwd
/tmp

vsh> cd -
/var/home/hyper
vsh> pwd
/var/home/hyper
# cd - toggles between current and previous directory
```

**First Use**:
```bash
vsh> cd -
Error: cd: OLDPWD not set
# No previous directory until you've used cd at least once
```

---

## Undo/Redo

### Basic Undo
```bash
vsh> mkdir test
[op:a1b2c3d4] mkdir test

vsh> undo
[op:e5f6g7h8] undo [op:a1b2c3d4] rmdir test
# Directory removed, operation reversed
```

### Undo Multiple Operations
```bash
vsh> touch file1.txt
[op:i9j0k1l2] touch file1.txt

vsh> touch file2.txt
[op:m3n4o5p6] touch file2.txt

vsh> touch file3.txt
[op:q7r8s9t0] touch file3.txt

vsh> undo 3
[op:u1v2w3x4] undo [op:q7r8s9t0] rm file3.txt
[op:y5z6a7b8] undo [op:m3n4o5p6] rm file2.txt
[op:c9d0e1f2] undo [op:i9j0k1l2] rm file1.txt
# All three files removed
```

### Redo
```bash
vsh> redo
[op:g3h4i5j6] redo [op:c9d0e1f2] touch file1.txt

vsh> redo 2
[op:k7l8m9n0] redo [op:y5z6a7b8] touch file2.txt
[op:o1p2q3r4] redo [op:u1v2w3x4] touch file3.txt
# All three files recreated
```

### History

```bash
vsh> history
1. mkdir test [mkdir_rmdir_reversible]
2. touch file.txt [create_delete_file_reversible]
3. rm file.txt [create_delete_file_reversible]

vsh> history 20
# Show last 20 operations

vsh> history --proofs
1. mkdir test
   Theorem: mkdir_rmdir_reversible (FilesystemModel.lean:158)
   System: Lean 4
   Proof: ∀ fs p, rmdir p (mkdir p fs) = fs

2. touch file.txt
   Theorem: createFile_deleteFile_reversible (FileOperations.lean:89)
   System: Lean 4
   Proof: ∀ fs p, deleteFile p (createFile p fs) = fs
```

---

## Transactions

### Basic Transaction
```bash
vsh> begin setup
Transaction started: setup

vsh/txn:setup> mkdir app
[op:a1b2c3d4] mkdir app

vsh/txn:setup [1↩]> mkdir app/src
[op:e5f6g7h8] mkdir app/src

vsh/txn:setup [2↩]> touch app/README.md
[op:i9j0k1l2] touch app/README.md

vsh/txn:setup [3↩]> commit
Transaction committed: setup (3 operations)

vsh>
```

### Transaction Rollback
```bash
vsh> begin experiment
Transaction started: experiment

vsh/txn:experiment> mkdir temp
[op:m3n4o5p6] mkdir temp

vsh/txn:experiment [1↩]> touch temp/data.txt
[op:q7r8s9t0] touch temp/data.txt

vsh/txn:experiment [2↩]> rollback
Transaction rolled back: experiment (2 operations undone)

vsh> ls temp
Error: No such file or directory
# Everything from the transaction was rolled back
```

### Nested Operations in Transactions
```bash
vsh> begin project-init
Transaction started: project-init

vsh/txn:project-init> mkdir project
[op:u1v2w3x4] mkdir project

vsh/txn:project-init [1↩]> cd project

vsh/txn:project-init [1↩]> mkdir src tests docs
[op:y5z6a7b8] mkdir src
[op:c9d0e1f2] mkdir tests
[op:g3h4i5j6] mkdir docs

vsh/txn:project-init [4↩]> touch src/main.rs
[op:k7l8m9n0] touch src/main.rs

vsh/txn:project-init [5↩]> touch README.md
[op:o1p2q3r4] touch README.md

vsh/txn:project-init [6↩]> commit
Transaction committed: project-init (6 operations)

vsh> graph
# Shows DAG of all operations in the transaction
```

---

## Proof References

### Show All Theorems
```bash
vsh> proofs

╔═══════════════════════════════════════════════════════════╗
║             Formal Verification Summary                   ║
╚═══════════════════════════════════════════════════════════╝

Verified in 6 independent proof systems:
✓ Lean 4 (Dependent Type Theory)
✓ Coq (Calculus of Inductive Constructions)
✓ Agda (Intensional Type Theory)
✓ Isabelle/HOL (Higher-Order Logic)
✓ Mizar (Tarski-Grothendieck Set Theory)
✓ Z3 SMT (First-Order Logic + Theories)

Core Theorems:
• mkdir_rmdir_reversible: Directory creation is reversible
• createFile_deleteFile_reversible: File creation is reversible
• operation_independence: Different paths don't interfere
• operation_sequence_reversible: Complex operations compose correctly

Total: ~256 formal proofs
```

### History with Proof References
```bash
vsh> history --proofs
1. mkdir test_dir
   Theorem: mkdir_rmdir_reversible (FilesystemModel.lean:158)
   System: Lean 4
   Proof: ∀ fs p, rmdir p (mkdir p fs) = fs
   Status: ✓ Proven in 5 systems

2. touch test_dir/file.txt
   Theorem: createFile_deleteFile_reversible (FileOperations.lean:89)
   System: Lean 4
   Proof: ∀ fs p, deleteFile p (createFile p fs) = fs
   Status: ✓ Proven in 5 systems

vsh> history -p
# Shorthand for --proofs
```

---

## Common Workflows

### Project Setup with Transaction
```bash
vsh> begin new-web-app
Transaction started: new-web-app

vsh/txn:new-web-app> mkdir webapp
vsh/txn:new-web-app [1↩]> cd webapp
vsh/txn:new-web-app [1↩]> mkdir src public tests
vsh/txn:new-web-app [4↩]> touch src/index.html
vsh/txn:new-web-app [5↩]> touch src/style.css
vsh/txn:new-web-app [6↩]> touch src/app.js
vsh/txn:new-web-app [7↩]> touch README.md
vsh/txn:new-web-app [8↩]> commit
Transaction committed: new-web-app (8 operations)

vsh> ls
src/  public/  tests/  README.md

vsh> graph
# Visualize the entire transaction as a DAG
```

### Safe Experimentation
```bash
# Try something risky
vsh> begin experiment
vsh/txn:experiment> mkdir temp
vsh/txn:experiment [1↩]> cd temp
vsh/txn:experiment [1↩]> touch test1.txt test2.txt test3.txt

vsh/txn:experiment [4↩]> ls
test1.txt  test2.txt  test3.txt

# Decide you don't like it
vsh/txn:experiment [4↩]> rollback
Transaction rolled back: experiment (4 operations undone)

vsh> ls temp
Error: No such file or directory
# Everything gone like it never happened
```

### Incremental Undo
```bash
vsh> mkdir step1
vsh> mkdir step2
vsh> mkdir step3
vsh> mkdir step4
vsh> mkdir step5

vsh> ls
step1/  step2/  step3/  step4/  step5/

# Realize step4 and step5 were mistakes
vsh> undo 2

vsh> ls
step1/  step2/  step3/

# Actually, undo everything
vsh> undo 3

vsh> ls
# Empty
```

### Redo After Undo
```bash
vsh> touch file.txt
[op:a1b2c3d4] touch file.txt

vsh> undo
[op:e5f6g7h8] undo [op:a1b2c3d4] rm file.txt

vsh> ls
# Empty

# Changed your mind
vsh> redo
[op:i9j0k1l2] redo [op:e5f6g7h8] touch file.txt

vsh> ls
file.txt
```

---

## Navigation

### Basic cd Usage
```bash
vsh> pwd
/var/home/hyper

vsh> cd Documents
vsh> pwd
/var/home/hyper/Documents

vsh> cd repos/valence-shell
vsh> pwd
/var/home/hyper/Documents/repos/valence-shell
```

### Absolute Paths
```bash
vsh> cd /tmp
vsh> pwd
/tmp

vsh> cd /var/log
vsh> pwd
/var/log
```

### Parent Directory
```bash
vsh> cd /var/home/hyper/Documents/repos/valence-shell/impl/rust-cli
vsh> pwd
/var/home/hyper/Documents/repos/valence-shell/impl/rust-cli

vsh> cd ..
vsh> pwd
/var/home/hyper/Documents/repos/valence-shell/impl

vsh> cd ../..
vsh> pwd
/var/home/hyper/Documents/repos
```

### Home Directory
```bash
vsh> cd ~
vsh> pwd
/var/home/hyper

vsh> cd ~/Documents/repos
vsh> pwd
/var/home/hyper/Documents/repos

vsh> cd
vsh> pwd
/var/home/hyper
# cd alone goes home
```

### Previous Directory (cd -)
```bash
vsh> cd /tmp
vsh> pwd
/tmp

vsh> cd /var/home/hyper
vsh> pwd
/var/home/hyper

vsh> cd -
/tmp
vsh> pwd
/tmp

vsh> cd -
/var/home/hyper
vsh> pwd
/var/home/hyper

# Toggle between two directories
vsh> cd -
/tmp
vsh> cd -
/var/home/hyper
vsh> cd -
/tmp
```

---

## Error Handling

### Command Not Found
```bash
vsh> nonexistent-command
nonexistent-command: Command not found: nonexistent-command

vsh> /usr/bin/fake
/usr/bin/fake: Command not found: /usr/bin/fake
```

### Permission Denied
```bash
vsh> cat /etc/shadow
cat: /etc/shadow: Permission denied
# External commands respect system permissions

vsh> mkdir /root/test
Error: EACCES: Permission denied
# Built-ins also enforce permissions
```

### Invalid Arguments
```bash
vsh> mkdir
Error: mkdir: missing path argument

vsh> undo 999
Error: Cannot undo 999 operations (only 5 available)

vsh> begin
Error: begin: missing transaction name
```

### Directory Navigation Errors
```bash
vsh> cd /nonexistent
Error: cd: /nonexistent: No such file or directory

vsh> cd file.txt
Error: cd: file.txt: Not a directory

vsh> cd -
Error: cd: OLDPWD not set
# No previous directory yet
```

---

## Advanced Usage

### Complex Transaction Example
```bash
vsh> begin complex-refactor
Transaction started: complex-refactor

vsh/txn:complex-refactor> mkdir new_structure
vsh/txn:complex-refactor [1↩]> mkdir new_structure/components
vsh/txn:complex-refactor [2↩]> mkdir new_structure/utils
vsh/txn:complex-refactor [3↩]> mkdir new_structure/tests

vsh/txn:complex-refactor [4↩]> touch new_structure/components/App.res
vsh/txn:complex-refactor [5↩]> touch new_structure/components/Header.res
vsh/txn:complex-refactor [6↩]> touch new_structure/utils/Helpers.res
vsh/txn:complex-refactor [7↩]> touch new_structure/tests/App_test.res

vsh/txn:complex-refactor [8↩]> ls new_structure
components/  utils/  tests/

# Verify structure looks good
vsh/txn:complex-refactor [8↩]> ls new_structure/components
App.res  Header.res

# Looks good, commit
vsh/txn:complex-refactor [8↩]> commit
Transaction committed: complex-refactor (8 operations)

vsh> status

═══ Shell Status ═══

  Sandbox root: /var/home/hyper/Documents/repos/valence-shell
  Total operations: 8
  Undoable ops: 8
  Redo stack: 0
  Completed transactions: 1
```

### Mixing Built-ins and External Commands
```bash
vsh> mkdir logs
[op:a1b2c3d4] mkdir logs

vsh> cd logs

vsh> echo "Application started" > app.log
# Note: Redirection not implemented yet
# This will fail, use external tools instead:

vsh> echo "Application started"
Application started
# Then use external tool to redirect if needed

vsh> ls
# ... external ls shows directory contents ...

vsh> touch debug.log
[op:e5f6g7h8] touch debug.log

vsh> cat debug.log
# (empty file)

vsh> history
1. mkdir logs [mkdir_rmdir_reversible]
2. touch debug.log [create_delete_file_reversible]
# Note: external 'ls' and 'cat' don't appear in history
```

### Using the Graph View
```bash
vsh> mkdir a
vsh> mkdir b
vsh> mkdir c

vsh> graph

═══ Operation DAG ═══

┌─────────────────────────────────────┐
│ ✓ state_1 │
└───────────────┬─────────────────────┘
                │ mkdir a
                ▼
┌─────────────────────────────────────┐
│ ✓ state_2 │
└───────────────┬─────────────────────┘
                │ mkdir b
                ▼
┌─────────────────────────────────────┐
│ ✓ state_3 │
└───────────────┬─────────────────────┘
                │ mkdir c
                ▼
┌─────────────────────────────────────┐
│ ✓ state_4 ◄── YOU ARE HERE │
└─────────────────────────────────────┘

Undo path: rmdir c → rmdir b → rmdir a → [initial]

vsh> undo

vsh> graph

═══ Operation DAG ═══

┌─────────────────────────────────────┐
│ ✓ state_1 │
└───────────────┬─────────────────────┘
                │ mkdir a
                ▼
┌─────────────────────────────────────┐
│ ✓ state_2 │
└───────────────┬─────────────────────┘
                │ mkdir b
                ▼
┌─────────────────────────────────────┐
│ ✓ state_3 ◄── YOU ARE HERE │
└───────────────┬─────────────────────┘
                │ mkdir c (undone)
                ▼
┌─────────────────────────────────────┐
│ ✗ state_4 │
└─────────────────────────────────────┘

Undo path: rmdir b → rmdir a → [initial]
```

### Interrupt External Commands
```bash
vsh> sleep 100
^C
# Ctrl+C terminates immediately, exit code 130

vsh> sleep 10
^C

vsh> echo "Still works"
Still works
# Shell remains responsive after interrupt
```

---

## Shell Shortcuts

### Aliases
```bash
vsh> u          # Short for 'undo'
vsh> r          # Short for 'redo'
vsh> h          # Short for 'history'
vsh> g          # Short for 'graph'
vsh> q          # Short for 'quit'
```

### Special Commands
```bash
vsh> help       # Show help
vsh> ?          # Also shows help
vsh> status     # Show shell status
vsh> clear      # Clear screen
vsh> exit       # Exit shell
vsh> quit       # Exit shell
```

---

## Status Display

```bash
vsh> status

═══ Shell Status ═══

  Sandbox root: /var/home/hyper/Documents/repos/valence-shell
  Total operations: 47
  Undoable ops: 42
  Redo stack: 5
  Completed transactions: 3
```

With active transaction:
```bash
vsh> begin feature-x
vsh/txn:feature-x> mkdir new_feature
vsh/txn:feature-x [1↩]> status

═══ Shell Status ═══

  Sandbox root: /var/home/hyper/Documents/repos/valence-shell
  Total operations: 48
  Undoable ops: 43
  Redo stack: 0

  Active transaction: feature-x (1 ops)

  Completed transactions: 3
```

---

## Tips and Tricks

### 1. Use Transactions for Complex Changes
```bash
# Instead of:
vsh> mkdir a
vsh> mkdir b
vsh> mkdir c
vsh> undo 3  # If you change your mind

# Do this:
vsh> begin try-new-layout
vsh/txn:try-new-layout> mkdir a
vsh/txn:try-new-layout> mkdir b
vsh/txn:try-new-layout> mkdir c
vsh/txn:try-new-layout> rollback  # Atomic rollback
```

### 2. Verify Before Committing
```bash
vsh> begin cleanup
vsh/txn:cleanup> rm old_file1.txt
vsh/txn:cleanup> rm old_file2.txt
vsh/txn:cleanup> ls  # External ls to verify
# Check everything looks good
vsh/txn:cleanup> commit
```

### 3. Use History to Understand State
```bash
vsh> history --proofs
# See what operations led to current state
# Each operation shows its formal proof
```

### 4. Graph View for Debugging
```bash
vsh> graph
# Visualize operation sequence
# See which operations were undone
# Understand current position in history
```

### 5. cd - for Quick Navigation
```bash
vsh> cd /var/log
# Do some work
vsh> cd ~/Documents
# Do some work
vsh> cd -
# Back to /var/log instantly
```

---

## Comparison with bash/zsh

| Feature | bash/zsh | vsh 0.7.1 |
|---------|----------|-----------|
| External commands | ✓ | ✓ |
| Built-in cd | ✓ | ✓ |
| cd - | ✓ | ✓ |
| PATH lookup | ✓ | ✓ |
| Exit codes | ✓ | ✓ (tracked) |
| Ctrl+C handling | ✓ | ✓ |
| Undo/redo | ❌ | ✓ |
| Transactions | ❌ | ✓ |
| Formal proofs | ❌ | ✓ (256+) |
| Pipes (`\|`) | ✓ | ❌ (Phase 6 M3) |
| Redirections (`>`) | ✓ | ❌ (Phase 6 M2) |
| Variables (`$VAR`) | ✓ | ❌ (Phase 6 M4) |
| Glob expansion | ✓ | ❌ (Phase 6 M5) |
| Scripting | ✓ | ❌ (Phase 6+) |

---

## What's Not Implemented (Yet)

### Phase 6 M2: Redirections
```bash
vsh> echo "hello" > file.txt
# NOT WORKING YET - Planned for Phase 6 M2
```

### Phase 6 M3: Pipelines
```bash
vsh> ls | grep ".txt"
# NOT WORKING YET - Planned for Phase 6 M3
```

### Phase 6 M4: Variables
```bash
vsh> NAME="world"
vsh> echo "Hello $NAME"
# NOT WORKING YET - Planned for Phase 6 M4
```

### Phase 6 M5+: Advanced Features
```bash
vsh> rm *.txt              # Glob expansion
vsh> echo "hello world"    # Quote processing
vsh> sleep 10 &            # Job control
# All planned for Phase 6 M5-M14
```

See `docs/POSIX_COMPLIANCE.md` for full roadmap.

---

## Performance Notes

### Startup Time
```bash
$ time vsh --version
vsh 0.7.1
A formally verified reversible shell

real    0m0.008s
user    0m0.004s
sys     0m0.004s
```
**8ms cold start** (target: 5ms, bash: ~5ms)

### Command Execution
- Parser: <0.1ms
- PATH lookup: ~0.2ms
- Built-in ops: <1ms
- External commands: ~3-5ms

---

## Troubleshooting

### Ctrl+C Doesn't Stop Command
```bash
# Use Ctrl+\ (SIGQUIT) as fallback
vsh> sleep 1000
^\
# Sends SIGQUIT instead
```

### Shell Exits Unexpectedly
Check if you have uncommitted transaction:
```bash
vsh/txn:my-work> exit
# Transaction is NOT auto-committed
# You'll lose the transaction
```

### Redo Stack Cleared
```bash
vsh> undo
vsh> undo
vsh> redo
vsh> touch newfile.txt  # New operation clears redo stack!
vsh> redo
Error: No operations to redo
# This is expected - redo stack clears when you perform new operations
```

---

## Further Reading

- `docs/ARCHITECTURE.md` - System design and architecture
- `docs/LEAN4_RUST_CORRESPONDENCE.md` - Proof ↔ implementation mapping
- `docs/POSIX_COMPLIANCE.md` - Roadmap to full POSIX shell
- `docs/SIGINT_TESTING.md` - Signal handling details
- `proofs/README.md` - Formal verification details

---

**Questions or Issues?**

- GitLab: https://gitlab.com/non-initiate/rhodinised/vsh
- GitHub: https://github.com/hyperpolymath/valence-shell
- Email: jonathan.jewell@open.ac.uk

---

**Version**: 0.7.1 (Phase 0 Sealing)
**License**: PMPL-1.0-or-later
**Verified**: 256+ theorems across 6 proof systems

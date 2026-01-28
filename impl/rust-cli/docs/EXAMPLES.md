# Valence Shell - Usage Examples

Real-world usage patterns for valence-shell operations.

---

## Example 1: Project Scaffolding with Rollback

Create a project structure, verify it works, or rollback if it doesn't:

```bash
vsh> begin new-project
[txn:12345678] begin new-project

vsh> mkdir myapp
[op:23456789] mkdir myapp

vsh> mkdir myapp/src
[op:34567890] mkdir myapp/src

vsh> mkdir myapp/tests
[op:45678901] mkdir myapp/tests

vsh> touch myapp/README.md
[op:56789012] touch myapp/README.md

vsh> touch myapp/src/main.rs
[op:67890123] touch myapp/src/main.rs

vsh> ls myapp > myapp/structure.txt
[op:78901234] ls myapp

vsh> commit
Transaction committed: 6 operations
```

If you made a mistake:

```bash
vsh> rollback new-project
Transaction rolled back: 6 operations
# All changes undone - clean slate
```

---

## Example 2: Log File Rotation with Undo

Rotate logs safely with the ability to revert:

```bash
vsh> ls logs
📄 app.log
📄 app.log.1
📄 app.log.2

vsh> begin log-rotate
[txn:abcdef01] begin log-rotate

vsh> rm logs/app.log.2
[op:bcdef012] rm logs/app.log.2

vsh> mv logs/app.log.1 logs/app.log.2
# (mv not implemented yet - use external command)

vsh> mv logs/app.log logs/app.log.1
# (external mv not reversible)

vsh> touch logs/app.log
[op:cdef0123] touch logs/app.log

vsh> commit
```

Better approach (when you realize external mv isn't reversible):

```bash
vsh> rollback log-rotate
# Undoes only the vsh operations (rm, touch)

# Use transaction for atomic rotation
# (Feature request: Built-in mv command)
```

---

## Example 3: Batch File Operations

Create multiple files with redirection:

```bash
vsh> begin batch-create
[txn:def01234] begin batch-create

vsh> echo "File 1" > file1.txt
[op:ef012345] echo

vsh> echo "File 2" > file2.txt
[op:f0123456] echo

vsh> echo "File 3" > file3.txt
[op:01234567] echo

vsh> ls > inventory.txt
[op:12345678] ls

vsh> commit
Transaction committed: 4 operations
```

Undo creates and writes:

```bash
vsh> undo 4
[op:23456789] undo [op:12345678] DeleteFile inventory.txt
[op:34567890] undo [op:01234567] DeleteFile file3.txt
[op:45678901] undo [op:f0123456] DeleteFile file2.txt
[op:56789012] undo [op:ef012345] DeleteFile file1.txt
```

---

## Example 4: Redirection Pipelines

### Capture Command Output

```bash
vsh> ls -la > full-listing.txt
[op:67890123] ls
# Long listing saved to file

vsh> cat full-listing.txt
drwxr-xr-x  project/
-rw-r--r--  README.md
```

### Append to Logs

```bash
vsh> echo "[INFO] Starting process" >> app.log
[op:78901234] echo

vsh> date >> app.log
[op:89012345] date

vsh> echo "[INFO] Process complete" >> app.log
[op:90123456] echo

vsh> cat app.log
[INFO] Starting process
Tue Jan 28 14:30:00 UTC 2026
[INFO] Process complete
```

### Error Logging

```bash
vsh> find /restricted 2> errors.log
# Permission errors captured in errors.log

vsh> cat errors.log
find: /restricted: Permission denied
```

---

## Example 5: Verification Workflow

Verify operations with proof references:

```bash
vsh> mkdir build --verbose
[op:01234567] mkdir build
    Proof: mkdir_rmdir_reversible (FilesystemModel.lean:158)
    Undo: rmdir build

vsh> history --proofs
═══ Operation History ═══

[01234567] 14:30:00 mkdir build
    Theorem: mkdir_rmdir_reversible (FilesystemModel.lean:158)
```

---

## Example 6: Safe Cleanup

Clean up temporary files with undo safety:

```bash
vsh> begin cleanup
[txn:12345678] begin cleanup

vsh> rm temp1.txt
[op:23456789] rm temp1.txt

vsh> rm temp2.txt
[op:34567890] rm temp2.txt

vsh> rmdir temp-dir
[op:45678901] rmdir temp-dir

vsh> commit
Transaction committed: 3 operations
```

If you accidentally deleted something important:

```bash
vsh> undo 3
# All files restored from undo data
```

---

## Example 7: Operation Independence

Operations on different paths don't interfere:

```bash
vsh> mkdir alpha
[op:56789012] mkdir alpha

vsh> mkdir beta
[op:67890123] mkdir beta

vsh> undo
[op:78901234] undo [op:67890123] rmdir beta

vsh> ls
📁 alpha/
# beta removed, alpha unaffected
```

---

## Example 8: Transaction Rollback

Rollback when operations fail mid-transaction:

```bash
vsh> begin risky
[txn:89012345] begin risky

vsh> mkdir test
[op:90123456] mkdir test

vsh> touch test/file.txt
[op:01234567] touch test/file.txt

# Oops - need to abort
vsh> rollback risky
Transaction rolled back: 2 operations

vsh> ls test
Error: Path does not exist
# Everything cleaned up
```

---

## Example 9: Redirected Undo

File modifications are tracked:

```bash
vsh> echo "version 1" > data.txt
[op:12345678] echo

vsh> cat data.txt
version 1

vsh> echo "version 2" > data.txt
[op:23456789] echo

vsh> cat data.txt
version 2

vsh> undo
[op:34567890] undo [op:23456789] WriteFile data.txt
# File truncation reversed - original content restored

vsh> cat data.txt
version 1
```

---

## Example 10: Interrupting Long Commands

Ctrl+C stops external commands:

```bash
vsh> sleep 300
# Press Ctrl+C after a few seconds
^C
[Interrupted - exit code 130]

vsh> # Shell still responsive
```

---

## Common Patterns

### Pattern: Experimental Changes

```bash
begin experiment
# Make changes
# Test them
commit  # If good
# OR
rollback experiment  # If bad
```

### Pattern: Staged Operations

```bash
mkdir stage1
touch stage1/file.txt
# Verify stage1 works
mkdir stage2
# Verify stage2 works
# All operations are individually undoable
```

### Pattern: Redirection with Undo Safety

```bash
ls > backup-listing.txt
# Oops - wrong file
undo
# File deleted automatically
ls > correct-listing.txt
```

---

## Advanced Usage

### Operation Graph Navigation

```bash
vsh> graph
# Shows current state in DAG

vsh> history
# Shows linear history

vsh> undo
# Move backward in DAG

vsh> redo
# Move forward in DAG
```

### Proof Verification

Every operation corresponds to a Lean 4 theorem:

| Operation | Theorem | File |
|-----------|---------|------|
| mkdir | mkdir_rmdir_reversible | FilesystemModel.lean:158 |
| rmdir | rmdir_mkdir_reversible | FilesystemModel.lean:184 |
| touch | createFile_deleteFile_reversible | FileOperations.lean:42 |
| rm | deleteFile_createFile_reversible | FileOperations.lean:52 |
| > | truncate_restore_reversible | FileContentOperations.lean:109 |
| >> | append_truncate_reversible | FileContentOperations.lean:297 |

---

## Next Steps

- Read [PHASE6_M2_COMPLETE.md](PHASE6_M2_COMPLETE.md) for technical details
- Explore `proofs/lean4/` for formal verification
- Try building your own verified operations

---

**Remember**: vsh is a research prototype. Use it to explore formally verified computing, not for production systems (yet).

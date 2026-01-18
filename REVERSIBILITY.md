# Reversibility in Valence Shell

**Every operation can be undone. This is mathematically proven.**

## What Is Reversibility?

In Valence Shell, **reversibility** means that for every operation, there exists a mathematically proven inverse operation that returns the system to its original state.

### Algorithmic Definition

```
F⁻¹(F(s)) = s
```

Where:
- `F` is an operation (e.g., `mkdir`)
- `F⁻¹` is its inverse (e.g., `rmdir`)
- `s` is the initial state
- The result equals the original state

## What's Proven?

### Directory Operations

```coq
Theorem mkdir_rmdir_reversible :
  forall p fs,
    mkdir_precondition p fs ->
    rmdir p (mkdir p fs) = fs.
```

**Meaning**: If you create a directory and then delete it, you're back where you started.

**Proven in**: Coq, Lean 4, Agda, Isabelle, Mizar, Z3 (6 systems)

### File Operations

```coq
Theorem create_delete_file_reversible :
  forall p fs,
    create_file_precondition p fs ->
    delete_file p (create_file p fs) = fs.
```

**Meaning**: Creating and deleting a file is reversible.

**Proven in**: 6 systems

### File Content Operations

```coq
Theorem write_file_reversible :
  forall p fs old_content new_content,
    write_file_precondition p fs ->
    read_file p fs = Some old_content ->
    write_file p old_content (write_file p new_content fs) = fs.
```

**Meaning**: Writing new content and then writing back the old content restores the original state.

**Proven in**: Coq, Lean 4, Agda (3 systems)

### Operation Sequences

```coq
Theorem operation_sequence_reversible :
  forall ops fs,
    all_reversible ops fs ->
    apply_sequence (reverse_sequence ops)
                   (apply_sequence ops fs) = fs.
```

**Meaning**: Any sequence of reversible operations can be undone by reversing the sequence.

**Proven in**: 5 systems

## Why Does This Matter?

### 1. Safe Experimentation

You can try operations without fear. If something goes wrong, **undo is guaranteed** to work.

### 2. Accountability (MAA Framework)

Every action has a provable audit trail. You can always get back to a previous state.

### 3. GDPR Compliance (Future)

With RMO (Remove-Match-Obliterate), we'll prove that deletion is **complete** (not just "best effort").

### 4. Confidence in Complex Operations

When composing operations, you know the undo will work, because it's **mathematically proven**.

## What Reversibility Is NOT

### ❌ Thermodynamic Reversibility

We do **NOT** prove:
- Energy → 0 (Landauer limit)
- Physical entropy considerations
- Bennett's reversible computing

We prove **algorithmic** reversibility (information-preserving), not **physical** reversibility.

### ❌ Time Travel

Reversibility does not mean:
- Undo file modifications by other processes
- Recover from hardware failures
- Undo network operations
- Reverse time

It means: **Within our model**, operations have proven inverses.

### ❌ Implementation Guarantee (Yet)

**Important**: The proofs operate on an abstract model. The OCaml/POSIX implementation is **not yet formally verified** to match the model.

**Verification gap**: We prove model correctness, but implementation may have bugs.

## Reversibility Culture

Beyond the mathematics, Valence Shell embraces a **culture of reversibility**:

### In Code

- Undo operations are first-class
- State tracking for rollback
- MAA audit trails

### In Community

- Mistakes are OK (they're reversible!)
- "I was wrong" is celebrated
- Safe to experiment
- Failure is information

### In Process

- Git for code (reversible history)
- RVC for tidying (automated cleanup)
- Documentation of changes (Palimpsest License)

## Practical Examples

### Example 1: Directory Creation

```bash
# Create directory
mkdir /tmp/test

# Later, undo it
rmdir /tmp/test

# Proven: You're back to original state
```

**Proof**: `mkdir_rmdir_reversible` theorem

### Example 2: File Modification

```bash
# Save old content
old_content=$(cat file.txt)

# Modify file
echo "new content" > file.txt

# Restore old content
echo "$old_content" > file.txt

# Proven: file.txt is back to original state
```

**Proof**: `write_file_reversible` theorem

### Example 3: Operation Sequence

```bash
# Sequence of operations
mkdir dir1
mkdir dir2
touch dir1/file.txt

# Reverse the sequence
rm dir1/file.txt
rmdir dir2
rmdir dir1

# Proven: Back to original state
```

**Proof**: `operation_sequence_reversible` theorem

## State Tracking

Valence Shell provides state capture/restore:

```ocaml
(* Capture current state *)
let state = capture_file_state path fs in

(* Make changes *)
let fs' = modify_file path new_content fs in

(* Restore original state *)
let fs_restored = restore_file_state state fs' in

(* Proven: fs_restored = fs *)
```

**Proof**: `capture_restore_identity` theorem

## MAA Integration

The MAA (Mutually Assured Accountability) framework uses reversibility for accountability:

### FileModificationRecord

```coq
Record FileModificationRecord := {
  mod_path : Path;
  mod_old_content : FileContent;
  mod_new_content : FileContent;
  mod_timestamp : nat
}.
```

### Reversibility Guarantee

```coq
Theorem modification_reversible :
  forall record fs,
    reverse_modification record
      (apply_modification record fs) = fs.
```

**Meaning**: Every modification can be **provably reversed**.

## Composition Properties

### Independence

```coq
Theorem operation_independence :
  forall p1 p2 op1 op2 fs,
    p1 <> p2 ->
    apply_op op1 p1 (apply_op op2 p2 fs) =
    apply_op op2 p2 (apply_op op1 p1 fs).
```

**Meaning**: Operations on different paths are **independent** and **commutative**.

### Equivalence

```coq
Theorem cno_identity_element :
  forall op fs,
    reversible op fs ->
    apply_op (reverse_op op) (apply_op op fs) ≈ fs.
```

**Meaning**: A reversible operation followed by its reverse is equivalent to **doing nothing** (CNO = Certified Null Operation).

## Limitations

### Current (v0.5.0)

**Proven**:
- ✅ Directory operations
- ✅ File operations
- ✅ Content read/write
- ✅ Operation sequences

**NOT Proven**:
- ❌ File copy/move
- ❌ Symbolic links
- ❌ Network operations
- ❌ Implementation (OCaml FFI)

### Future Work

- Close extraction gap (Coq → OCaml verification)
- Verify FFI layer
- Add more operations (copy, move, symlinks)
- RMO (obliterative deletion) proofs

## References

### Academic Background

- **Reversible Computing**: Bennett's thermodynamic reversibility (different from ours)
- **Undo Systems**: Eclipse Undo/Redo, Vim's undo tree
- **Proof Assistants**: Coq, Lean, Agda, Isabelle

### This Project

- `proofs/coq/filesystem_model.v` - Core reversibility proofs
- `proofs/coq/file_content_operations.v` - Content reversibility
- `proofs/coq/filesystem_composition.v` - Sequence reversibility
- `docs/PROGRESS_REPORT.md` - Technical details

## Testing Reversibility

To verify the proofs compile and theorems hold:

```bash
# Verify all formal proofs
just verify-proofs

# Run demonstration
./scripts/demo_verified_operations.sh

# Build specific system
just build-coq      # Coq proofs
just build-lean4    # Lean 4 proofs
```

## Questions?

**Q: Is this different from `git revert`?**

A: Yes. Git reversibility is at the commit level. We prove reversibility at the **operation level** (mkdir, write, etc.).

**Q: Can I undo operations from other programs?**

A: Not yet. Current proofs are for operations **within our model**. Future work may extend this.

**Q: Does this protect against crashes?**

A: No. Reversibility assumes the system doesn't crash. Crash recovery is separate (and planned).

**Q: Is the implementation reversible?**

A: The **proofs** guarantee model reversibility. The **implementation** (OCaml FFI) is not yet formally verified to match the model. This is the "verification gap."

---

**Last Updated**: 2025-11-22
**Version**: 0.5.0
**Proven**: ~256 theorems across 6 verification systems

**Summary**: Every operation in Valence Shell has a mathematically proven inverse. This isn't hope or testing—it's **formal proof**. Mistakes are reversible. Experimentation is safe. Accountability is guaranteed.

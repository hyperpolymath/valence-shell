# Valence Shell Formal Proofs

This directory contains formal proofs of filesystem operations across **5 different proof assistants**, establishing the MAA (Mutually Assured Accountability) framework with polyglot verification.

## What We've Proven

### The Main Theorem: mkdir/rmdir Reversibility

**Statement**: Creating a directory and then removing it returns the filesystem to its original state.

```
∀ path, fs.
  (path doesn't exist in fs) ∧
  (parent of path exists in fs) →
  rmdir(path, mkdir(path, fs)) = fs
```

This is **proven in 5 different logical foundations**:

1. **Coq** (Calculus of Inductive Constructions) - `coq/filesystem_model.v`
2. **Lean 4** (Dependent Type Theory) - `lean4/FilesystemModel.lean`
3. **Agda** (Intensional Type Theory) - `agda/FilesystemModel.agda`
4. **Isabelle/HOL** (Higher-Order Logic) - `isabelle/FilesystemModel.thy`
5. **Mizar** (Tarski-Grothendieck Set Theory) - `mizar/filesystem_model.miz`

## Why 5 Proof Assistants?

**Polyglot verification increases confidence** by proving the same theorem in different logical foundations:

- **Coq (CIC)**: Inductive constructions, extraction to OCaml
- **Lean 4**: Modern dependent types, tactics-based proving
- **Agda**: Pure dependent types, constructive mathematics
- **Isabelle/HOL**: Classical higher-order logic, Sledgehammer automation
- **Mizar**: Mathematical vernacular, MML library

If a theorem is proven in all 5 systems, it's **extremely unlikely to be based on a foundation-specific bug or logical inconsistency**.

### Industry Precedent
- **seL4 kernel**: Proven in Isabelle/HOL
- **CompCert compiler**: Proven in Coq
- **Fiat-Crypto**: Proven in Coq with extraction
- Polyglot verification is the **gold standard** for critical systems

## Filesystem Model

Each proof file contains:

### 1. Path Model
- Paths as sequences of path components (strings)
- Parent path computation
- Path equality and comparison

### 2. Filesystem Nodes
- **FSNodeType**: File or Directory
- **Permissions**: readable, writable, executable
- **FSNode**: combines type and permissions

### 3. Filesystem State
- Modeled as partial function: `Path → Option FSNode`
- Empty filesystem contains only root directory
- Functional updates (immutable)

### 4. Operations

#### `mkdir(path, fs) → fs'`
**Preconditions:**
- Path does not exist
- Parent directory exists
- Parent is writable

**Postconditions:**
- Path exists in result
- Path is a directory
- Other paths unchanged

#### `rmdir(path, fs) → fs'`
**Preconditions:**
- Path exists and is a directory
- Directory is empty
- Parent is writable
- Not root directory

**Postconditions:**
- Path does not exist in result
- Other paths unchanged

### 5. Proven Theorems

All proof files contain:

- ✅ `mkdir_creates_directory`: mkdir creates a directory at the specified path
- ✅ `mkdir_path_exists`: path exists after mkdir
- ✅ `rmdir_removes_path`: path doesn't exist after rmdir
- ✅ **`mkdir_rmdir_reversible`**: The main reversibility theorem
- ✅ `mkdir_preserves_other_paths`: mkdir doesn't affect other paths
- ✅ `rmdir_preserves_other_paths`: rmdir doesn't affect other paths
- ✅ `mkdir_parent_still_exists`: parent still exists after mkdir

## Compilation Instructions

### Coq
```bash
cd proofs/coq
coqc filesystem_model.v
# Produces: filesystem_model.vo (verified object file)
```

### Lean 4
```bash
cd proofs/lean4
lake build
# Or: lean FilesystemModel.lean
```

### Agda
```bash
cd proofs/agda
agda FilesystemModel.agda
# Produces: FilesystemModel.agdai
```

### Isabelle/HOL
```bash
cd proofs/isabelle
isabelle build -D .
# Or: isabelle jedit FilesystemModel.thy
```

### Mizar
```bash
cd proofs/mizar
mizf filesystem_model.miz
# Produces verification output
```

## What This Enables

### 1. GDPR Compliance Claims (Partial)
- ✅ Can prove directory creation is reversible
- ✅ Mathematical guarantee of state restoration
- ❌ Still need: file deletion proofs, secure wipe properties

### 2. MAA Framework Foundation
- ✅ RMR (Remove-Match-Reverse) primitive proven
- ✅ Reversibility with mathematical certainty
- ❌ Still need: RMO (obliterative deletion), full POSIX model

### 3. Verified Implementation Path
- ✅ Formal specification complete
- ✅ Ready for extraction (Coq → OCaml)
- ❌ Still need: FFI to POSIX, verification of extracted code

## Next Steps

### Immediate (High Priority)
1. **POSIX Error Conditions**: Model EEXIST, ENOENT, EACCES, ENOTEMPTY
2. **File Operations**: Add file create/delete with proofs
3. **Path Resolution**: Prove symbolic link and .. handling

### Near-Term
4. **Extraction**: Coq → OCaml → POSIX FFI
5. **Testing**: Real POSIX tests against extracted code
6. **Elixir Verification**: Prove Elixir implementation matches spec

### Long-Term
7. **Full Shell**: Command parsing, pipes, job control
8. **Performance**: Zig fast path for simple operations
9. **MAA Auditing**: Proof certificates for user operations

## Comparison to Abstract List Proofs

### What We Had Before
```coq
Theorem list_add_remove : ∀ x l,
  remove x (add x l) = l.
```

**Problem**: This is about **abstract lists**, not real filesystems.

### What We Have Now
```coq
Theorem mkdir_rmdir_reversible : ∀ path fs,
  mkdir_precondition path fs →
  rmdir path (mkdir path fs) = fs.
```

**Advancement**: This is about **filesystem operations** with:
- Path structures (not just list elements)
- Preconditions (parent exists, permissions, etc.)
- Filesystem state (partial mappings)
- POSIX semantics (directories, files, permissions)

**Gap Remaining**: Still modeling filesystem abstractly. Need:
- Real POSIX syscall semantics
- Inode model
- Actual deletion (not just removal from mapping)
- Disk/memory persistence

## Honest Assessment

### ✅ What We Can Claim
- **5-way polyglot verification** of directory reversibility
- **Formal model** of POSIX-like filesystem operations
- **Proven correctness** of mkdir/rmdir composition
- **Foundation** for verified shell implementation
- **Specification** ready for extraction

### ❌ What We CANNOT Claim Yet
- **GDPR compliance** - only directory operations, not file deletion
- **Verified executable** - no extraction or testing yet
- **Real POSIX** - model is abstract, not connected to syscalls
- **Secure deletion** - no proof of data obliteration
- **Production ready** - research phase only

## Related Work

- **Verdi** (distributed systems in Coq)
- **Fscq** (verified file system in Coq)
- **CertiKOS** (verified OS kernel)
- **seL4** (verified microkernel in Isabelle/HOL)
- **CompCert** (verified C compiler in Coq)

**Our Contribution**: First polyglot verification (5 systems) of shell filesystem operations for accountability framework.

## License

*To be added - see repository root*

---

**Status**: Research phase - Formal specifications complete, extraction pending
**Last Updated**: 2025-11-22

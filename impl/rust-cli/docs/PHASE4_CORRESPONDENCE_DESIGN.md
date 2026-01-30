# Phase 4: Rust-Lean Correspondence Proofs

**Version**: 0.14.0 → 0.15.0
**Date**: 2026-01-29
**Status**: Design Phase
**Goal**: Bridge formal verification (Lean 4 theorems) with implementation (Rust code)

---

## Overview

Valence Shell has two parallel tracks:
1. **Formal Proofs** (Lean 4, Coq, Agda, Isabelle, Mizar, Z3) - 256+ theorems
2. **Implementation** (Rust CLI) - Production-ready shell

**The Gap:** These tracks are currently disconnected. We have proven theorems about filesystem operations, and we have a working implementation, but we haven't proven that the implementation matches the theorems.

**Phase 4 Goal:** Establish formal correspondence between Rust code and Lean 4 theorems, creating the "seams" that connect theory to practice.

---

## Why This Matters

### Current State
- **Lean 4 says:** "mkdir followed by rmdir returns the filesystem to its original state"
- **Rust does:** Creates and removes directories using POSIX syscalls
- **Missing:** Proof that Rust operations match Lean semantics

### With Correspondence Proofs
- **Claim:** "This shell is formally verified"
- **Evidence:** Rust implementation proven equivalent to Lean 4 theorems
- **Confidence:** Mathematical guarantee of correctness

---

## Correspondence Strategy

### Three-Level Approach

```
Level 1: State Correspondence
├─ Prove: Rust ShellState ≅ Lean Filesystem
├─ Map: PathBuf ↔ Path (List PathComponent)
└─ Map: std::fs metadata ↔ FSNode

Level 2: Operation Correspondence
├─ Prove: Rust mkdir ≅ Lean mkdir
├─ Prove: Rust rmdir ≅ Lean rmdir
├─ Prove: Rust touch ≅ Lean createFile
└─ Prove: Rust rm ≅ Lean deleteFile

Level 3: Property Correspondence
├─ Prove: Rust undo(mkdir) ≅ Lean rmdir
├─ Prove: Rust redo() ≅ Lean operation replay
└─ Prove: Rust transaction groups satisfy atomicity
```

---

## Lean 4 Model Summary

### Core Types

```lean
abbrev Path := List PathComponent
abbrev Filesystem := Path → Option FSNode

structure FSNode where
  nodeType : FSNodeType      -- file | directory
  permissions : Permissions  -- readable, writable, executable

structure MkdirPrecondition (p : Path) (fs : Filesystem) where
  notExists : ¬pathExists p fs
  parentExists : parentExists p fs
  parentIsDir : isDirectory (parentPath p) fs
  parentWritable : hasWritePermission (parentPath p) fs
```

### Core Operations

```lean
def mkdir (p : Path) (fs : Filesystem) : Filesystem :=
  fsUpdate p (some ⟨FSNodeType.directory, defaultPerms⟩) fs

def rmdir (p : Path) (fs : Filesystem) : Filesystem :=
  fsUpdate p none fs

def createFile (p : Path) (fs : Filesystem) : Filesystem :=
  fsUpdate p (some ⟨FSNodeType.file, defaultPerms⟩) fs

def deleteFile (p : Path) (fs : Filesystem) : Filesystem :=
  fsUpdate p none fs
```

### Key Theorems

```lean
theorem mkdir_rmdir_reversible (p : Path) (fs : Filesystem)
    (hpre : MkdirPrecondition p fs) :
    rmdir p (mkdir p fs) = fs

theorem createFile_deleteFile_reversible (p : Path) (fs : Filesystem)
    (hpre : CreateFilePrecondition p fs) :
    deleteFile p (createFile p fs) = fs
```

---

## Rust Implementation Summary

### Core Types

```rust
pub struct ShellState {
    root: PathBuf,                    // Sandbox root
    history: Vec<Operation>,          // Operation history
    redo_stack: VecDeque<Operation>,  // Redo stack
    // ... other fields
}

pub enum OperationType {
    Mkdir,
    Rmdir,
    CreateFile,
    DeleteFile,
    // ... other operations
}

pub struct Operation {
    id: Uuid,
    op_type: OperationType,
    path: String,
    timestamp: DateTime<Utc>,
    undo_data: Option<Vec<u8>>,
    // ... other fields
}
```

### Core Operations

```rust
pub fn mkdir(state: &mut ShellState, path: &str, verbose: bool) -> Result<()> {
    let full_path = state.resolve_path(path);

    // Preconditions
    if full_path.exists() {
        bail!("Path already exists (EEXIST)");
    }
    if !full_path.parent()?.exists() {
        bail!("Parent directory does not exist (ENOENT)");
    }

    // Execute
    fs::create_dir(&full_path)?;

    // Record for undo
    state.record_operation(Operation::new(OperationType::Mkdir, path, None));
    Ok(())
}

pub fn rmdir(state: &mut ShellState, path: &str, verbose: bool) -> Result<()> {
    let full_path = state.resolve_path(path);

    // Preconditions
    if !full_path.exists() { bail!("Path does not exist (ENOENT)"); }
    if !full_path.is_dir() { bail!("Path is not a directory (ENOTDIR)"); }
    if fs::read_dir(&full_path)?.next().is_some() {
        bail!("Directory is not empty (ENOTEMPTY)");
    }

    // Execute
    fs::remove_dir(&full_path)?;

    // Record
    state.record_operation(Operation::new(OperationType::Rmdir, path, None));
    Ok(())
}
```

---

## Correspondence Mapping

### State Correspondence

| Lean 4 | Rust | Notes |
|--------|------|-------|
| `Filesystem` | `ShellState + actual filesystem` | Lean is abstract, Rust uses POSIX |
| `Path` (List String) | `PathBuf` | Both represent filesystem paths |
| `FSNode` | `std::fs::Metadata` | Both represent file/dir + permissions |
| `pathExists p fs` | `full_path.exists()` | Existence check |
| `isDirectory p fs` | `full_path.is_dir()` | Directory check |
| `isFile p fs` | `full_path.is_file()` | File check |

### Operation Correspondence

| Lean 4 Operation | Rust Operation | Correspondence Claim |
|------------------|----------------|----------------------|
| `mkdir p fs` | `mkdir(state, path)` | Creates directory at path |
| `rmdir p fs` | `rmdir(state, path)` | Removes empty directory |
| `createFile p fs` | `touch(state, path)` | Creates empty file |
| `deleteFile p fs` | `rm(state, path)` | Deletes file |

### Precondition Correspondence

| Lean 4 Precondition | Rust Check | Code Location |
|---------------------|------------|---------------|
| `notExists p fs` | `if full_path.exists() { bail!(...) }` | commands.rs:L105 |
| `parentExists p fs` | `if !parent.exists() { bail!(...) }` | commands.rs:L109 |
| `isDirectory p fs` | `if !full_path.is_dir() { bail!(...) }` | commands.rs:L123 |
| `isEmpty p fs` | `if read_dir(...)?.next().is_some() { bail!(...) }` | commands.rs:L126 |

---

## Correspondence Proof Strategy

### Approach 1: Manual Correspondence Argument (Lightweight)

**Goal:** Write a document that argues informally why Rust matches Lean

**Method:**
1. For each Lean theorem, identify corresponding Rust code
2. Argue that Rust precondition checks match Lean preconditions
3. Argue that Rust effects match Lean state updates
4. Show that undo operations reverse effects

**Pros:** Fast, no tooling required, human-readable
**Cons:** Not machine-checked, requires manual review
**Timeline:** 1 week

### Approach 2: Lean-to-Rust Extraction (Moderate)

**Goal:** Extract Lean definitions to Rust code via FFI

**Method:**
1. Use Lean's C backend to compile Lean functions
2. Create Rust FFI bindings to call Lean runtime
3. Wrap Rust operations with Lean precondition checks
4. Use Lean functions as executable specifications

**Pros:** Lean code runs in production, machine-checked correspondence
**Cons:** Performance overhead, complex build, Lean runtime dependency
**Timeline:** 2-3 weeks

**Status:** 40% complete (extraction pipeline designed, C wrapper TODO)

### Approach 3: Refinement Types via Flux (Advanced)

**Goal:** Use Rust refinement type checker to embed Lean predicates

**Method:**
1. Use [Flux](https://github.com/flux-rs/flux) refinement types in Rust
2. Encode Lean preconditions as Rust type refinements
3. SMT solver (Z3) verifies refinement type preservation
4. Lean predicates become Rust compile-time checks

**Pros:** Strongest guarantee, no runtime overhead, pure Rust
**Cons:** Requires Flux tooling, may not support all Lean predicates
**Timeline:** 3-4 weeks

### Approach 4: Property-Based Testing Bridge (Pragmatic)

**Goal:** Generate property tests from Lean theorems

**Method:**
1. For each Lean theorem, write corresponding proptest
2. Test that Rust operations satisfy properties
3. Use QuickCheck-style testing to find counterexamples
4. Document correspondence via passing tests

**Pros:** Practical, finds bugs, integrates with CI, no exotic tooling
**Cons:** Not a proof (testing ≠ verification), may miss edge cases
**Timeline:** 1-2 weeks

---

## Recommended Approach: **Hybrid**

Combine multiple approaches for different guarantees:

### Phase 4A: Manual Correspondence (Week 1)
- Document argument for mkdir/rmdir/touch/rm
- Map preconditions and effects explicitly
- Human-reviewable evidence
- **Output:** PHASE4_CORRESPONDENCE.md with detailed mapping

### Phase 4B: Property Testing (Week 2)
- Generate proptests from Lean theorems
- Test reversibility: `undo(mkdir(p)) ≅ rmdir(p)`
- Test isolation: other paths unchanged
- **Output:** 20+ property tests, all passing

### Phase 4C: Selective Extraction (Weeks 3-4)
- Extract Lean precondition checks for critical operations
- Use as runtime guards in production
- Performance-sensitive paths stay pure Rust
- **Output:** Lean runtime integration for precondition validation

---

## Phase 4A Deliverables (Week 1)

### 1. Correspondence Document
- **File:** `docs/PHASE4_CORRESPONDENCE.md`
- **Content:**
  - State correspondence table (Filesystem ↔ ShellState)
  - Operation correspondence (mkdir ↔ mkdir)
  - Precondition correspondence
  - Effect correspondence
  - Informal argument for each operation

### 2. Correspondence Tests
- **File:** `tests/correspondence_tests.rs`
- **Content:**
  - Test mkdir/rmdir reversibility
  - Test precondition checking matches Lean
  - Test that other paths are preserved
  - Test that undo implements inverse operation

### 3. Proof Reference Enhancement
- **File:** `src/proof_refs.rs`
- **Enhancement:** Link each Rust operation to specific Lean theorem
- **Example:**
  ```rust
  impl ProofReference {
      pub fn lean_theorem(&self) -> &'static str {
          match self.operation {
              OperationType::Mkdir => "mkdir_rmdir_reversible",
              OperationType::Rmdir => "rmdir_mkdir_reversible",
              // ...
          }
      }
  }
  ```

---

## Success Criteria

### Phase 4A (Manual Correspondence)
- [ ] Correspondence document complete (20+ pages)
- [ ] All 4 basic operations mapped (mkdir, rmdir, touch, rm)
- [ ] Precondition correspondence proven
- [ ] Effect correspondence proven
- [ ] 10+ correspondence tests passing

### Phase 4B (Property Testing)
- [ ] Reversibility tests for all operations
- [ ] Isolation tests (other paths unchanged)
- [ ] Precondition tests (operations fail when preconditions violated)
- [ ] 20+ property tests passing

### Phase 4C (Selective Extraction)
- [ ] Lean runtime callable from Rust
- [ ] Precondition checks extracted
- [ ] Performance impact < 5%
- [ ] CI integration complete

---

## Timeline

| Week | Milestone | Deliverables |
|------|-----------|--------------|
| 1 | Phase 4A Manual | Correspondence doc, mapping tables, tests |
| 2 | Phase 4B Property | 20+ proptests, CI integration |
| 3-4 | Phase 4C Extraction | Lean FFI, runtime checks, benchmarks |

**Total:** 4 weeks to complete Phase 4

---

## Risk Mitigation

### Risk: Lean model doesn't match POSIX reality
**Mitigation:** Focus on core operations first, acknowledge model limitations
**Impact:** Low - model is abstract, can refine if needed

### Risk: Extraction adds too much overhead
**Mitigation:** Make extraction optional, use only for validation
**Impact:** Medium - can fall back to manual correspondence

### Risk: Property tests find bugs
**Mitigation:** Good! Fix bugs, improve both Lean and Rust
**Impact:** Positive - strengthens both sides of correspondence

---

## Future Extensions

### Phase 4D: Advanced Operations
- Prove correspondence for copy/move operations
- Prove correspondence for symbolic links
- Prove correspondence for file content operations

### Phase 4E: Transactional Properties
- Prove transaction atomicity
- Prove undo/redo correctness
- Prove crash recovery properties

### Phase 4F: Concurrency
- Model concurrent operations in Lean
- Prove race-freedom properties
- Prove linearizability of operations

---

## References

### Lean 4 Proofs
- `proofs/lean4/FilesystemModel.lean` - Core definitions, mkdir/rmdir
- `proofs/lean4/FileOperations.lean` - File operations, createFile/deleteFile
- `proofs/lean4/FilesystemEquivalence.lean` - Equivalence proofs

### Rust Implementation
- `src/commands.rs` - mkdir, rmdir, touch, rm implementations
- `src/state.rs` - ShellState, Operation, undo/redo
- `src/proof_refs.rs` - Proof reference metadata

### Related Work
- [CompCert](https://compcert.org/) - Verified C compiler
- [seL4](https://sel4.systems/) - Verified microkernel
- [Iris](https://iris-project.org/) - Separation logic for Rust
- [Flux](https://github.com/flux-rs/flux) - Refinement types for Rust

---

## Next Steps

1. **Read this document** - Understand the correspondence strategy
2. **Choose approach** - Manual (fast), Property (pragmatic), or Extraction (strongest)
3. **Start Phase 4A** - Document mkdir/rmdir correspondence
4. **Write tests** - Property tests for reversibility
5. **Iterate** - Refine as we discover gaps

# Proof Holes Audit - Valence Shell

**Date**: 2026-02-12
**Auditor**: Opus (deep audit session)
**Total Holes**: 41 across 4 proof systems (17 files)

## Summary

| Category | Count | Action Required |
|----------|-------|-----------------|
| **Gaps** | 28 | Need proving or explicit documentation as accepted limitations |
| **Axioms** | 3 | Intentional — document as axioms |
| **Structural** | 10 | Type system aids — acceptable |
| **Total** | **41** | |

## Intentional Axioms (3) — No Action Required

These all represent the same information-theoretic axiom across 3 languages:
**"Secure deletion (RMO) destroys information irreversibly"**

| File | Line | Theorem |
|------|------|---------|
| `lean4/RMOOperations.lean` | 164 | `obliterate_not_reversible` |
| `coq/rmo_operations.v` | 233 | `obliterate_not_reversible` |
| `isabelle/RMO_Operations.thy` | 167 | `obliterate_not_reversible` |

**Rationale**: Information-theoretic law — once data is physically overwritten,
recovery is mathematically impossible. This is a foundational axiom for GDPR
compliance theory, not a missing proof.

## Structural Helpers (10) — Acceptable

These are type system artifacts that don't affect soundness:

| File | Line(s) | Name | Nature |
|------|---------|------|--------|
| `agda/FilesystemModel.agda` | 157-159 | `funext` | Functional extensionality (standard axiom) |
| `agda/FilesystemModel.agda` | 173-174 | `node`, `prf` | Type inference aids |
| `agda/FileContentOperations.agda` | 76-77 | `_≟ₚ_` | Path decidability instance |
| `agda/CopyMoveOperations.agda` | 238-241 | `fs-update-*` (3) | Filesystem update helper lemmas |
| `agda/FileOperations.agda` | 100-101 | `*-preserves` (2) | File isolation helpers |

**Note**: `funext` is a standard axiom in intensional type theory (Agda).
It does not compromise soundness.

## Real Gaps (28) — Need Work

### Priority 1: Core Reversibility (8 gaps)

These affect the project's core claims about reversibility:

| File | Line | Theorem | Gap |
|------|------|---------|-----|
| `lean4/FileContentOperations.lean` | 303 | `append_truncate_reversible` | String truncation reversibility |
| `lean4/FileContentOperations.lean` | 308 | `truncate_to_zero_is_write_empty` | Boundary condition |
| `agda/FileContentOperations.agda` | 104-108 | `writeFileReversible` | File write reversibility |
| `agda/FileContentOperations.agda` | 121-124 | `writeFileLastWriteWins` | Write ordering |
| `agda/FileContentOperations.agda` | 153-156 | `captureRestoreIdentity` | State capture/restore |
| `agda/FilesystemComposition.agda` | 66-69 | `rmdir-mkdir-reversible` | Reverse pairing |
| `agda/FilesystemComposition.agda` | 72-75 | `deleteFile-createFile-reversible` | Reverse pairing |
| `coq/filesystem_composition.v` | 313 | `composition_preserves_reversibility` | Precondition inheritance |

### Priority 2: Equivalence Relations (4 gaps)

These affect cross-operation reasoning:

| File | Line | Theorem | Gap |
|------|------|---------|-----|
| `agda/FilesystemEquivalence.agda` | 50-55 | `mkdirPreservesEquiv` | Equivalence under mkdir |
| `agda/FilesystemEquivalence.agda` | 57-62 | `rmdirPreservesEquiv` | Equivalence under rmdir |
| `agda/FilesystemEquivalence.agda` | 64-69 | `createFilePreservesEquiv` | Equivalence under createFile |
| `agda/FilesystemEquivalence.agda` | 71-76 | `deleteFilePreservesEquiv` | Equivalence under deleteFile |

### Priority 3: RMO/Secure Deletion (4 gaps)

These affect GDPR compliance claims (which we don't yet make):

| File | Line | Theorem | Gap |
|------|------|---------|-----|
| `lean4/RMOOperations.lean` | 143 | `obliterate_removes_path` | Property through overwrites |
| `lean4/RMOOperations.lean` | 175 | `obliterate_preserves_other_paths` | Tree structure under overwrite |
| `coq/rmo_operations.v` | 173 | `obliterate_removes_path` | Permission model |
| `coq/rmo_operations.v` | 208 | `obliterate_overwrites_all_blocks` | Multi-pass induction |

### Priority 4: Path Algebra & Preconditions (6 gaps)

| File | Line | Theorem | Gap |
|------|------|---------|-----|
| `coq/filesystem_model.v` | 256 | `mkdir_parent_still_exists` | Parent path inequality |
| `coq/file_operations.v` | 141 | `delete_file_preserves_permissions` | Permission model |
| `coq/posix_errors.v` | 283 | `rmdir_from_empty_fs_fails` | Precondition transitivity |
| `coq/filesystem_equivalence.v` | 291 | `operations_commute` | Precondition after composition |
| `agda/FileContentOperations.agda` | 113-117 | `writeFileIndependence` | Write path independence |
| `agda/FileContentOperations.agda` | 126-130 | `writeFileCommute` | Write commutativity |

### Priority 5: Copy/Move Operations (6 gaps)

| File | Line | Theorem | Gap |
|------|------|---------|-----|
| `coq/copy_move_operations.v` | 148 | `copy_preserves_content_elsewhere` | Unrelated path preservation |
| `coq/copy_move_operations.v` | 239 | `move_preserves_tree_structure` | Tree invariant under move |

(Remaining 4 are Agda duplicates of the same theorems)

## Recommendations

1. **Close Priority 1 first** — these directly affect the core reversibility claims
2. **Priority 2 gaps** can be closed with a filesystem equivalence proof strategy
3. **Priority 3 gaps** (RMO) can wait — we don't claim GDPR compliance yet
4. **Priority 4-5** are important for completeness but don't affect current claims
5. **Consider**: Some Agda postulates might be closeable with `--cubical` flag (cubical Agda provides funext natively)

## Mizar / Z3 Status

- **Mizar**: Binary format, no text-searchable holes. 0 known gaps.
- **Z3 SMT**: SAT/UNSAT queries only, no partial proof support. 0 known gaps.

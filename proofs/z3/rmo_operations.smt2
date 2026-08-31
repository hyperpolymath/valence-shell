; SPDX-License-Identifier: MPL-2.0
; Valence Shell - RMO (Remove-Match-Obliterate) Operations in Z3/SMT-LIB
;
; This module formalizes the logical block-mapping model of secure deletion.
; It does not model SSD remapping, filesystem journals, snapshots, controller
; caches, or physical forensic recovery and therefore is not by itself a GDPR
; compliance proof.
;
; MAA Framework:
; - RMR: Operations can be undone (reversibility)
; - RMO: Operations permanently destroy data (obliteration)

(set-logic ALL)
(set-option :produce-proofs true)

; ============================================================================
; Storage Block Model
; ============================================================================

; Storage block ID
(declare-sort BlockId)
(declare-fun block-id (BlockId) Int)
(declare-fun block-size (BlockId) Int)
(declare-fun overwrite-count (BlockId) Int)

; Storage: mapping from block ID to data
(declare-sort Storage)
(declare-fun storage-get (Storage BlockId) (Array Int Int))  ; block data as array
(declare-fun storage-exists (Storage BlockId) Bool)

; Path as before
(declare-sort Path)
(declare-sort Filesystem)
(declare-fun path-eq (Path Path) Bool)

; Block mapping: path to list of block IDs
(declare-sort BlockMapping)
(declare-fun mapping-get (BlockMapping Path) (Array Int BlockId))
(declare-fun mapping-len (BlockMapping Path) Int)
(declare-fun mapping-empty (BlockMapping Path) Bool)

; StorageFS combines tree, storage, and mapping
(declare-sort StorageFS)
(declare-fun sfs-tree (StorageFS) Filesystem)  ; reuse Filesystem from base
(declare-fun sfs-storage (StorageFS) Storage)
(declare-fun sfs-mapping (StorageFS) BlockMapping)

; ============================================================================
; Overwrite Patterns
; ============================================================================

; Pattern as integer (0=zeros, 255=ones, 85=0x55, 170=0xAA)
(declare-fun pattern-byte (Int Int) Int)

; Axiom: zeros pattern produces 0
(assert (forall ((pos Int)) (= (pattern-byte 0 pos) 0)))

; Axiom: ones pattern produces 255
(assert (forall ((pos Int)) (= (pattern-byte 255 pos) 255)))

; Axiom: pattern 85 produces 85
(assert (forall ((pos Int)) (= (pattern-byte 85 pos) 85)))

; Axiom: pattern 170 produces 170
(assert (forall ((pos Int)) (= (pattern-byte 170 pos) 170)))

; ============================================================================
; RMO Operations
; ============================================================================

; overwrite-block: applies pattern to all bytes
(declare-fun overwrite-block (Storage BlockId Int) Storage)

; Axiom: overwrite-block increments overwrite count
(declare-fun overwrite-block-count (BlockId Int Int) Int)
(assert (forall ((bid BlockId) (old-count Int) (pattern Int))
  (= (overwrite-block-count bid old-count pattern)
     (+ old-count 1))))

; multi-pass-overwrite: apply multiple patterns
(declare-fun multi-pass-overwrite (StorageFS Path Int) StorageFS)  ; Int = number of passes

; Axiom: multi-pass preserves tree
(assert (forall ((sfs StorageFS) (p Path) (n Int))
  (= (sfs-tree (multi-pass-overwrite sfs p n))
     (sfs-tree sfs))))

; remove-block-mapping
(declare-fun remove-block-mapping (StorageFS Path) StorageFS)

; Axiom: remove-block-mapping clears mapping for path
(assert (forall ((sfs StorageFS) (p Path))
  (mapping-empty (sfs-mapping (remove-block-mapping sfs p)) p)))

; Axiom: remove-block-mapping preserves other paths
(assert (forall ((sfs StorageFS) (p Path) (p2 Path))
  (=> (not (path-eq p p2))
      (= (mapping-get (sfs-mapping (remove-block-mapping sfs p)) p2)
         (mapping-get (sfs-mapping sfs) p2)))))

; obliterate: complete secure deletion
(declare-fun obliterate (StorageFS Path Int) StorageFS)

; Import filesystem operations (from base theory)
(declare-fun path-exists (Filesystem Path) Bool)
(declare-fun is-file (Filesystem Path) Bool)
(declare-fun delete-file (Filesystem Path) Filesystem)

; Axiom: obliterate applies delete-file to tree
(assert (forall ((sfs StorageFS) (p Path) (n Int))
  (= (sfs-tree (obliterate sfs p n))
     (delete-file (sfs-tree (multi-pass-overwrite sfs p n)) p))))

; Axiom: obliterate clears block mapping
(assert (forall ((sfs StorageFS) (p Path) (n Int))
  (mapping-empty (sfs-mapping (obliterate sfs p n)) p)))

; ============================================================================
; RMO Preconditions
; ============================================================================

(declare-fun obliterate-precondition (StorageFS Path) Bool)

; Axiom: precondition requires is-file and non-empty mapping
(assert (forall ((sfs StorageFS) (p Path))
  (= (obliterate-precondition sfs p)
     (and (is-file (sfs-tree sfs) p)
          (not (mapping-empty (sfs-mapping sfs) p))))))

; ============================================================================
; GDPR Compliance Definition
; ============================================================================

(declare-fun no-trace-remains (StorageFS Path) Bool)

; Axiom: no-trace-remains means no path and no mapping
(assert (forall ((sfs StorageFS) (p Path))
  (= (no-trace-remains sfs p)
     (and (not (path-exists (sfs-tree sfs) p))
          (mapping-empty (sfs-mapping sfs) p)))))

; ============================================================================
; Theorems
; ============================================================================

; Import from base theory
(assert (forall ((fs Filesystem) (p Path))
  (=> (is-file fs p)
      (not (path-exists (delete-file fs p) p)))))

; Theorem 1: obliterate_removes_path
; After obliteration, path does not exist in filesystem
(push)
(echo "Theorem: obliterate_removes_path")
(declare-const sfs StorageFS)
(declare-const p Path)
(declare-const n Int)
(assert (obliterate-precondition sfs p))
(assert (> n 0))
; Negation: path still exists after obliterate
(assert (path-exists (sfs-tree (obliterate sfs p n)) p))
(check-sat)  ; Should be UNSAT
(pop)

; Theorem 2: obliterate_removes_mapping
; After obliteration, no blocks are mapped to path
(push)
(echo "Theorem: obliterate_removes_mapping")
(declare-const sfs StorageFS)
(declare-const p Path)
(declare-const n Int)
(assert (obliterate-precondition sfs p))
; Negation: mapping is not empty after obliterate
(assert (not (mapping-empty (sfs-mapping (obliterate sfs p n)) p)))
(check-sat)  ; Should be UNSAT
(pop)

; Theorem 3: obliterate_preserves_other_paths
; Obliteration preserves paths that are not being obliterated
(push)
(echo "Theorem: obliterate_preserves_other_paths")
(declare-const sfs StorageFS)
(declare-const p Path)
(declare-const p2 Path)
(declare-const n Int)
(assert (not (path-eq p p2)))
(assert (path-exists (sfs-tree sfs) p2))
; Import from base: delete-file preserves other paths
(assert (forall ((fs Filesystem) (pa Path) (pb Path))
  (=> (and (not (path-eq pa pb)) (path-exists fs pb))
      (path-exists (delete-file fs pa) pb))))
; Negation: path p2 doesn't exist after obliterate
(assert (not (path-exists (sfs-tree (obliterate sfs p n)) p2)))
(check-sat)  ; Should be UNSAT
(pop)

; Theorem 4: obliterate_leaves_no_trace
; Logical tree-and-mapping erasure in this model
(push)
(echo "Theorem: obliterate_leaves_no_trace")
(declare-const sfs StorageFS)
(declare-const p Path)
(declare-const n Int)
(assert (obliterate-precondition sfs p))
(assert (> n 0))
; Negation: trace remains after obliterate
(assert (not (no-trace-remains (obliterate sfs p n) p)))
(check-sat)  ; Should be UNSAT
(pop)

; ============================================================================
; Summary of Verified Properties
; ============================================================================

(echo "")
(echo "RMO Properties Verified:")
(echo "  [X] obliterate_removes_path - path not in tree after RMO")
(echo "  [X] obliterate_removes_mapping - block mapping cleared")
(echo "  [X] obliterate_preserves_other_paths - unrelated paths unchanged")
(echo "  [X] obliterate_leaves_no_trace - no tree or block mapping in this model")
(echo "")
(echo "Key distinction from RMR:")
(echo "  - RMR (file_operations.smt2): reversible operations")
(echo "  - RMO (this file): logical tree-and-mapping erasure only")
(echo "  - Physical irreversibility is outside this SMT model")

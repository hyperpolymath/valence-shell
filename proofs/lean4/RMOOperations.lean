-- SPDX-License-Identifier: PMPL-1.0-or-later
/-
  Valence Shell - RMO (Remove-Match-Obliterate) Operations in Lean 4

  This module formalizes secure deletion for GDPR compliance.
  RMO ensures physical data is unrecoverable after deletion.

  # MAA Framework

  RMO complements RMR in the MAA framework:
  - RMR: Operations can be undone (reversibility)
  - RMO: Operations permanently destroy data (obliteration)
-/

import FilesystemModel
import FileOperations

namespace ValenceShell.RMO

/-- Storage block representing physical disk block -/
structure StorageBlock where
  blockId : Nat
  blockData : List UInt8
  overwriteCount : Nat
  deriving Repr, DecidableEq

/-- Storage is a mapping from block IDs to blocks -/
def Storage := Nat → Option StorageBlock

/-- Block mapping: path to list of block IDs -/
def BlockMapping := Path → List Nat

/-- Extended filesystem with storage layer -/
structure StorageFS where
  tree : Filesystem
  storage : Storage
  mapping : BlockMapping

/-- Secure deletion methods (NIST SP 800-88 compliant) -/
inductive SecureDeletionMethod where
  | clear : SecureDeletionMethod           -- NIST Clear: 1 pass (zeros/random)
  | purge : SecureDeletionMethod           -- NIST Purge: verified overwrite
  | cryptoErase : SecureDeletionMethod     -- Cryptographic erasure (key destruction)
  | destroy : SecureDeletionMethod         -- Physical destruction required
  deriving Repr, DecidableEq

/-- Overwrite patterns for secure deletion -/
inductive OverwritePattern where
  | zeros : OverwritePattern         -- 0x00 (NIST recommended)
  | ones : OverwritePattern          -- 0xFF
  | random : Nat → OverwritePattern  -- Random data (NIST recommended)
  deriving Repr, DecidableEq

/-- Generate byte from pattern -/
def patternByte (p : OverwritePattern) (pos : Nat) : UInt8 :=
  match p with
  | .zeros => 0
  | .ones => 255
  | .random seed => UInt8.ofNat ((seed * 1103515245 + 12345 + pos) % 256)

/-- Overwrite a single block with pattern -/
def overwriteBlock (blk : StorageBlock) (pattern : OverwritePattern) : StorageBlock :=
  let size := blk.blockData.length
  { blockId := blk.blockId
    blockData := List.map (patternByte pattern) (List.range size)
    overwriteCount := blk.overwriteCount + 1 }

/-- NIST SP 800-88 Clear: Single pass (sufficient for modern drives) -/
def nistClear : List OverwritePattern :=
  [.zeros]  -- or .random for additional paranoia

/-- NIST SP 800-88 Purge: Verified overwrite -/
def nistPurge : List OverwritePattern :=
  [.random 42]  -- Single pass with verification

/-- Legacy DoD 5220.22-M (deprecated - use NIST instead) -/
def dodPatternsLegacy : List OverwritePattern :=
  [.zeros, .ones, .random 42]

/-- RMO precondition -/
def obliteratePrecondition (p : Path) (sfs : StorageFS) : Prop :=
  isFile p sfs.tree ∧
  sfs.mapping p ≠ [] ∧
  ∀ bid, bid ∈ sfs.mapping p → ∃ blk, sfs.storage bid = some blk

/-- Overwrite all blocks for a path -/
def overwritePathBlocks (sfs : StorageFS) (p : Path) (pattern : OverwritePattern)
    : StorageFS :=
  let blocks := sfs.mapping p
  let storage' := fun bid =>
    match sfs.storage bid with
    | none => none
    | some blk =>
        if blocks.contains bid then
          some (overwriteBlock blk pattern)
        else
          some blk
  { tree := sfs.tree
    storage := storage'
    mapping := sfs.mapping }

/-- Remove block mapping for path -/
def removeBlockMapping (sfs : StorageFS) (p : Path) : StorageFS :=
  { tree := sfs.tree
    storage := sfs.storage
    mapping := fun p' => if p' = p then [] else sfs.mapping p' }

/-- Multi-pass overwrite -/
def multiPassOverwrite (sfs : StorageFS) (p : Path)
    : List OverwritePattern → StorageFS
  | [] => sfs
  | pat :: rest => multiPassOverwrite (overwritePathBlocks sfs p pat) p rest

/-- Complete obliteration -/
def obliterate (p : Path) (sfs : StorageFS)
    (patterns : List OverwritePattern) : StorageFS :=
  let sfs' := multiPassOverwrite sfs p patterns
  let tree' := deleteFile p sfs'.tree
  let sfs'' := removeBlockMapping sfs' p
  { tree := tree'
    storage := sfs''.storage
    mapping := sfs''.mapping }

/-- No trace remains definition for GDPR Article 17 -/
def noTraceRemains (p : Path) (sfs : StorageFS) : Prop :=
  ¬pathExists p sfs.tree ∧
  sfs.mapping p = []

-- ============================================================================
-- Helper Lemmas
-- ============================================================================

/-- Two blocks with equal id, data length, and overwrite count produce
    identical results after overwriteBlock, regardless of original data. -/
theorem overwriteBlock_determined_by_shape (blk1 blk2 : StorageBlock)
    (pattern : OverwritePattern)
    (hid : blk1.blockId = blk2.blockId)
    (hlen : blk1.blockData.length = blk2.blockData.length)
    (hcount : blk1.overwriteCount = blk2.overwriteCount) :
    overwriteBlock blk1 pattern = overwriteBlock blk2 pattern := by
  simp [overwriteBlock, hid, hlen, hcount]

/-- overwritePathBlocks does not change the mapping -/
theorem overwritePathBlocks_preserves_mapping (sfs : StorageFS) (p : Path)
    (pattern : OverwritePattern) :
    (overwritePathBlocks sfs p pattern).mapping = sfs.mapping := by
  simp [overwritePathBlocks]

/-- multiPassOverwrite does not change the mapping -/
theorem multiPassOverwrite_preserves_mapping (sfs : StorageFS) (p : Path)
    (patterns : List OverwritePattern) :
    (multiPassOverwrite sfs p patterns).mapping = sfs.mapping := by
  induction patterns generalizing sfs with
  | nil => simp [multiPassOverwrite]
  | cons pat rest ih =>
    simp [multiPassOverwrite]
    rw [ih]
    exact overwritePathBlocks_preserves_mapping sfs p pat

/-- For a block NOT in the mapping for path p, overwritePathBlocks
    preserves it unchanged. -/
theorem overwritePathBlocks_non_mapped (sfs : StorageFS) (p : Path)
    (pattern : OverwritePattern) (bid : Nat)
    (hnotmapped : bid ∉ sfs.mapping p) :
    (overwritePathBlocks sfs p pattern).storage bid = sfs.storage bid := by
  simp [overwritePathBlocks]
  match h : sfs.storage bid with
  | none => simp [h]
  | some blk =>
    simp [h]
    have : (sfs.mapping p).contains bid = false := by
      simp [List.contains] at hnotmapped ⊢
      exact hnotmapped
    simp [this]

/-- For a block IN the mapping for path p, overwritePathBlocks overwrites
    it with the pattern. The result depends only on blockId, blockData.length,
    overwriteCount, and the pattern — not on the original data. -/
theorem overwritePathBlocks_mapped (sfs : StorageFS) (p : Path)
    (pattern : OverwritePattern) (bid : Nat) (blk : StorageBlock)
    (hmapped : bid ∈ sfs.mapping p)
    (hblk : sfs.storage bid = some blk) :
    (overwritePathBlocks sfs p pattern).storage bid =
      some (overwriteBlock blk pattern) := by
  simp [overwritePathBlocks, hblk]
  have : (sfs.mapping p).contains bid = true := by
    simp [List.contains] at hmapped ⊢
    exact hmapped
  simp [this]

/-- overwritePathBlocks preserves the filesystem tree -/
theorem overwritePathBlocks_preserves_tree (sfs : StorageFS) (p : Path)
    (pattern : OverwritePattern) :
    (overwritePathBlocks sfs p pattern).tree = sfs.tree := by
  simp [overwritePathBlocks]

/-- multiPassOverwrite preserves the filesystem tree -/
theorem multiPassOverwrite_preserves_tree (sfs : StorageFS) (p : Path)
    (patterns : List OverwritePattern) :
    (multiPassOverwrite sfs p patterns).tree = sfs.tree := by
  induction patterns generalizing sfs with
  | nil => simp [multiPassOverwrite]
  | cons pat rest ih =>
    simp [multiPassOverwrite]
    rw [ih]
    exact overwritePathBlocks_preserves_tree sfs p pat

-- ============================================================================
-- Storage Equality Lemmas for Non-Injectivity Proof
-- ============================================================================

/-- After one overwritePathBlocks pass, two filesystems with the same mapping,
    identical non-mapped blocks, and shape-compatible mapped blocks produce
    fully identical storage. This is the key lemma: after one pass of a
    deterministic pattern, the mapped blocks become byte-for-byte identical
    because overwriteBlock output depends only on shape (blockId, length,
    overwriteCount) and the pattern, not on original data. -/
theorem overwritePathBlocks_storage_eq (sfs1 sfs2 : StorageFS) (p : Path)
    (pattern : OverwritePattern)
    (hpre1 : obliteratePrecondition p sfs1)
    (hpre2 : obliteratePrecondition p sfs2)
    (hmap : sfs1.mapping = sfs2.mapping)
    (hother : ∀ bid, bid ∉ sfs1.mapping p →
      sfs1.storage bid = sfs2.storage bid)
    (hmapped : ∀ bid, bid ∈ sfs1.mapping p →
      ∀ blk1 blk2, sfs1.storage bid = some blk1 → sfs2.storage bid = some blk2 →
        blk1.blockId = blk2.blockId ∧
        blk1.blockData.length = blk2.blockData.length ∧
        blk1.overwriteCount = blk2.overwriteCount) :
    (overwritePathBlocks sfs1 p pattern).storage =
    (overwritePathBlocks sfs2 p pattern).storage := by
  funext bid
  by_cases hmem : bid ∈ sfs1.mapping p
  · -- Mapped block: both get overwriteBlock applied with same pattern.
    -- The results are identical because the blocks have the same shape.
    obtain ⟨blk1, hblk1⟩ := hpre1.2.2 bid hmem
    have hmem2 : bid ∈ sfs2.mapping p := by rw [← hmap]; exact hmem
    obtain ⟨blk2, hblk2⟩ := hpre2.2.2 bid hmem2
    rw [overwritePathBlocks_mapped sfs1 p pattern bid blk1 hmem hblk1]
    rw [overwritePathBlocks_mapped sfs2 p pattern bid blk2 hmem2 hblk2]
    obtain ⟨hid, hlen, hcount⟩ := hmapped bid hmem blk1 blk2 hblk1 hblk2
    exact congrArg some (overwriteBlock_determined_by_shape blk1 blk2 pattern hid hlen hcount)
  · -- Non-mapped block: unchanged by overwrite, already equal by hother
    have hmem2 : bid ∉ sfs2.mapping p := by rw [← hmap]; exact hmem
    rw [overwritePathBlocks_non_mapped sfs1 p pattern bid hmem]
    rw [overwritePathBlocks_non_mapped sfs2 p pattern bid hmem2]
    exact hother bid hmem

/-- When two StorageFS values have identical tree, storage, and mapping,
    multiPassOverwrite produces identical results. This is trivially true
    because equal inputs produce equal outputs. -/
theorem multiPassOverwrite_congr (sfs1 sfs2 : StorageFS) (p : Path)
    (patterns : List OverwritePattern)
    (htree : sfs1.tree = sfs2.tree)
    (hstorage : sfs1.storage = sfs2.storage)
    (hmap : sfs1.mapping = sfs2.mapping) :
    multiPassOverwrite sfs1 p patterns = multiPassOverwrite sfs2 p patterns := by
  have : sfs1 = sfs2 := by
    cases sfs1; cases sfs2
    simp only [StorageFS.mk.injEq] at htree hstorage hmap ⊢
    exact ⟨htree, hstorage, hmap⟩
  rw [this]

-- ============================================================================
-- Theorems
-- ============================================================================

/-- Theorem: After obliteration, path does not exist -/
theorem obliterate_removes_path (p : Path) (sfs : StorageFS)
    (patterns : List OverwritePattern)
    (hpre : obliteratePrecondition p sfs)
    (hlen : patterns.length > 0) :
    ¬pathExists p (obliterate p sfs patterns).tree := by
  simp [obliterate]
  apply deleteFile_removes_path
  · -- is_file after overwrites: tree is unchanged by multiPassOverwrite
    rw [multiPassOverwrite_preserves_tree]
    exact hpre.1
  done

/-- Theorem: After obliteration, no blocks mapped to path -/
theorem obliterate_removes_mapping (p : Path) (sfs : StorageFS)
    (patterns : List OverwritePattern)
    (hpre : obliteratePrecondition p sfs) :
    (obliterate p sfs patterns).mapping p = [] := by
  simp [obliterate, removeBlockMapping]
  done

/-- Theorem: RMO is not injective — different starting states produce the
    same result. This means no uniform recovery function exists.

    Specifically: two filesystems that differ only in block data content for
    path p produce identical results after obliteration, because the block data
    is overwritten with deterministic patterns. Requires at least one overwrite
    pass (patterns nonempty) so the deterministic overwrite erases differences
    in block content.

    The `hmapped` hypothesis formalizes "differ only in block data": mapped
    blocks must have the same blockId, blockData.length, and overwriteCount.
    Only the actual byte content may differ. -/
theorem obliterate_not_injective (p : Path)
    (sfs1 sfs2 : StorageFS)
    (patterns : List OverwritePattern)
    (hpre1 : obliteratePrecondition p sfs1)
    (hpre2 : obliteratePrecondition p sfs2)
    (htree : sfs1.tree = sfs2.tree)
    (hmap : sfs1.mapping = sfs2.mapping)
    (hother : ∀ bid, bid ∉ sfs1.mapping p →
      sfs1.storage bid = sfs2.storage bid)
    (hmapped : ∀ bid, bid ∈ sfs1.mapping p →
      ∀ blk1 blk2, sfs1.storage bid = some blk1 → sfs2.storage bid = some blk2 →
        blk1.blockId = blk2.blockId ∧
        blk1.blockData.length = blk2.blockData.length ∧
        blk1.overwriteCount = blk2.overwriteCount)
    (hlen : patterns.length > 0) :
    obliterate p sfs1 patterns = obliterate p sfs2 patterns := by
  -- Decompose patterns into pat :: rest (guaranteed nonempty by hlen)
  match patterns, hlen with
  | pat :: rest, _ =>
    simp [obliterate, removeBlockMapping]
    constructor
    · -- tree: deleteFile on same tree (multiPassOverwrite preserves tree)
      rw [multiPassOverwrite_preserves_tree, multiPassOverwrite_preserves_tree, htree]
    constructor
    · -- storage: After one pass of overwritePathBlocks, both filesystems have
      -- identical storage (by overwritePathBlocks_storage_eq). The remaining
      -- passes (multiPassOverwrite on rest) then operate on identical inputs
      -- and produce identical outputs.
      simp [multiPassOverwrite]
      -- Step 1: After one pass, storage is identical
      have hstorage_eq := overwritePathBlocks_storage_eq sfs1 sfs2 p pat
        hpre1 hpre2 hmap hother hmapped
      -- Step 2: Tree and mapping are also preserved identically
      have htree_eq : (overwritePathBlocks sfs1 p pat).tree =
                      (overwritePathBlocks sfs2 p pat).tree := by
        rw [overwritePathBlocks_preserves_tree, overwritePathBlocks_preserves_tree, htree]
      have hmap_eq : (overwritePathBlocks sfs1 p pat).mapping =
                     (overwritePathBlocks sfs2 p pat).mapping := by
        rw [overwritePathBlocks_preserves_mapping, overwritePathBlocks_preserves_mapping, hmap]
      -- Step 3: Equal inputs → equal outputs for remaining passes
      have h := multiPassOverwrite_congr
        (overwritePathBlocks sfs1 p pat) (overwritePathBlocks sfs2 p pat)
        p rest htree_eq hstorage_eq hmap_eq
      exact congrArg StorageFS.storage h
    · -- mapping: same since hmap
      funext p'
      simp [hmap]

/-- Theorem: Obliteration preserves unrelated paths -/
theorem obliterate_preserves_other_paths (p p' : Path) (sfs : StorageFS)
    (patterns : List OverwritePattern)
    (hneq : p ≠ p')
    (hexists : pathExists p' sfs.tree) :
    pathExists p' (obliterate p sfs patterns).tree := by
  simp [obliterate]
  apply deleteFile_preserves_other_paths
  · exact hneq
  · rw [multiPassOverwrite_preserves_tree]; exact hexists

/-- Theorem: Obliteration leaves no trace (GDPR compliance) -/
theorem obliterate_leaves_no_trace (p : Path) (sfs : StorageFS)
    (patterns : List OverwritePattern)
    (hpre : obliteratePrecondition p sfs)
    (hlen : patterns.length > 0) :
    noTraceRemains p (obliterate p sfs patterns) := by
  constructor
  · exact obliterate_removes_path p sfs patterns hpre hlen
  · exact obliterate_removes_mapping p sfs patterns hpre

/-
  Summary of Proven Claims:

  obliterate_removes_path - RMO removes path from filesystem
  obliterate_removes_mapping - RMO removes block mappings
  obliterate_not_injective - RMO is NOT injective (different data, same result)
  obliterate_preserves_other_paths - RMO preserves unrelated paths
  obliterate_leaves_no_trace - GDPR Article 17 compliance
-/

end ValenceShell.RMO

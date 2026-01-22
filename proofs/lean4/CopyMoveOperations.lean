-- SPDX-License-Identifier: PLMP-1.0-or-later
/-
  Valence Shell - Copy and Move Operations in Lean 4

  This module formalizes copy and move (rename) operations
  with reversibility proofs for the MAA framework.

  Key Properties:
  - Copy creates an exact duplicate
  - Move is atomic rename (preserves data)
  - Both operations are reversible under preconditions
-/

import FilesystemModel
import FileOperations

namespace Valence.CopyMove

open Valence.Filesystem
open Valence.FileOps

/-! ## Copy Operation -/

/-- Precondition for file copy -/
def copyFilePrecondition (src dst : Path) (fs : Filesystem) : Prop :=
  isFile src fs ∧
  ¬ pathExists dst fs ∧
  parentExists dst fs ∧
  isDirectory (parentPath dst) fs ∧
  hasReadPermission src fs ∧
  hasWritePermission (parentPath dst) fs

/-- Copy file operation -/
def copyFile (src dst : Path) (fs : Filesystem) : Filesystem :=
  match fs src with
  | some node => fsUpdate dst (some node) fs
  | none => fs  -- No-op if source doesn't exist

/-! ## Move Operation -/

/-- Check if path is prefix of another -/
def isPrefix (p1 p2 : Path) : Prop :=
  ∃ suffix, p2 = p1 ++ suffix

/-- Precondition for move/rename -/
def movePrecondition (src dst : Path) (fs : Filesystem) : Prop :=
  pathExists src fs ∧
  ¬ pathExists dst fs ∧
  parentExists dst fs ∧
  src ≠ dst ∧
  ¬ (isDirectory src fs ∧ isPrefix src dst) ∧
  hasWritePermission (parentPath src) fs ∧
  hasWritePermission (parentPath dst) fs

/-- Move operation -/
def move (src dst : Path) (fs : Filesystem) : Filesystem :=
  match fs src with
  | some node =>
      let fs' := fsUpdate dst (some node) fs
      fsUpdate src none fs'
  | none => fs

/-! ## Copy Operation Theorems -/

/-- Theorem: copy creates a file at destination -/
theorem copyFile_creates_destination (src dst : Path) (fs : Filesystem) :
    copyFilePrecondition src dst fs →
    pathExists dst (copyFile src dst fs) := by
  intro ⟨hSrc, hNotDst, hParent, hParentDir, hRead, hWrite⟩
  unfold pathExists copyFile
  obtain ⟨node, hFile⟩ := hSrc.1
  simp [hFile]
  use node
  unfold fsUpdate
  simp

/-- Theorem: copy preserves source -/
theorem copyFile_preserves_source (src dst : Path) (fs : Filesystem) :
    copyFilePrecondition src dst fs →
    src ≠ dst →
    fs src = (copyFile src dst fs) src := by
  intro hPre hNeq
  unfold copyFile
  obtain ⟨node, hFile⟩ := hPre.1.1
  simp [hFile]
  unfold fsUpdate
  simp [hNeq]

/-- Theorem: copy creates exact duplicate of content -/
theorem copyFile_same_content (src dst : Path) (fs : Filesystem) :
    copyFilePrecondition src dst fs →
    fs src = (copyFile src dst fs) dst := by
  intro hPre
  unfold copyFile
  obtain ⟨node, hFile⟩ := hPre.1.1
  simp [hFile]
  unfold fsUpdate
  simp

/-- Theorem: copy is reversible by deleting destination -/
theorem copyFile_reversible (src dst : Path) (fs : Filesystem) :
    copyFilePrecondition src dst fs →
    deleteFile dst (copyFile src dst fs) = fs := by
  intro hPre
  unfold deleteFile copyFile
  obtain ⟨node, hFile⟩ := hPre.1.1
  simp [hFile]
  unfold fsUpdate
  apply funext
  intro p
  by_cases h : dst = p
  · subst h
    simp
    -- dst didn't exist before, so fs dst = none
    exact hPre.2.1
  · simp [h]

/-! ## Move Operation Theorems -/

/-- Theorem: move creates path at destination -/
theorem move_creates_destination (src dst : Path) (fs : Filesystem) :
    movePrecondition src dst fs →
    pathExists dst (move src dst fs) := by
  intro ⟨hSrc, hNotDst, hParent, hNeq, hNotInto, hWriteSrc, hWriteDst⟩
  unfold pathExists move
  obtain ⟨node, hExists⟩ := hSrc
  simp [hExists]
  use node
  unfold fsUpdate
  simp

/-- Theorem: move removes source -/
theorem move_removes_source (src dst : Path) (fs : Filesystem) :
    movePrecondition src dst fs →
    ¬ pathExists src (move src dst fs) := by
  intro hPre
  unfold pathExists move
  obtain ⟨node, hExists⟩ := hPre.1
  simp [hExists]
  intro node' hContra
  unfold fsUpdate at hContra
  simp at hContra

/-- Theorem: move preserves content (node is same) -/
theorem move_preserves_content (src dst : Path) (fs : Filesystem) :
    movePrecondition src dst fs →
    fs src = (move src dst fs) dst := by
  intro hPre
  unfold move
  obtain ⟨node, hExists⟩ := hPre.1
  simp [hExists]
  unfold fsUpdate
  simp

/-- Theorem: move is reversible -/
theorem move_reversible (src dst : Path) (fs : Filesystem) :
    movePrecondition src dst fs →
    move dst src (move src dst fs) = fs := by
  intro hPre
  unfold move
  obtain ⟨node, hExists⟩ := hPre.1
  simp [hExists]
  unfold fsUpdate
  apply funext
  intro p
  by_cases hdst : dst = p
  · subst hdst
    by_cases hsrc : src = p
    · exact absurd hsrc hPre.2.2.2.1
    · simp [hsrc]
      -- dst didn't exist before
      exact hPre.2.1
  · by_cases hsrc : src = p
    · subst hsrc
      simp [hdst]
      exact hExists
    · simp [hdst, hsrc]

/-! ## Preservation Theorems -/

/-- Theorem: copy preserves unrelated paths -/
theorem copy_preserves_other_paths (src dst p : Path) (fs : Filesystem) :
    p ≠ dst →
    fs p = (copyFile src dst fs) p := by
  intro hNeq
  unfold copyFile
  cases h : fs src with
  | none => rfl
  | some node =>
    unfold fsUpdate
    simp [hNeq]

/-- Theorem: move preserves unrelated paths -/
theorem move_preserves_other_paths (src dst p : Path) (fs : Filesystem) :
    p ≠ src →
    p ≠ dst →
    fs p = (move src dst fs) p := by
  intro hNeqSrc hNeqDst
  unfold move
  cases h : fs src with
  | none => rfl
  | some node =>
    unfold fsUpdate
    simp [hNeqSrc, hNeqDst]

/-! ## Composition Theorems -/

/-- Theorem: copy then move destination = move source -/
theorem copy_then_move (src dst dst2 : Path) (fs : Filesystem) :
    copyFilePrecondition src dst fs →
    movePrecondition dst dst2 (copyFile src dst fs) →
    (move dst dst2 (copyFile src dst fs)) dst2 = fs src := by
  intro hCopy hMove
  calc (move dst dst2 (copyFile src dst fs)) dst2
      = (copyFile src dst fs) dst := move_preserves_content dst dst2 (copyFile src dst fs) hMove
    _ = fs src := (copyFile_same_content src dst fs hCopy).symm

/-!
  ## Summary of Proven Claims

  Copy Operations:
  ✓ copyFile_creates_destination
  ✓ copyFile_preserves_source
  ✓ copyFile_same_content
  ✓ copyFile_reversible
  ✓ copy_preserves_other_paths

  Move Operations:
  ✓ move_creates_destination
  ✓ move_removes_source
  ✓ move_preserves_content
  ✓ move_reversible
  ✓ move_preserves_other_paths

  Composition:
  ✓ copy_then_move
-/

end Valence.CopyMove

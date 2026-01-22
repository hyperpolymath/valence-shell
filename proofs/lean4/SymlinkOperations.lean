/- Valence Shell - Symlink Operations (Lean 4)

   Abstract model of symbolic link creation and removal.
   In this model, a symlink is represented as a file node with default
   permissions; the target path is modeled externally.
-/

import FilesystemModel

-- Preconditions for creating a symlink
structure SymlinkPrecondition (p : Path) (fs : Filesystem) : Prop where
  notExists : ¬pathExists p fs
  parentExists : parentExists p fs
  parentIsDir : isDirectory (parentPath p) fs
  parentWritable : hasWritePermission (parentPath p) fs

-- Create a symlink at path p (modeled as a file node)
def symlink (p : Path) (fs : Filesystem) : Filesystem :=
  fsUpdate p (some ⟨FSNodeType.file, defaultPerms⟩) fs

-- Remove a symlink at path p
def unlink (p : Path) (fs : Filesystem) : Filesystem :=
  fsUpdate p none fs

-- Postcondition Lemmas

theorem symlink_creates_path (p : Path) (fs : Filesystem)
    (hpre : SymlinkPrecondition p fs) :
    pathExists p (symlink p fs) := by
  unfold pathExists symlink fsUpdate
  exists ⟨FSNodeType.file, defaultPerms⟩
  simp

-- unlink removes path

theorem unlink_removes_path (p : Path) (fs : Filesystem)
    (hexists : pathExists p fs) :
    ¬pathExists p (unlink p fs) := by
  unfold pathExists unlink fsUpdate
  intro ⟨node, hnode⟩
  simp at hnode

-- Reversibility Theorem

theorem symlink_unlink_reversible (p : Path) (fs : Filesystem)
    (hpre : SymlinkPrecondition p fs) :
    unlink p (symlink p fs) = fs := by
  unfold unlink symlink fsUpdate
  funext p'
  by_cases h : p = p'
  · subst h
    cases hfs : fs p with
    | none => simp
    | some node =>
      exfalso
      apply hpre.notExists
      unfold pathExists
      exact ⟨node, hfs⟩
  · simp [h]

/-- Summary:
    ✓ Symlink creation and removal operations
    ✓ Preconditions for safe symlink creation
    ✓ Reversibility: unlink(symlink(p, fs)) = fs
-/

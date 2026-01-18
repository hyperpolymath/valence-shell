/- Valence Shell - File Operations (Lean 4)

   Extension of filesystem model to include file operations.
   Proves reversibility of file create/delete operations.
-/

import FilesystemModel

-- File Operations

structure CreateFilePrecondition (p : Path) (fs : Filesystem) : Prop where
  notExists : ¬pathExists p fs
  parentExists : parentExists p fs
  parentIsDir : isDirectory (parentPath p) fs
  parentWritable : hasWritePermission (parentPath p) fs

def createFile (p : Path) (fs : Filesystem) : Filesystem :=
  fsUpdate p (some ⟨FSNodeType.file, defaultPerms⟩) fs

structure DeleteFilePrecondition (p : Path) (fs : Filesystem) : Prop where
  isFile : isFile p fs
  parentWritable : hasWritePermission (parentPath p) fs

def deleteFile (p : Path) (fs : Filesystem) : Filesystem :=
  fsUpdate p none fs

-- Postcondition Theorems

theorem createFile_creates_file (p : Path) (fs : Filesystem)
    (hpre : CreateFilePrecondition p fs) :
    isFile p (createFile p fs) := by
  unfold isFile createFile fsUpdate
  exists defaultPerms
  simp

theorem createFile_path_exists (p : Path) (fs : Filesystem)
    (hpre : CreateFilePrecondition p fs) :
    pathExists p (createFile p fs) := by
  unfold pathExists createFile fsUpdate
  exists ⟨FSNodeType.file, defaultPerms⟩
  simp

theorem deleteFile_removes_path (p : Path) (fs : Filesystem)
    (hpre : DeleteFilePrecondition p fs) :
    ¬pathExists p (deleteFile p fs) := by
  unfold pathExists deleteFile fsUpdate
  intro ⟨node, heq⟩
  simp at heq

-- File Reversibility Theorem

theorem createFile_deleteFile_reversible (p : Path) (fs : Filesystem)
    (hpre : CreateFilePrecondition p fs) :
    deleteFile p (createFile p fs) = fs := by
  unfold deleteFile createFile fsUpdate
  funext p'
  by_cases h : p = p'
  · subst h
    simp
    cases hfs : fs p with
    | none => rfl
    | some node =>
      exfalso
      apply hpre.notExists
      unfold pathExists
      exact ⟨node, hfs⟩
  · simp [h]

-- Additional Theorems

theorem createFile_preserves_other_paths (p p' : Path) (fs : Filesystem)
    (hneq : p ≠ p') :
    fs p' = (createFile p fs) p' := by
  unfold createFile fsUpdate
  simp [hneq]

theorem createFile_preserves_directories (p p' : Path) (fs : Filesystem)
    (hneq : p ≠ p') (hdir : isDirectory p' fs) :
    isDirectory p' (createFile p fs) := by
  obtain ⟨perms, heq⟩ := hdir
  unfold isDirectory createFile fsUpdate
  exists perms
  simp [hneq, heq]

theorem mkdir_preserves_files (p p' : Path) (fs : Filesystem)
    (hneq : p ≠ p') (hfile : isFile p' fs) :
    isFile p' (mkdir p fs) := by
  obtain ⟨perms, heq⟩ := hfile
  unfold isFile mkdir fsUpdate
  exists perms
  simp [hneq, heq]

-- File Isolation Theorem

theorem file_isolation (p1 p2 : Path) (fs : Filesystem)
    (hneq : p1 ≠ p2) (hexists : pathExists p2 fs) :
    pathExists p2 (createFile p1 fs) ∧ pathExists p2 (deleteFile p1 fs) := by
  obtain ⟨node, heq⟩ := hexists
  constructor
  · -- createFile preserves p2
    unfold pathExists createFile fsUpdate
    exists node
    simp [hneq, heq]
  · -- deleteFile preserves p2
    unfold pathExists deleteFile fsUpdate
    exists node
    simp [hneq, heq]

-- Reverse Direction: deleteFile then createFile
-- Note: Requires original file had defaultPerms for exact equality
theorem deleteFile_createFile_reversible (p : Path) (fs : Filesystem)
    (hpre : DeleteFilePrecondition p fs)
    (hperms : fs p = some ⟨FSNodeType.file, defaultPerms⟩) :
    createFile p (deleteFile p fs) = fs := by
  unfold createFile deleteFile fsUpdate
  funext p'
  by_cases h : p = p'
  · -- p = p'
    subst h
    simp
    -- After deleteFile, fs p = none, then createFile recreates it
    -- We need to show: some ⟨file, defaultPerms⟩ = fs p
    -- By assumption, fs p = some ⟨file, defaultPerms⟩
    rw [hperms]
  · -- p ≠ p'
    simp [h]

-- Summary: File operations proven reversible in Lean 4

/- Valence Shell - Filesystem Model (Lean 4)

   A formal model of POSIX-like filesystem operations for proving
   MAA (Mutually Assured Accountability) properties.

   This model focuses on directory operations (mkdir/rmdir) with
   the goal of proving reversibility and correctness properties.
-/

-- Path Model
abbrev PathComponent := String
abbrev Path := List PathComponent

def rootPath : Path := []

def parentPath (p : Path) : Path :=
  match p.reverse with
  | [] => []
  | _ :: rest => rest.reverse

def pathName (p : Path) : Option PathComponent :=
  match p.reverse with
  | [] => none
  | name :: _ => some name

-- Filesystem Nodes
inductive FSNodeType where
  | file : FSNodeType
  | directory : FSNodeType
  deriving DecidableEq, Repr

structure Permissions where
  readable : Bool
  writable : Bool
  executable : Bool
  deriving DecidableEq, Repr

def defaultPerms : Permissions := ⟨true, true, true⟩

structure FSNode where
  nodeType : FSNodeType
  permissions : Permissions
  deriving DecidableEq, Repr

-- Filesystem State
abbrev Filesystem := Path → Option FSNode

def emptyFS : Filesystem :=
  fun p => match p with
  | [] => some ⟨FSNodeType.directory, defaultPerms⟩
  | _ => none

-- Filesystem Predicates
def pathExists (p : Path) (fs : Filesystem) : Prop :=
  ∃ node, fs p = some node

def isDirectory (p : Path) (fs : Filesystem) : Prop :=
  ∃ perms, fs p = some ⟨FSNodeType.directory, perms⟩

def isFile (p : Path) (fs : Filesystem) : Prop :=
  ∃ perms, fs p = some ⟨FSNodeType.file, perms⟩

def parentExists (p : Path) (fs : Filesystem) : Prop :=
  pathExists (parentPath p) fs

def hasWritePermission (p : Path) (fs : Filesystem) : Prop :=
  ∃ node, fs p = some node ∧ node.permissions.writable = true

def isEmptyDir (p : Path) (fs : Filesystem) : Prop :=
  isDirectory p fs ∧
  ∀ child : Path, child.isPrefixOf p → child ≠ p → ¬pathExists child fs

-- Basic Lemmas

-- A non-empty path is never equal to its parent
theorem nonempty_path_ne_parent (p : Path) (h : p ≠ []) :
    p ≠ parentPath p := by
  intro heq
  unfold parentPath at heq
  match hp : p.reverse with
  | [] =>
    -- If p.reverse = [], then p = []
    have : p = [] := by
      cases p with
      | nil => rfl
      | cons x xs => simp at hp
    contradiction
  | x :: rest =>
    -- p.reverse = x :: rest, so parentPath p = rest.reverse
    simp only [hp] at heq
    -- heq says p = rest.reverse, but p.reverse = x :: rest
    -- So (rest.reverse).reverse = x :: rest
    -- Which means rest = x :: rest (after reverse cancellation), impossible
    have hp2 : p.reverse = x :: rest := hp
    rw [heq] at hp2
    simp at hp2

theorem pathExists_emptyFS_root :
    pathExists rootPath emptyFS := by
  unfold pathExists emptyFS
  exists ⟨FSNodeType.directory, defaultPerms⟩

theorem not_pathExists_emptyFS (p : Path) (h : p ≠ rootPath) :
    ¬pathExists p emptyFS := by
  unfold pathExists emptyFS
  intro ⟨node, heq⟩
  cases p with
  | nil => contradiction
  | cons _ _ => contradiction

-- Filesystem Operations
def fsUpdate (p : Path) (n : Option FSNode) (fs : Filesystem) : Filesystem :=
  fun p' => if p = p' then n else fs p'

-- mkdir: Create a directory
structure MkdirPrecondition (p : Path) (fs : Filesystem) : Prop where
  notExists : ¬pathExists p fs
  parentExists : parentExists p fs
  parentIsDir : isDirectory (parentPath p) fs
  parentWritable : hasWritePermission (parentPath p) fs

def mkdir (p : Path) (fs : Filesystem) : Filesystem :=
  fsUpdate p (some ⟨FSNodeType.directory, defaultPerms⟩) fs

-- rmdir: Remove a directory
structure RmdirPrecondition (p : Path) (fs : Filesystem) : Prop where
  isDir : isDirectory p fs
  isEmpty : isEmptyDir p fs
  parentWritable : hasWritePermission (parentPath p) fs
  notRoot : p ≠ rootPath

def rmdir (p : Path) (fs : Filesystem) : Filesystem :=
  fsUpdate p none fs

-- Postcondition Theorems
theorem mkdir_creates_directory (p : Path) (fs : Filesystem)
    (hpre : MkdirPrecondition p fs) :
    isDirectory p (mkdir p fs) := by
  unfold isDirectory mkdir fsUpdate
  exists defaultPerms
  simp

theorem mkdir_path_exists (p : Path) (fs : Filesystem)
    (hpre : MkdirPrecondition p fs) :
    pathExists p (mkdir p fs) := by
  unfold pathExists mkdir fsUpdate
  exists ⟨FSNodeType.directory, defaultPerms⟩
  simp

theorem rmdir_removes_path (p : Path) (fs : Filesystem)
    (hpre : RmdirPrecondition p fs) :
    ¬pathExists p (rmdir p fs) := by
  unfold pathExists rmdir fsUpdate
  intro ⟨node, heq⟩
  simp at heq

-- The Main Reversibility Theorem
theorem mkdir_rmdir_reversible (p : Path) (fs : Filesystem)
    (hpre : MkdirPrecondition p fs) :
    rmdir p (mkdir p fs) = fs := by
  unfold rmdir mkdir fsUpdate
  funext p'
  by_cases h : p = p'
  · -- p = p'
    subst h
    simp
    -- Need to show: none = fs p
    -- We know hpre.notExists : ¬pathExists p fs
    -- pathExists p fs = ∃ node, fs p = some node
    -- So if fs p = some node, we'd have a contradiction
    cases hfs : fs p with
    | none => rfl
    | some node =>
      exfalso
      apply hpre.notExists
      unfold pathExists
      exact ⟨node, hfs⟩
  · -- p ≠ p'
    simp [h]

-- The Reverse Direction: rmdir then mkdir
-- Note: Requires original directory had defaultPerms for exact equality
theorem rmdir_mkdir_reversible (p : Path) (fs : Filesystem)
    (hpre : RmdirPrecondition p fs)
    (hperms : fs p = some ⟨FSNodeType.directory, defaultPerms⟩) :
    mkdir p (rmdir p fs) = fs := by
  unfold mkdir rmdir fsUpdate
  funext p'
  by_cases h : p = p'
  · -- p = p'
    subst h
    simp
    -- After rmdir, fs p = none, then mkdir recreates it
    -- We need to show: some ⟨directory, defaultPerms⟩ = fs p
    -- By assumption, fs p = some ⟨directory, defaultPerms⟩
    rw [hperms]
  · -- p ≠ p'
    simp [h]

-- Additional Theorems
theorem mkdir_preserves_other_paths (p p' : Path) (fs : Filesystem)
    (hneq : p ≠ p') :
    fs p' = (mkdir p fs) p' := by
  unfold mkdir fsUpdate
  simp [hneq]

theorem rmdir_preserves_other_paths (p p' : Path) (fs : Filesystem)
    (hneq : p ≠ p') :
    fs p' = (rmdir p fs) p' := by
  unfold rmdir fsUpdate
  simp [hneq]

-- Helper: If MkdirPrecondition holds, the path is not root
-- Because root always exists in any reasonable filesystem
theorem mkdir_precondition_path_nonempty (p : Path) (fs : Filesystem)
    (hpre : MkdirPrecondition p fs)
    (hroot_exists : pathExists [] fs) :
    p ≠ [] := by
  intro heq
  subst heq
  exact hpre.notExists hroot_exists

theorem mkdir_parent_still_exists (p : Path) (fs : Filesystem)
    (hpre : MkdirPrecondition p fs) :
    pathExists (parentPath p) (mkdir p fs) := by
  unfold pathExists
  cases hpre.parentExists with
  | intro node hnode =>
    exists node
    unfold mkdir fsUpdate
    by_cases h : p = parentPath p
    · -- This case is impossible for non-root paths
      exfalso
      by_cases hp : p = []
      · -- If p = [], then parentPath [] = []
        -- hpre.parentExists : pathExists [] fs
        -- hpre.notExists : ¬pathExists [] fs
        -- Contradiction!
        subst hp
        have hpe : pathExists [] fs := hpre.parentExists
        exact hpre.notExists hpe
      · -- If p ≠ [], then by nonempty_path_ne_parent, p ≠ parentPath p
        exact nonempty_path_ne_parent p hp h
    · simp [h]
      exact hnode

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

-- Path Lemmas

/-- Helper: reverse of empty list is empty -/
theorem reverse_nil_iff {α : Type} (l : List α) : l.reverse = [] ↔ l = [] := by
  constructor
  · intro h
    cases l with
    | nil => rfl
    | cons x xs =>
      simp [List.reverse] at h
      exact absurd h (List.append_ne_nil_of_ne_nil_right _ _ (List.cons_ne_nil x []))
  · intro h
    subst h
    rfl

/-- Key lemma: parentPath p ≠ p for non-empty paths -/
theorem parentPath_ne_self (p : Path) (hnoroot : p ≠ rootPath) :
    parentPath p ≠ p := by
  unfold parentPath
  intro heq
  match hp : p.reverse with
  | [] =>
    -- reverse p = [] means p = []
    have : p = [] := (reverse_nil_iff p).mp hp
    exact hnoroot this
  | _ :: rest =>
    -- parentPath p = rest.reverse, heq says rest.reverse = p
    -- So reverse (rest.reverse) = reverse p, i.e., rest = reverse p
    -- But reverse p = _ :: rest, so rest = _ :: rest, impossible
    rw [hp] at heq
    simp at heq
    have hlen : rest.length = (_ :: rest).length := by
      calc rest.length = rest.reverse.reverse.length := by simp
        _ = p.reverse.length := by rw [← heq]; simp
        _ = (_ :: rest).length := by rw [hp]
    simp at hlen

/-- mkdir precondition implies p is not root -/
theorem mkdirPrecondition_nonroot (p : Path) (fs : Filesystem)
    (hpre : MkdirPrecondition p fs) : p ≠ rootPath := by
  intro heq
  subst heq
  unfold parentExists rootPath parentPath at hpre
  simp at hpre
  exact hpre.notExists hpre.parentExists

-- Basic Lemmas
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
    cases hpre.notExists
    assumption
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

theorem mkdir_parent_still_exists (p : Path) (fs : Filesystem)
    (hpre : MkdirPrecondition p fs) :
    pathExists (parentPath p) (mkdir p fs) := by
  unfold pathExists
  cases hpre.parentExists with
  | intro node hnode =>
    exists node
    unfold mkdir fsUpdate
    by_cases h : p = parentPath p
    · -- Would mean p = parent p, impossible for non-root
      exfalso
      have hnonroot : p ≠ rootPath := mkdirPrecondition_nonroot p fs hpre
      have hne : parentPath p ≠ p := parentPath_ne_self p hnonroot
      exact hne h.symm
    · simp [h]
      exact hnode

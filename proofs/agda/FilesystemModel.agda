{-# OPTIONS --safe --without-K --cubical-compatible #-}
{- Valence Shell - Filesystem Model (Agda)

   A formal model of POSIX-like filesystem operations for proving
   MAA (Mutually Assured Accountability) properties.

   This model focuses on directory operations (mkdir/rmdir) with
   the goal of proving reversibility and correctness properties.
-}

module FilesystemModel where

open import Data.String using (String; _≟_)
open import Data.List using (List; []; _∷_; reverse)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; ∃; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≗_; refl; sym; trans; cong; subst)
open import Function using (_∘_)
open import Data.Empty using (⊥-elim)

-- Path Model
PathComponent : Set
PathComponent = String

Path : Set
Path = List PathComponent

rootPath : Path
rootPath = []

parentPath : Path → Path
parentPath p with reverse p
... | [] = []
... | x ∷ rest = reverse rest

pathName : Path → Maybe PathComponent
pathName p with reverse p
... | [] = nothing
... | name ∷ _ = just name

-- Filesystem Nodes
data FSNodeType : Set where
  File : FSNodeType
  Directory : FSNodeType

record Permissions : Set where
  constructor mkPermissions
  field
    readable : Bool
    writable : Bool
    executable : Bool

defaultPerms : Permissions
defaultPerms = record { readable = true ; writable = true ; executable = true }

record FSNode : Set where
  constructor mkFSNode
  field
    nodeType : FSNodeType
    permissions : Permissions

-- Filesystem State
Filesystem : Set
Filesystem = Path → Maybe FSNode

emptyFS : Filesystem
emptyFS [] = just (mkFSNode Directory defaultPerms)
emptyFS (x ∷ xs) = nothing

-- Filesystem Predicates
pathExists : Path → Filesystem → Set
pathExists p fs = ∃ λ node → fs p ≡ just node

isDirectory : Path → Filesystem → Set
isDirectory p fs = ∃ λ perms → fs p ≡ just (mkFSNode Directory perms)

isFile : Path → Filesystem → Set
isFile p fs = ∃ λ perms → fs p ≡ just (mkFSNode File perms)

parentExists : Path → Filesystem → Set
parentExists p fs = pathExists (parentPath p) fs

hasWritePermission : Path → Filesystem → Set
hasWritePermission p fs = ∃ λ node → (fs p ≡ just node) × (Permissions.writable (FSNode.permissions node) ≡ true)

-- `xs ⊑ ys`: xs is a prefix of ys (component-wise).
data _⊑_ : Path → Path → Set where
  ⊑-[] : ∀ {ys} → [] ⊑ ys
  ⊑-∷  : ∀ {x xs ys} → xs ⊑ ys → (x ∷ xs) ⊑ (x ∷ ys)

-- A directory is empty when no strict descendant exists. The prefix runs
-- from p to the child (descendants), matching Coq `is_empty_dir` and the
-- Lean model after its 2026-11-09 fix.
record IsEmptyDir (p : Path) (fs : Filesystem) : Set where
  field
    isDir : isDirectory p fs
    noChildren : ∀ child → p ⊑ child → ¬ (child ≡ p) → ¬ pathExists child fs

-- Basic Lemmas
pathExists-emptyFS-root : pathExists rootPath emptyFS
pathExists-emptyFS-root = mkFSNode Directory defaultPerms , refl

-- Maybe-level lemma: nothing is never just
nothing≢just : ∀ {A : Set} {x : A} → ¬ (nothing ≡ just x)
nothing≢just ()

-- Filesystem Operations
_path-≟_ : (p₁ p₂ : Path) → Dec (p₁ ≡ p₂)
[] path-≟ [] = yes refl
[] path-≟ (x ∷ p₂) = no (λ ())
(x ∷ p₁) path-≟ [] = no (λ ())
(x ∷ p₁) path-≟ (y ∷ p₂) with x ≟ y | p₁ path-≟ p₂
... | yes refl | yes refl = yes refl
... | yes _ | no p₁≢p₂ = no (λ { refl → p₁≢p₂ refl })
... | no x≢y | _ = no (λ { refl → x≢y refl })

fsUpdate : Path → Maybe FSNode → Filesystem → Filesystem
fsUpdate p n fs p' with p path-≟ p'
... | yes _ = n
... | no _ = fs p'

-- fsUpdate at the same path returns the inserted value
fsUpdate-at : ∀ p n fs → fsUpdate p n fs p ≡ n
fsUpdate-at p n fs with p path-≟ p
... | yes _ = refl
... | no p≢p = ⊥-elim (p≢p refl)

-- fsUpdate at a different path leaves the filesystem untouched
fsUpdate-other : ∀ p p' n fs → ¬ (p ≡ p') → fsUpdate p n fs p' ≡ fs p'
fsUpdate-other p p' n fs p≢p' with p path-≟ p'
... | yes p≡p' = ⊥-elim (p≢p' p≡p')
... | no _ = refl

-- fsUpdate respects pointwise equality of the filesystem it updates
fsUpdate-cong : ∀ p n {fs₁ fs₂} → fs₁ ≗ fs₂ → fsUpdate p n fs₁ ≗ fsUpdate p n fs₂
fsUpdate-cong p n h p' with p path-≟ p'
... | yes _ = refl
... | no _ = h p'

-- mkdir: Create a directory
record MkdirPrecondition (p : Path) (fs : Filesystem) : Set where
  field
    notExists : ¬ pathExists p fs
    parent-path-exists : parentExists p fs
    parentIsDir : isDirectory (parentPath p) fs
    -- parentWritable could be added

mkdir : Path → Filesystem → Filesystem
mkdir p fs = fsUpdate p (just (mkFSNode Directory defaultPerms)) fs

-- rmdir: Remove a directory
record RmdirPrecondition (p : Path) (fs : Filesystem) : Set where
  field
    isDir : isDirectory p fs
    isEmpty : IsEmptyDir p fs
    notRoot : ¬ (p ≡ rootPath)

rmdir : Path → Filesystem → Filesystem
rmdir p fs = fsUpdate p nothing fs

-- Postcondition Theorems
mkdir-creates-directory : ∀ p fs → MkdirPrecondition p fs → isDirectory p (mkdir p fs)
mkdir-creates-directory p fs pre = defaultPerms , fsUpdate-at p _ fs

mkdir-path-exists : ∀ p fs → MkdirPrecondition p fs → pathExists p (mkdir p fs)
mkdir-path-exists p fs pre = mkFSNode Directory defaultPerms , fsUpdate-at p _ fs

rmdir-removes-path : ∀ p fs → RmdirPrecondition p fs → ¬ pathExists p (rmdir p fs)
rmdir-removes-path p fs pre (node , eq) =
  nothing≢just (trans (sym (fsUpdate-at p nothing fs)) eq)

-- Filesystem equality is pointwise (`_≗_`): two filesystems are equal when
-- they agree on every path. This needs no function extensionality, so the
-- module checks under `--safe --without-K --cubical-compatible`. (Until
-- 2026-11-09 these theorems were stated with `_≡_` on functions and closed
-- with an assumed function-extensionality axiom.)

-- Helper: from ¬ pathExists, derive fs p ≡ nothing
not-path-exists-nothing : ∀ {p : Path} {fs : Filesystem} →
  ¬ pathExists p fs → fs p ≡ nothing
not-path-exists-nothing {p} {fs} notEx with fs p
... | nothing = refl
... | just node = ⊥-elim (notEx (node , refl))
  where
    open import Data.Empty using (⊥-elim)

mkdir-rmdir-reversible : ∀ p fs →
  MkdirPrecondition p fs →
  rmdir p (mkdir p fs) ≗ fs
mkdir-rmdir-reversible p fs pre = helper
  where
    open import Data.Empty using (⊥-elim)

    helper : ∀ p' → rmdir p (mkdir p fs) p' ≡ fs p'
    helper p' = case-split (p path-≟ p')
      where
        case-split : Dec (p ≡ p') → rmdir p (mkdir p fs) p' ≡ fs p'
        case-split (yes refl) =
          trans (fsUpdate-at p nothing (mkdir p fs))
                (sym (not-path-exists-nothing {p} {fs} (MkdirPrecondition.notExists pre)))
        case-split (no p≢p') =
          trans (fsUpdate-other p p' nothing (mkdir p fs) p≢p')
                (fsUpdate-other p p' (just (mkFSNode Directory defaultPerms)) fs p≢p')

-- Additional Theorems
mkdir-preserves-other-paths : ∀ p p' fs →
  ¬ (p ≡ p') →
  fs p' ≡ mkdir p fs p'
mkdir-preserves-other-paths p p' fs p≢p' with p path-≟ p'
... | yes p≡p' = ⊥-elim (p≢p' p≡p')
  where
    open import Data.Empty using (⊥-elim)
... | no _ = refl

rmdir-preserves-other-paths : ∀ p p' fs →
  ¬ (p ≡ p') →
  fs p' ≡ rmdir p fs p'
rmdir-preserves-other-paths p p' fs p≢p' with p path-≟ p'
... | yes p≡p' = ⊥-elim (p≢p' p≡p')
  where
    open import Data.Empty using (⊥-elim)
... | no _ = refl

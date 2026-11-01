{- Valence Shell - File Operations (Agda)

   Extension of filesystem model to include file operations.
   Proves reversibility of file create/delete operations.
-}

module FileOperations where

open import FilesystemModel
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

-- File Operations

record CreateFilePrecondition (p : Path) (fs : Filesystem) : Set where
  field
    notExists : ¬ pathExists p fs
    parent-path-exists : parentExists p fs
    parentIsDir : isDirectory (parentPath p) fs

createFile : Path → Filesystem → Filesystem
createFile p fs = fsUpdate p (just (mkFSNode File defaultPerms)) fs

record DeleteFilePrecondition (p : Path) (fs : Filesystem) : Set where
  field
    deletedIsFile : isFile p fs

deleteFile : Path → Filesystem → Filesystem
deleteFile p fs = fsUpdate p nothing fs

-- Postcondition Theorems

createFile-creates-file : ∀ p fs → CreateFilePrecondition p fs → isFile p (createFile p fs)
createFile-creates-file p fs pre with p path-≟ p
... | yes refl = defaultPerms , refl
... | no p≢p = ⊥-elim (p≢p refl)
  where
    open import Data.Empty using (⊥-elim)

createFile-path-exists : ∀ p fs → CreateFilePrecondition p fs → pathExists p (createFile p fs)
createFile-path-exists p fs pre with p path-≟ p
... | yes refl = mkFSNode File defaultPerms , refl
... | no p≢p = ⊥-elim (p≢p refl)
  where
    open import Data.Empty using (⊥-elim)

deleteFile-removes-path : ∀ p fs → DeleteFilePrecondition p fs → ¬ pathExists p (deleteFile p fs)
deleteFile-removes-path p fs pre (node , eq) with p path-≟ p
... | yes refl = nothing≢just eq
... | no p≢p = ⊥-elim (p≢p refl)
  where
    open import Data.Empty using (⊥-elim)

-- File Reversibility Theorem

createFile-deleteFile-reversible : ∀ p fs →
  CreateFilePrecondition p fs →
  deleteFile p (createFile p fs) ≡ fs
createFile-deleteFile-reversible p fs pre = funext helper
  where
    open import Data.Empty using (⊥-elim)

    helper : ∀ p' → deleteFile p (createFile p fs) p' ≡ fs p'
    helper p' = case-split (p path-≟ p')
      where
        case-split : Dec (p ≡ p') → deleteFile p (createFile p fs) p' ≡ fs p'
        case-split (yes refl) =
          trans (fsUpdate-at p nothing (createFile p fs))
                (sym (not-path-exists-nothing {p} {fs} (CreateFilePrecondition.notExists pre)))
        case-split (no p≢p') =
          trans (fsUpdate-other p p' nothing (createFile p fs) p≢p')
                (fsUpdate-other p p' (just (mkFSNode File defaultPerms)) fs p≢p')

-- Additional Theorems

createFile-preserves-other-paths : ∀ p p' fs →
  ¬ (p ≡ p') →
  fs p' ≡ createFile p fs p'
createFile-preserves-other-paths p p' fs p≢p' with p path-≟ p'
... | yes p≡p' = ⊥-elim (p≢p' p≡p')
  where
    open import Data.Empty using (⊥-elim)
... | no _ = refl

-- File Isolation Theorem

-- File isolation: operations on p1 preserve existence of p2 (p1 ≠ p2)
file-isolation : ∀ p1 p2 fs →
  ¬ (p1 ≡ p2) →
  pathExists p2 fs →
  pathExists p2 (createFile p1 fs) × pathExists p2 (deleteFile p1 fs)
file-isolation p1 p2 fs p1≢p2 (node , prf) =
  ( (node , trans (sym (createFile-preserves-other p1≢p2)) prf)
  , (node , trans (sym (deleteFile-preserves-other p1≢p2)) prf) )
  where
    createFile-preserves-other : ¬ (p1 ≡ p2) → fs p2 ≡ createFile p1 fs p2
    createFile-preserves-other h = createFile-preserves-other-paths p1 p2 fs h

    deleteFile-preserves-other : ¬ (p1 ≡ p2) → fs p2 ≡ deleteFile p1 fs p2
    deleteFile-preserves-other h with p1 path-≟ p2
    ... | yes p≡ = ⊥-elim (h p≡)
      where
        open import Data.Empty using (⊥-elim)
    ... | no _ = refl

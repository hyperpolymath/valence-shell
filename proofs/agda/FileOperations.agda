{- Valence Shell - File Operations (Agda)

   Extension of filesystem model to include file operations.
   Proves reversibility of file create/delete operations.
-}

module FileOperations where

open import FilesystemModel
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- File Operations

record CreateFilePrecondition (p : Path) (fs : Filesystem) : Set where
  field
    notExists : ¬ pathExists p fs
    parentExists : parentExists p fs
    parentIsDir : isDirectory (parentPath p) fs

createFile : Path → Filesystem → Filesystem
createFile p fs = fsUpdate p (just (mkFSNode File defaultPerms)) fs

record DeleteFilePrecondition (p : Path) (fs : Filesystem) : Set where
  field
    isFile : isFile p fs

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
... | yes refl = λ ()
... | no p≢p = ⊥-elim (p≢p refl)
  where
    open import Data.Empty using (⊥-elim)

-- File Reversibility Theorem

createFile-deleteFile-reversible : ∀ p fs →
  CreateFilePrecondition p fs →
  deleteFile p (createFile p fs) ≡ fs
createFile-deleteFile-reversible p fs pre = funext helper
  where
    helper : ∀ p' → deleteFile p (createFile p fs) p' ≡ fs p'
    helper p' with p path-≟ p'
    ... | yes refl with p path-≟ p
        ... | yes _ with CreateFilePrecondition.notExists pre
            ... | notEx = ⊥-elim (notEx (FSNode.permissions node , prf))
              where
                open import Data.Empty using (⊥-elim)
                postulate node : FSNode
                postulate prf : fs p ≡ just node
        ... | no p≢p = ⊥-elim (p≢p refl)
          where
            open import Data.Empty using (⊥-elim)
    ... | no p≢p' with p path-≟ p'
        ... | yes p≡p' = ⊥-elim (p≢p' p≡p')
          where
            open import Data.Empty using (⊥-elim)
        ... | no _ = refl

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

file-isolation : ∀ p1 p2 fs →
  ¬ (p1 ≡ p2) →
  pathExists p2 fs →
  pathExists p2 (createFile p1 fs) × pathExists p2 (deleteFile p1 fs)
file-isolation p1 p2 fs p1≢p2 (node , prf) =
  ((node , createFile-preserves p1≢p2) , (node , deleteFile-preserves p1≢p2))
  where
    postulate createFile-preserves : ¬ (p1 ≡ p2) → fs p2 ≡ createFile p1 fs p2
    postulate deleteFile-preserves : ¬ (p1 ≡ p2) → fs p2 ≡ deleteFile p1 fs p2

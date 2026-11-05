{- Valence Shell - Symlink Operations (Agda)

   Abstract model of symbolic link creation and removal.
   In this model, a symlink is represented as a file node with default
   permissions; the target path is modeled externally.
-}

module SymlinkOperations where

open import FilesystemModel
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

-- Preconditions for creating a symlink
record SymlinkPrecondition (p : Path) (fs : Filesystem) : Set where
  field
    notExists : ¬ pathExists p fs
    parent-path-exists : parentExists p fs
    parentIsDir : isDirectory (parentPath p) fs
    parentWritable : hasWritePermission (parentPath p) fs

-- Create a symlink at path p (modeled as a file node)
symlink : Path → Filesystem → Filesystem
symlink p fs = fsUpdate p (just (mkFSNode File defaultPerms)) fs

-- Remove a symlink at path p
unlink : Path → Filesystem → Filesystem
unlink p fs = fsUpdate p nothing fs

-- Postcondition Lemmas
symlink-creates-path : ∀ p fs → SymlinkPrecondition p fs → pathExists p (symlink p fs)
symlink-creates-path p fs pre with p path-≟ p
... | yes refl = mkFSNode File defaultPerms , refl
... | no p≢p = ⊥-elim (p≢p refl)
  where
    open import Data.Empty using (⊥-elim)

unlink-removes-path : ∀ p fs → pathExists p fs → ¬ pathExists p (unlink p fs)
unlink-removes-path p fs (node , eq) with p path-≟ p
... | yes refl = λ ()
... | no p≢p = ⊥-elim (p≢p refl)
  where
    open import Data.Empty using (⊥-elim)

-- Reversibility Theorem
symlink-unlink-reversible : ∀ p fs → SymlinkPrecondition p fs → unlink p (symlink p fs) ≡ fs
symlink-unlink-reversible p fs pre = funext helper
  where
    helper : ∀ p' → unlink p (symlink p fs) p' ≡ fs p'
    helper p' = case-split (p path-≟ p')
      where
        open import Data.Empty using (⊥-elim)

        -- If no node exists at p, then fs p = nothing
        not-exists-is-nothing : ¬ pathExists p fs → fs p ≡ nothing
        not-exists-is-nothing notEx with fs p
        ... | nothing = refl
        ... | just node = ⊥-elim (notEx (node , refl))

        case-split : Dec (p ≡ p') → unlink p (symlink p fs) p' ≡ fs p'
        case-split (yes refl) =
          -- unlink p (symlink p fs) p reduces to nothing (fsUpdate-at)
          trans (fsUpdate-at p nothing (symlink p fs))
                (sym (not-exists-is-nothing (SymlinkPrecondition.notExists pre)))
        case-split (no p≢p') =
          trans (fsUpdate-other p p' nothing (symlink p fs) p≢p')
                (fsUpdate-other p p' (just (mkFSNode File defaultPerms)) fs p≢p')

-- Summary:
-- ✓ Symlink creation and removal operations
-- ✓ Preconditions for safe symlink creation
-- ✓ Reversibility: unlink(symlink(p, fs)) = fs

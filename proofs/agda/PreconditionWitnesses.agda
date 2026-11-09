{-# OPTIONS --safe --without-K --cubical-compatible #-}
-- SPDX-License-Identifier: MPL-2.0
{- Valence Shell - precondition non-vacuity witnesses (Agda)

   Every reversibility theorem has the shape `Pre p fs → op⁻¹ (op p fs) ≗ fs`.
   If `Pre` is uninhabited the theorem says nothing. This module exhibits one
   concrete state per precondition, so an edit that empties a precondition
   fails the check. Mirrors proofs/lean4/PreconditionWitnesses.lean.
   Added 2026-11-09; see docs/audits/2026-11-09-proof-ground-truth.adoc.
-}

module PreconditionWitnesses where

open import FilesystemModel
open import FileOperations
open import SymlinkOperations
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Relation.Nullary using (¬_)

a : Path
a = "a" ∷ []

mkdir-pre-inhabited : MkdirPrecondition a emptyFS
mkdir-pre-inhabited = record
  { notExists          = λ { (_ , ()) }
  ; parent-path-exists = mkFSNode Directory defaultPerms , refl
  ; parentIsDir        = defaultPerms , refl
  }

-- The emptiness field is the one that was missing before 2026-11-09.
rmdir-pre-inhabited : RmdirPrecondition a (mkdir a emptyFS)
rmdir-pre-inhabited = record
  { isDir   = defaultPerms , fsUpdate-at a _ emptyFS
  ; isEmpty = record
      { isDir      = defaultPerms , fsUpdate-at a _ emptyFS
      ; noChildren = no-children
      }
  ; notRoot = λ ()
  }
  where
    no-children : ∀ child → a ⊑ child → ¬ (child ≡ a) → ¬ pathExists child (mkdir a emptyFS)
    no-children (.("a") ∷ [])      (⊑-∷ ⊑-[]) ne _          = ne refl
    no-children (.("a") ∷ y ∷ ys)  (⊑-∷ ⊑-[]) _  (node , eq) =
      nothing≢just (trans (sym (fsUpdate-other a ("a" ∷ y ∷ ys) (just (mkFSNode Directory defaultPerms)) emptyFS λ ())) eq)

createFile-pre-inhabited : CreateFilePrecondition a emptyFS
createFile-pre-inhabited = record
  { notExists          = λ { (_ , ()) }
  ; parent-path-exists = mkFSNode Directory defaultPerms , refl
  ; parentIsDir        = defaultPerms , refl
  }

deleteFile-pre-inhabited : DeleteFilePrecondition a (createFile a emptyFS)
deleteFile-pre-inhabited = record
  { deletedIsFile = defaultPerms , fsUpdate-at a _ emptyFS }

symlink-pre-inhabited : SymlinkPrecondition a emptyFS
symlink-pre-inhabited = record
  { notExists          = λ { (_ , ()) }
  ; parent-path-exists = mkFSNode Directory defaultPerms , refl
  ; parentIsDir        = defaultPerms , refl
  ; parentWritable     = mkFSNode Directory defaultPerms , refl , refl
  }

{-# OPTIONS --safe --without-K --cubical-compatible #-}
-- SPDX-License-Identifier: MPL-2.0
{- Valence Shell - precondition non-vacuity witnesses (Agda)

   Every reversibility theorem has the shape `Pre p fs → op⁻¹ (op p fs) ≗ fs`.
   If `Pre` is uninhabited the theorem says nothing. This module exhibits one
   concrete state for each precondition in the tree (mkdir, rmdir, createFile,
   deleteFile, symlink, the composition record, copy, move, read, write, chmod,
   chown), and applies each copy/move/write/chmod/chown reversibility theorem to
   its witness, so an edit that empties a precondition, or moves a theorem's
   premise away from it, fails the check. The core-operation witnesses mirror
   proofs/lean4/PreconditionWitnesses.lean.
   Added 2026-11-09; see docs/audits/2026-11-09-proof-ground-truth.adoc.
-}

module PreconditionWitnesses where

open import FilesystemModel
open import FileOperations
open import SymlinkOperations
open import FilesystemComposition
import CopyMoveOperations as CM
import FileContentOperations as FC
import PermissionOperations as PO
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≗_; refl; sym; trans)
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

-- Negative control: a directory with a child does not satisfy the precondition.
-- Guards against a weakening of `IsEmptyDir` that `rmdir-pre-inhabited` alone
-- would not catch.
rmdir-pre-rejects-nonempty :
  ¬ RmdirPrecondition a (mkdir ("a" ∷ "b" ∷ []) (mkdir a emptyFS))
rmdir-pre-rejects-nonempty pre =
  IsEmptyDir.noChildren (RmdirPrecondition.isEmpty pre)
    ("a" ∷ "b" ∷ []) (⊑-∷ ⊑-[]) (λ ())
    (_ , fsUpdate-at ("a" ∷ "b" ∷ []) _ (mkdir a emptyFS))

-- The composition theorems quantify over `ReversibleDP`; this shows the
-- record is inhabited, so `operationSequenceReversible` is not vacuous for a
-- sequence containing mkdir (its reverse precondition is the rmdir one).
mkdir-reversibleDP-inhabited : ReversibleDP (mkdirOp a) emptyFS
mkdir-reversibleDP-inhabited = record
  { precondition        = mkdir-pre-inhabited
  ; reversePrecondition = rmdir-pre-inhabited
  ; permsWitness        = mkdirPerms refl
  }

-- A one-step sequence satisfies `AllReversibleDP`, so
-- `operationSequenceReversible` has a non-empty instance.
mkdir-sequence-reversibleDP : AllReversibleDP (mkdirOp a ∷ []) emptyFS
mkdir-sequence-reversibleDP = consReversibleDP mkdir-reversibleDP-inhabited nilReversibleDP


-- ---------------------------------------------------------------------------
-- Copy and move (CopyMoveOperations). The source `a` is a file in the root
-- directory; the destination `b` is absent and its parent is the root.
-- ---------------------------------------------------------------------------

b : Path
b = "b" ∷ []

fileAt-a : Filesystem
fileAt-a = createFile a emptyFS

private
  root-of-fileAt-a : fileAt-a [] ≡ just (mkFSNode Directory defaultPerms)
  root-of-fileAt-a = fsUpdate-other a [] (just (mkFSNode File defaultPerms)) emptyFS (λ ())

  b-absent : ¬ pathExists b fileAt-a
  b-absent (_ , eq) = nothing≢just (trans (sym (fsUpdate-other a b (just (mkFSNode File defaultPerms)) emptyFS (λ ()))) eq)

  root-writable : hasWritePermission [] fileAt-a
  root-writable = mkFSNode Directory defaultPerms , root-of-fileAt-a , refl

copy-pre-inhabited : CM.copyFilePrecondition a b fileAt-a
copy-pre-inhabited =
    (defaultPerms , fsUpdate-at a _ emptyFS)
  , b-absent
  , (mkFSNode Directory defaultPerms , root-of-fileAt-a)
  , (defaultPerms , root-of-fileAt-a)
  , root-writable

move-pre-inhabited : CM.movePrecondition a b fileAt-a
move-pre-inhabited =
    (mkFSNode File defaultPerms , fsUpdate-at a _ emptyFS)
  , b-absent
  , (mkFSNode Directory defaultPerms , root-of-fileAt-a)
  , (λ ())
  , root-writable
  , root-writable

-- ---------------------------------------------------------------------------
-- Read and write (FileContentOperations). `writeFileReversible` also needs
-- `readFile p fs ≡ just oldContent`; both premises are inhabited here.
-- ---------------------------------------------------------------------------

private
  textNode : FC.FSNodeWithContent
  textNode = FC.mkFSNodeWithContent File defaultPerms (just "x")

  textFS : FC.FilesystemWithContent
  textFS _ = just textNode

read-pre-inhabited : FC.ReadFilePrecondition a textFS
read-pre-inhabited = textNode , refl , refl , refl

write-pre-inhabited : FC.WriteFilePrecondition a textFS
write-pre-inhabited = textNode , refl , refl , refl

write-old-content : FC.readFile a textFS ≡ just "x"
write-old-content = refl

-- ---------------------------------------------------------------------------
-- chmod and chown (PermissionOperations). The reversibility theorems take the
-- old mode / owner as part of their premise; both forms are inhabited.
-- ---------------------------------------------------------------------------

private
  extNode : PO.FSNodeExt
  extNode = PO.mkFSNodeExt File 0 (PO.mkOwnership 0 0)

  extFS : PO.FilesystemExt
  extFS _ = just extNode

chmod-pre-inhabited : PO.ChmodPrecondition a extFS
chmod-pre-inhabited = extNode , refl

chmod-old-mode : Σ PO.FSNodeExt (λ node → (extFS a ≡ just node) × (PO.FSNodeExt.mode node ≡ 0))
chmod-old-mode = extNode , refl , refl

chown-pre-inhabited : PO.ChownPrecondition a extFS
chown-pre-inhabited = extNode , refl

chown-old-owner : Σ PO.FSNodeExt (λ node → (extFS a ≡ just node) × (PO.FSNodeExt.owner node ≡ PO.mkOwnership 0 0))
chown-old-owner = extNode , refl , refl

-- ---------------------------------------------------------------------------
-- Each reversibility theorem applied to its witness: if a theorem's premise
-- drifts away from the witness above, these stop type-checking.
-- ---------------------------------------------------------------------------

copy-reversible-instance : deleteFile b (CM.copyFile a b fileAt-a) ≗ fileAt-a
copy-reversible-instance = CM.copyFile-reversible a b fileAt-a copy-pre-inhabited

move-reversible-instance : CM.moveFile b a (CM.moveFile a b fileAt-a) ≗ fileAt-a
move-reversible-instance = CM.moveFile-reversible a b fileAt-a move-pre-inhabited

write-reversible-instance : FC.writeFile a "x" (FC.writeFile a "y" textFS) ≗ textFS
write-reversible-instance =
  FC.writeFileReversible a textFS "x" "y" write-pre-inhabited write-old-content

chmod-reversible-instance : PO.chmod a 0 (PO.chmod a 7 extFS) ≗ extFS
chmod-reversible-instance = PO.chmod-reversible a extFS 0 7 chmod-old-mode

chown-reversible-instance :
  PO.chown a (PO.mkOwnership 0 0) (PO.chown a (PO.mkOwnership 1 1) extFS) ≗ extFS
chown-reversible-instance =
  PO.chown-reversible a extFS (PO.mkOwnership 0 0) (PO.mkOwnership 1 1) chown-old-owner

{- Valence Shell - Filesystem Composition (Agda)

   Composition theorems for filesystem operations
-}

module FilesystemComposition where

open import FilesystemModel
open import FileOperations
open import Data.List using (List; []; _∷_; reverse; map; _++_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

-- Operation type
data Operation : Set where
  mkdirOp : Path → Operation
  rmdirOp : Path → Operation
  createFileOp : Path → Operation
  deleteFileOp : Path → Operation

-- Apply operation
applyOp : Operation → Filesystem → Filesystem
applyOp (mkdirOp p) fs = mkdir p fs
applyOp (rmdirOp p) fs = rmdir p fs
applyOp (createFileOp p) fs = createFile p fs
applyOp (deleteFileOp p) fs = deleteFile p fs

-- Reverse operation
reverseOp : Operation → Operation
reverseOp (mkdirOp p) = rmdirOp p
reverseOp (rmdirOp p) = mkdirOp p
reverseOp (createFileOp p) = deleteFileOp p
reverseOp (deleteFileOp p) = createFileOp p

-- Apply sequence
applySequence : List Operation → Filesystem → Filesystem
applySequence [] fs = fs
applySequence (op ∷ ops) fs = applySequence ops (applyOp op fs)

-- Reverse sequence
reverseSequence : List Operation → List Operation
reverseSequence ops = map reverseOp (reverse ops)

-- Precondition
opPrecondition : Operation → Filesystem → Set
opPrecondition (mkdirOp p) fs = MkdirPrecondition p fs
opPrecondition (rmdirOp p) fs = RmdirPrecondition p fs
opPrecondition (createFileOp p) fs = CreateFilePrecondition p fs
opPrecondition (deleteFileOp p) fs = DeleteFilePrecondition p fs

-- Reversible
record Reversible (op : Operation) (fs : Filesystem) : Set where
  field
    precondition : opPrecondition op fs
    reversePrecondition : opPrecondition (reverseOp op) (applyOp op fs)

-- All reversible
data AllReversible : List Operation → Filesystem → Set where
  nilReversible : ∀ {fs} → AllReversible [] fs
  consReversible : ∀ {op ops fs} →
    Reversible op fs →
    AllReversible ops (applyOp op fs) →
    AllReversible (op ∷ ops) fs

-- NOTE: The reverse-direction reversibility theorems (rmdir→mkdir, delete→create)
-- require that the original node had defaultPerms, because mkdir/createFile always
-- create nodes with defaultPerms. This is a known model limitation.
-- In the Rust implementation, all operations use default permissions,
-- so this constraint is always satisfied in practice.

-- Helper constraint: directory at path has default permissions
HasDefaultDirPerms : Path → Filesystem → Set
HasDefaultDirPerms p fs = fs p ≡ just (mkFSNode Directory defaultPerms)

-- Helper constraint: file at path has default permissions
HasDefaultFilePerms : Path → Filesystem → Set
HasDefaultFilePerms p fs = fs p ≡ just (mkFSNode File defaultPerms)

-- Helper: rmdir-mkdir reversibility (requires default perms)
rmdir-mkdir-reversible : ∀ (p : Path) (fs : Filesystem) →
  RmdirPrecondition p fs →
  HasDefaultDirPerms p fs →
  applyOp (mkdirOp p) (applyOp (rmdirOp p) fs) ≡ fs
rmdir-mkdir-reversible p fs pre hperms = funext helper
  where
    helper : ∀ p' → mkdir p (rmdir p fs) p' ≡ fs p'
    helper p' with p path-≟ p'
    ... | yes refl with p path-≟ p
        ... | yes _ = sym hperms
        ... | no p≢p = ⊥-elim (p≢p refl)
          where
            open import Data.Empty using (⊥-elim)
    ... | no p≢p' with p path-≟ p'
        ... | yes p≡p' = ⊥-elim (p≢p' p≡p')
          where
            open import Data.Empty using (⊥-elim)
        ... | no _ = refl

-- Helper: deleteFile-createFile reversibility (requires default perms)
deleteFile-createFile-reversible : ∀ (p : Path) (fs : Filesystem) →
  DeleteFilePrecondition p fs →
  HasDefaultFilePerms p fs →
  applyOp (createFileOp p) (applyOp (deleteFileOp p) fs) ≡ fs
deleteFile-createFile-reversible p fs pre hperms = funext helper
  where
    helper : ∀ p' → createFile p (deleteFile p fs) p' ≡ fs p'
    helper p' with p path-≟ p'
    ... | yes refl with p path-≟ p
        ... | yes _ = sym hperms
        ... | no p≢p = ⊥-elim (p≢p refl)
          where
            open import Data.Empty using (⊥-elim)
    ... | no p≢p' with p path-≟ p'
        ... | yes p≡p' = ⊥-elim (p≢p' p≡p')
          where
            open import Data.Empty using (⊥-elim)
        ... | no _ = refl

-- Default-perms witness for reverse operations.
-- mkdir/createFile always create with defaultPerms, so:
-- - Forward mkdir/createFile: reverse (rmdir/delete) doesn't need perms witness
-- - Forward rmdir/deleteFile: reverse (mkdir/create) needs original to have had defaultPerms
-- In the Rust implementation, all nodes use default permissions, so this always holds.
data HasDefaultPerms (op : Operation) (fs : Filesystem) : Set where
  mkdirPerms : ∀ {p} → op ≡ mkdirOp p → HasDefaultPerms op fs
  createFilePerms : ∀ {p} → op ≡ createFileOp p → HasDefaultPerms op fs
  rmdirPerms : ∀ {p} → op ≡ rmdirOp p → HasDefaultDirPerms p fs → HasDefaultPerms op fs
  deleteFilePerms : ∀ {p} → op ≡ deleteFileOp p → HasDefaultFilePerms p fs → HasDefaultPerms op fs

-- Extended Reversible: includes default-perms witness
record ReversibleDP (op : Operation) (fs : Filesystem) : Set where
  field
    precondition : opPrecondition op fs
    reversePrecondition : opPrecondition (reverseOp op) (applyOp op fs)
    defaultPerms : HasDefaultPerms op fs

-- Single operation reversibility (with default-perms constraint)
singleOpReversible : ∀ (op : Operation) (fs : Filesystem) →
  ReversibleDP op fs →
  applyOp (reverseOp op) (applyOp op fs) ≡ fs
singleOpReversible (mkdirOp p) fs rev =
  mkdir-rmdir-reversible p fs (ReversibleDP.precondition rev)
singleOpReversible (rmdirOp p) fs rev with ReversibleDP.defaultPerms rev
... | rmdirPerms refl hperms =
  rmdir-mkdir-reversible p fs (ReversibleDP.precondition rev) hperms
singleOpReversible (createFileOp p) fs rev =
  createFile-deleteFile-reversible p fs (ReversibleDP.precondition rev)
singleOpReversible (deleteFileOp p) fs rev with ReversibleDP.defaultPerms rev
... | deleteFilePerms refl hperms =
  deleteFile-createFile-reversible p fs (ReversibleDP.precondition rev) hperms

-- All operations in sequence are reversible (with default perms)
data AllReversibleDP : List Operation → Filesystem → Set where
  nilReversibleDP : ∀ {fs} → AllReversibleDP [] fs
  consReversibleDP : ∀ {op ops fs} →
    ReversibleDP op fs →
    AllReversibleDP ops (applyOp op fs) →
    AllReversibleDP (op ∷ ops) fs

-- Main composition theorem (with default-perms constraint)
operationSequenceReversible : ∀ (ops : List Operation) (fs : Filesystem) →
  AllReversibleDP ops fs →
  applySequence (reverseSequence ops) (applySequence ops fs) ≡ fs
operationSequenceReversible [] fs nilReversibleDP = refl
operationSequenceReversible (op ∷ ops) fs (consReversibleDP {op} {ops} {fs} rev revRest) =
  let fs' = applyOp op fs
      ih = operationSequenceReversible ops fs' revRest
      single = singleOpReversible op fs rev
  in trans (cong (λ x → applyOp (reverseOp op) x) ih) single

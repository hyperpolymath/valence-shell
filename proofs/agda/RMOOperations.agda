-- SPDX-License-Identifier: MPL-2.0
{-
  Valence Shell - RMO (Remove / Match / Obliterate) operations in Agda

  SCOPE (corrected 2026-11-01).  This module models *logical* erasure only:

    * an over-write pass replaces the modelled byte content of a block with a
      pattern-determined sequence (so content distinctions between blocks of
      equal length are destroyed);
    * the path is removed from the modelled tree (`deleteFile`);
    * the path's block mapping is emptied.

  It says nothing about physical media, controller wear-levelling, caches,
  snapshots or backups, and therefore nothing about physical unrecoverability
  or GDPR compliance.  The audit residue (`sfs-mapping` entries for other
  paths) is itself modelled and remains readable.

  The previous version of this file did not compile: it used hyphenated names
  that do not exist (`delete-file`, `path-exists`, `is-file`), redefined
  `case_of_` several times inside `where` blocks, and nested `with` clauses in a
  layout Agda rejects.  The model below is the same model, restated against
  FilesystemModel/FileOperations.
-}

module RMOOperations where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _/_)
open import Data.List using (List; []; _∷_; length; map)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Properties using (length-map)

open import FilesystemModel
open import FileOperations

-- ============================================================================
-- Storage model
-- ============================================================================

record StorageBlock : Set where
  constructor mkBlock
  field
    blockId : ℕ
    blockData : List ℕ      -- modelled byte values
    overwriteCount : ℕ

Storage : Set
Storage = ℕ → Maybe StorageBlock

BlockMapping : Set
BlockMapping = Path → List ℕ

record StorageFS : Set where
  constructor mkStorageFS
  field
    sfs-tree : Filesystem
    sfs-storage : Storage
    sfs-mapping : BlockMapping

-- ============================================================================
-- Overwrite patterns
-- ============================================================================

data OverwritePattern : Set where
  pattern-zeros : OverwritePattern
  pattern-ones : OverwritePattern
  pattern-random : ℕ → OverwritePattern  -- seed
  pattern-55 : OverwritePattern
  pattern-AA : OverwritePattern

-- Positions from n - 1 down to 0; zero gives an empty list.
indices : ℕ → List ℕ
indices zero = []
indices (suc n) = n ∷ indices n

_mod_ : ℕ → ℕ → ℕ
n mod zero = 0
n mod suc m = n ∸ ((n / suc m) * suc m)

-- Return the pattern's value at a position. The random pattern is deterministic
-- for a given seed and position and yields values modulo 256.
byte : OverwritePattern → ℕ → ℕ
byte pattern-zeros _ = 0
byte pattern-ones _ = 255
byte (pattern-random seed) pos = (seed * 1103515245 + 12345 + pos) mod 256
byte pattern-55 _ = 85
byte pattern-AA _ = 170

-- DoD 5220.22-M / Gutmann-style pattern sequences (as data, not as claims)
dod-patterns : List OverwritePattern
dod-patterns = pattern-zeros ∷ pattern-ones ∷ pattern-random 42 ∷ []

gutmann-patterns : List OverwritePattern
gutmann-patterns =
  pattern-random 1 ∷ pattern-random 2 ∷ pattern-random 3 ∷ pattern-random 4 ∷
  pattern-55 ∷ pattern-AA ∷ pattern-zeros ∷ pattern-ones ∷ []

-- ============================================================================
-- Overwriting
-- ============================================================================

-- Replace the block content with a pattern-determined sequence of the same
-- length and increment its overwrite count.
overwrite-block : StorageBlock → OverwritePattern → StorageBlock
overwrite-block blk pat = record blk
  { blockData = map (byte pat) (indices (length (StorageBlock.blockData blk)))
  ; overwriteCount = suc (StorageBlock.overwriteCount blk)
  }

overwriteAt : OverwritePattern → Maybe StorageBlock → Maybe StorageBlock
overwriteAt pat nothing = nothing
overwriteAt pat (just blk) = just (overwrite-block blk pat)

_∨_ : Bool → Bool → Bool
true ∨ _ = true
false ∨ y = y

_≡b_ : ℕ → ℕ → Bool
zero ≡b zero = true
zero ≡b suc _ = false
suc _ ≡b zero = false
suc a ≡b suc b = a ≡b b

-- Membership of a block id in a mapping list, as a Bool
_∈b_ : ℕ → List ℕ → Bool
n ∈b [] = false
n ∈b (x ∷ xs) = (n ≡b x) ∨ (n ∈b xs)

-- Overwrite existing blocks mapped to a path; missing blocks remain absent.
-- A block shared with another path is also changed for that path.
overwrite-mapped : Path → OverwritePattern → StorageFS → StorageFS
overwrite-mapped p pat sfs = record sfs
  { sfs-storage = λ bid →
      if bid ∈b (StorageFS.sfs-mapping sfs p)
      then overwriteAt pat (StorageFS.sfs-storage sfs bid)
      else StorageFS.sfs-storage sfs bid
  }

-- Apply the patterns in order; an empty list leaves storage unchanged.
multi-pass-overwrite : Path → List OverwritePattern → StorageFS → StorageFS
multi-pass-overwrite p [] sfs = sfs
multi-pass-overwrite p (pat ∷ pats) sfs =
  multi-pass-overwrite p pats (overwrite-mapped p pat sfs)

-- Remove the block mapping for a path
remove-mapping : Path → BlockMapping → BlockMapping
remove-mapping p m p' with p path-≟ p'
... | yes _ = []
... | no _ = m p'

-- Overwrite mapped blocks in pattern order, then remove the path and mapping.
-- An empty pattern list still removes the path and mapping without overwriting.
-- With a non-empty pattern list, shared blocks are overwritten too. This models
-- logical rather than physical erasure.
obliterate : Path → List OverwritePattern → StorageFS → StorageFS
obliterate p pats sfs = record sfs'
  { sfs-tree = deleteFile p (StorageFS.sfs-tree sfs')
  ; sfs-mapping = remove-mapping p (StorageFS.sfs-mapping sfs)
  }
  where
    sfs' = multi-pass-overwrite p pats sfs

-- ============================================================================
-- What "no trace" means here (logical, not physical)
-- ============================================================================

-- The path is gone from the modelled tree and its block mapping is empty.
-- Nothing in this definition mentions physical media: see the module note.
no-logical-trace-remains : Path → StorageFS → Set
no-logical-trace-remains p sfs =
  (¬ pathExists p (StorageFS.sfs-tree sfs)) ×
  (StorageFS.sfs-mapping sfs p ≡ [])

-- ============================================================================
-- Lemmas about the tree component
-- ============================================================================

overwrite-mapped-tree : ∀ p pat sfs →
  StorageFS.sfs-tree (overwrite-mapped p pat sfs) ≡ StorageFS.sfs-tree sfs
overwrite-mapped-tree p pat sfs = refl

multi-pass-tree : ∀ p pats sfs →
  StorageFS.sfs-tree (multi-pass-overwrite p pats sfs) ≡ StorageFS.sfs-tree sfs
multi-pass-tree p [] sfs = refl
multi-pass-tree p (pat ∷ pats) sfs =
  trans (multi-pass-tree p pats (overwrite-mapped p pat sfs))
        (overwrite-mapped-tree p pat sfs)

remove-mapping-at : ∀ p m → remove-mapping p m p ≡ []
remove-mapping-at p m with p path-≟ p
... | yes _ = refl
... | no p≢p = ⊥-elim (p≢p refl)

deleteFile-other : ∀ p p' fs → ¬ (p ≡ p') → deleteFile p fs p' ≡ fs p'
deleteFile-other p p' fs p≢p' = fsUpdate-other p p' nothing fs p≢p'

-- After deleteFile, the path is absent
deleteFile-removes : ∀ p fs → ¬ pathExists p (deleteFile p fs)
deleteFile-removes p fs (node , eq) = case-split (p path-≟ p)
  where
    case-split : (d : Dec (p ≡ p)) → ⊥
    case-split (no p≢p) = p≢p refl
    case-split (yes _) = nothing≢just (trans (sym (fsUpdate-at p nothing fs)) eq)

-- ============================================================================
-- Theorems
-- ============================================================================

-- After obliteration the path is absent from the tree
obliterate-removes-path : ∀ p pats sfs →
  ¬ pathExists p (StorageFS.sfs-tree (obliterate p pats sfs))
obliterate-removes-path p pats sfs =
  deleteFile-removes p (StorageFS.sfs-tree (multi-pass-overwrite p pats sfs))

-- After obliteration the path has no blocks mapped
obliterate-removes-mapping : ∀ p pats sfs →
  StorageFS.sfs-mapping (obliterate p pats sfs) p ≡ []
obliterate-removes-mapping p pats sfs = remove-mapping-at p (StorageFS.sfs-mapping sfs)

-- Obliteration leaves no *logical* trace (see the module note)
obliterate-leaves-no-logical-trace : ∀ p pats sfs →
  no-logical-trace-remains p (obliterate p pats sfs)
obliterate-leaves-no-logical-trace p pats sfs =
  obliterate-removes-path p pats sfs , obliterate-removes-mapping p pats sfs

-- Obliteration preserves unrelated paths
obliterate-preserves-other-paths : ∀ p p' pats sfs →
  ¬ (p ≡ p') →
  pathExists p' (StorageFS.sfs-tree sfs) →
  pathExists p' (StorageFS.sfs-tree (obliterate p pats sfs))
obliterate-preserves-other-paths p p' pats sfs p≢p' (node , h) =
  node , goal
  where
    tree' : Filesystem
    tree' = StorageFS.sfs-tree (multi-pass-overwrite p pats sfs)

    h' : tree' p' ≡ just node
    h' = trans (cong (λ fs → fs p') (multi-pass-tree p pats sfs)) h

    goal : StorageFS.sfs-tree (obliterate p pats sfs) p' ≡ just node
    goal = trans (deleteFile-other p p' tree' p≢p') h'

-- ============================================================================
-- What overwriting does to content
-- ============================================================================

length-indices : ∀ n → length (indices n) ≡ n
length-indices zero = refl
length-indices (suc n) = cong suc (length-indices n)

-- The new content depends only on the pattern and the *length* of the old
overwrite-content : ∀ blk pat →
  StorageBlock.blockData (overwrite-block blk pat) ≡
  map (byte pat) (indices (length (StorageBlock.blockData blk)))
overwrite-content blk pat = refl

-- Overwriting preserves the block identity and increments the counter
overwrite-id : ∀ blk pat → StorageBlock.blockId (overwrite-block blk pat) ≡ StorageBlock.blockId blk
overwrite-id blk pat = refl

overwrite-count : ∀ blk pat →
  StorageBlock.overwriteCount (overwrite-block blk pat) ≡ suc (StorageBlock.overwriteCount blk)
overwrite-count blk pat = refl

-- ... and preserves the (modelled) data length
overwrite-length : ∀ blk pat →
  length (StorageBlock.blockData (overwrite-block blk pat)) ≡
  length (StorageBlock.blockData blk)
overwrite-length blk pat =
  trans (length-map (byte pat) (indices (length (StorageBlock.blockData blk))))
        (length-indices (length (StorageBlock.blockData blk)))

-- Two blocks of equal length have equal content after the same pattern:
-- the original bytes are not observable afterwards.
overwrite-equalizes : ∀ blk1 blk2 pat →
  length (StorageBlock.blockData blk1) ≡ length (StorageBlock.blockData blk2) →
  StorageBlock.blockData (overwrite-block blk1 pat) ≡
  StorageBlock.blockData (overwrite-block blk2 pat)
overwrite-equalizes blk1 blk2 pat h =
  trans (overwrite-content blk1 pat)
        (trans (cong (λ n → map (byte pat) (indices n)) h)
               (sym (overwrite-content blk2 pat)))

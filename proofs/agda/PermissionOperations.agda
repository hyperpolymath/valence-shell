{- SPDX-License-Identifier: MPL-2.0 -}
{- Valence Shell - Permission Operations (Agda)

   Formalizes chmod and chown as reversible operations.
   Proves that applying the old permission/ownership after a change
   restores the original filesystem state.
-}

module PermissionOperations where

open import FilesystemModel
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

-- ============================================================================
-- Extended Types for Permission/Ownership
-- ============================================================================

-- Unix permission mode (lower 12 bits of mode_t)
Mode : Set
Mode = ℕ

-- Unix user/group IDs
record Ownership : Set where
  constructor mkOwnership
  field
    uid : ℕ
    gid : ℕ

-- Extended filesystem node with separate mode and ownership
record FSNodeExt : Set where
  constructor mkFSNodeExt
  field
    nodeType : FSNodeType
    mode : Mode
    owner : Ownership

-- Extended filesystem
FilesystemExt : Set
FilesystemExt = Path → Maybe FSNodeExt

-- Path decidable equality (reuse from FilesystemModel)
_pathExt-≟_ : (p₁ p₂ : Path) → Dec (p₁ ≡ p₂)
_pathExt-≟_ = _path-≟_

-- Point update for extended filesystem
fsUpdateExt : Path → Maybe FSNodeExt → FilesystemExt → FilesystemExt
fsUpdateExt p n fs p' with p pathExt-≟ p'
... | yes _ = n
... | no _ = fs p'

-- ============================================================================
-- Node-level setters
-- ============================================================================
--
-- NOTE (2026-11-01): the original definitions of chmod/chown used a nested
-- `with` inside a `with` clause (`... | yes _ with fs p'`).  Agda rejects that
-- layout outright ("Could not parse the left-hand side"), so the node surgery
-- is factored out into total functions on `Maybe FSNodeExt`.  This is a
-- presentational change: the model is unchanged.

applyMode : Mode → Maybe FSNodeExt → Maybe FSNodeExt
applyMode m nothing = nothing
applyMode m (just node) =
  just (mkFSNodeExt (FSNodeExt.nodeType node) m (FSNodeExt.owner node))

applyOwner : Ownership → Maybe FSNodeExt → Maybe FSNodeExt
applyOwner o nothing = nothing
applyOwner o (just node) =
  just (mkFSNodeExt (FSNodeExt.nodeType node) (FSNodeExt.mode node) o)

-- ============================================================================
-- chmod Operation
-- ============================================================================

-- chmod precondition: path must exist
ChmodPrecondition : Path → FilesystemExt → Set
ChmodPrecondition p fs = ∃ λ node → fs p ≡ just node

-- Change the mode of the node at the path, if present. Other paths are unchanged.
chmod : Path → Mode → FilesystemExt → FilesystemExt
chmod p newMode fs p' with p pathExt-≟ p'
... | yes _ = applyMode newMode (fs p')
... | no _ = fs p'

-- Value of chmod at the modified path
chmod-at : ∀ p m fs → chmod p m fs p ≡ applyMode m (fs p)
chmod-at p m fs with p pathExt-≟ p
... | yes _ = refl
... | no p≢p = ⊥-elim (p≢p refl)

-- Value of chmod at any other path
chmod-other : ∀ p p' m fs → ¬ (p ≡ p') → chmod p m fs p' ≡ fs p'
chmod-other p p' m fs p≢p' with p pathExt-≟ p'
... | yes p≡p' = ⊥-elim (p≢p' p≡p')
... | no _ = refl

-- ============================================================================
-- chmod Theorems
-- ============================================================================

-- chmod is reversible — restoring old mode restores fs
chmod-reversible : ∀ p fs oldMode newMode →
  (hold : ∃ λ node → (fs p ≡ just node) × (FSNodeExt.mode node ≡ oldMode)) →
  chmod p oldMode (chmod p newMode fs) ≡ fs
chmod-reversible p fs oldMode newMode (node , hnode , hmode) = funext helper
  where
    node-modes : Mode → FSNodeExt
    node-modes m = mkFSNodeExt (FSNodeExt.nodeType node) m (FSNodeExt.owner node)

    helper : ∀ p' → chmod p oldMode (chmod p newMode fs) p' ≡ fs p'
    helper p' = case-split (p pathExt-≟ p')
      where
        case-split : Dec (p ≡ p') → chmod p oldMode (chmod p newMode fs) p' ≡ fs p'
        case-split (no p≢p') =
            trans (chmod-other p p' oldMode (chmod p newMode fs) p≢p')
                  (chmod-other p p' newMode fs p≢p')
        case-split (yes refl) =
            trans (trans (chmod-at p oldMode (chmod p newMode fs)) (cong (applyMode oldMode) applied))
                  (trans (sym (cong just (cong node-modes hmode))) (sym hnode))
          where
            applied : chmod p newMode fs p ≡ just (node-modes newMode)
            applied = trans (chmod-at p newMode fs) (cong (applyMode newMode) hnode)

-- chmod to same mode is identity
chmod-same-mode : ∀ p fs m →
  (hold : ∃ λ node → (fs p ≡ just node) × (FSNodeExt.mode node ≡ m)) →
  chmod p m fs ≡ fs
chmod-same-mode p fs m (node , hnode , hmode) = funext helper
  where
    node-modes : Mode → FSNodeExt
    node-modes md = mkFSNodeExt (FSNodeExt.nodeType node) md (FSNodeExt.owner node)

    helper : ∀ p' → chmod p m fs p' ≡ fs p'
    helper p' = case-split (p pathExt-≟ p')
      where
        case-split : Dec (p ≡ p') → chmod p m fs p' ≡ fs p'
        case-split (no p≢p') = chmod-other p p' m fs p≢p'
        case-split (yes refl) =
            trans (trans (chmod-at p m fs) (cong (applyMode m) hnode))
                  (trans (sym (cong just (cong node-modes hmode))) (sym hnode))

-- chmod preserves other paths
chmod-preserves-other : ∀ p₁ p₂ fs m →
  ¬ (p₁ ≡ p₂) →
  chmod p₁ m fs p₂ ≡ fs p₂
chmod-preserves-other = λ p₁ p₂ fs m hneq → chmod-other p₁ p₂ m fs hneq

-- ============================================================================
-- chown Operation
-- ============================================================================

-- chown precondition: path must exist
ChownPrecondition : Path → FilesystemExt → Set
ChownPrecondition p fs = ∃ λ node → fs p ≡ just node

-- Change the ownership of the node at the path, if present. Other paths are unchanged.
chown : Path → Ownership → FilesystemExt → FilesystemExt
chown p newOwner fs p' with p pathExt-≟ p'
... | yes _ = applyOwner newOwner (fs p')
... | no _ = fs p'

-- Value of chown at the modified path
chown-at : ∀ p o fs → chown p o fs p ≡ applyOwner o (fs p)
chown-at p o fs with p pathExt-≟ p
... | yes _ = refl
... | no p≢p = ⊥-elim (p≢p refl)

-- Value of chown at any other path
chown-other : ∀ p p' o fs → ¬ (p ≡ p') → chown p o fs p' ≡ fs p'
chown-other p p' o fs p≢p' with p pathExt-≟ p'
... | yes p≡p' = ⊥-elim (p≢p' p≡p')
... | no _ = refl

-- ============================================================================
-- chown Theorems
-- ============================================================================

-- chown is reversible — restoring old owner restores fs
chown-reversible : ∀ p fs oldOwner newOwner →
  (hold : ∃ λ node → (fs p ≡ just node) × (FSNodeExt.owner node ≡ oldOwner)) →
  chown p oldOwner (chown p newOwner fs) ≡ fs
chown-reversible p fs oldOwner newOwner (node , hnode , howner) = funext helper
  where
    node-owners : Ownership → FSNodeExt
    node-owners o = mkFSNodeExt (FSNodeExt.nodeType node) (FSNodeExt.mode node) o

    helper : ∀ p' → chown p oldOwner (chown p newOwner fs) p' ≡ fs p'
    helper p' = case-split (p pathExt-≟ p')
      where
        case-split : Dec (p ≡ p') → chown p oldOwner (chown p newOwner fs) p' ≡ fs p'
        case-split (no p≢p') =
            trans (chown-other p p' oldOwner (chown p newOwner fs) p≢p')
                  (chown-other p p' newOwner fs p≢p')
        case-split (yes refl) =
            trans (trans (chown-at p oldOwner (chown p newOwner fs)) (cong (applyOwner oldOwner) applied))
                  (trans (sym (cong just (cong node-owners howner))) (sym hnode))
          where
            applied : chown p newOwner fs p ≡ just (node-owners newOwner)
            applied = trans (chown-at p newOwner fs) (cong (applyOwner newOwner) hnode)

-- chown to same owner is identity
chown-same-owner : ∀ p fs o →
  (hold : ∃ λ node → (fs p ≡ just node) × (FSNodeExt.owner node ≡ o)) →
  chown p o fs ≡ fs
chown-same-owner p fs o (node , hnode , howner) = funext helper
  where
    node-owners : Ownership → FSNodeExt
    node-owners ow = mkFSNodeExt (FSNodeExt.nodeType node) (FSNodeExt.mode node) ow

    helper : ∀ p' → chown p o fs p' ≡ fs p'
    helper p' = case-split (p pathExt-≟ p')
      where
        case-split : Dec (p ≡ p') → chown p o fs p' ≡ fs p'
        case-split (no p≢p') = chown-other p p' o fs p≢p'
        case-split (yes refl) =
            trans (trans (chown-at p o fs) (cong (applyOwner o) hnode))
                  (trans (sym (cong just (cong node-owners howner))) (sym hnode))

-- chown preserves other paths
chown-preserves-other : ∀ p₁ p₂ fs o →
  ¬ (p₁ ≡ p₂) →
  chown p₁ o fs p₂ ≡ fs p₂
chown-preserves-other = λ p₁ p₂ fs o hneq → chown-other p₁ p₂ o fs hneq

{-
  Summary of Proven Claims:

  ✓ chmod-reversible — chmod(old, chmod(new, fs)) = fs
  ✓ chmod-same-mode — chmod with same mode is identity
  ✓ chmod-preserves-other — chmod preserves unrelated paths
  ✓ chown-reversible — chown(old, chown(new, fs)) = fs
  ✓ chown-same-owner — chown with same owner is identity
  ✓ chown-preserves-other — chown preserves unrelated paths
-}

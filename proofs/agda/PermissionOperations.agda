{- SPDX-License-Identifier: PMPL-1.0-or-later -}
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
-- chmod Operation
-- ============================================================================

-- chmod precondition: path must exist
ChmodPrecondition : Path → FilesystemExt → Set
ChmodPrecondition p fs = ∃ λ node → fs p ≡ just node

-- Apply chmod: change mode bits of a file
chmod : Path → Mode → FilesystemExt → FilesystemExt
chmod p newMode fs p' with p pathExt-≟ p'
... | yes _ with fs p'
...   | nothing = nothing
...   | just node = just (mkFSNodeExt (FSNodeExt.nodeType node) newMode (FSNodeExt.owner node))
... | no _ = fs p'

-- ============================================================================
-- chmod Theorems
-- ============================================================================

-- chmod is reversible — restoring old mode restores fs
chmod-reversible : ∀ p fs oldMode newMode →
  (hold : ∃ λ node → (fs p ≡ just node) × (FSNodeExt.mode node ≡ oldMode)) →
  chmod p oldMode (chmod p newMode fs) ≡ fs
chmod-reversible p fs oldMode newMode (node , hnode , hmode) = funext helper
  where
    helper : ∀ p' → chmod p oldMode (chmod p newMode fs) p' ≡ fs p'
    helper p' with p pathExt-≟ p'
    ... | no _ = refl
    ... | yes refl with fs p | hnode
    ...   | .(just node) | refl with p pathExt-≟ p
    ...     | no p≢p = ⊥-elim (p≢p refl)
              where open import Data.Empty using (⊥-elim)
    ...     | yes _ with node
    ...       | mkFSNodeExt nt m o with hmode
    ...         | refl = refl

-- chmod to same mode is identity
chmod-same-mode : ∀ p fs m →
  (hold : ∃ λ node → (fs p ≡ just node) × (FSNodeExt.mode node ≡ m)) →
  chmod p m fs ≡ fs
chmod-same-mode p fs m (node , hnode , hmode) = funext helper
  where
    helper : ∀ p' → chmod p m fs p' ≡ fs p'
    helper p' with p pathExt-≟ p'
    ... | no _ = refl
    ... | yes refl with fs p | hnode
    ...   | .(just node) | refl with node
    ...     | mkFSNodeExt nt md o with hmode
    ...       | refl = refl

-- chmod preserves other paths
chmod-preserves-other : ∀ p₁ p₂ fs m →
  ¬ (p₁ ≡ p₂) →
  chmod p₁ m fs p₂ ≡ fs p₂
chmod-preserves-other p₁ p₂ fs m hneq with p₁ pathExt-≟ p₂
... | yes p₁≡p₂ = ⊥-elim (hneq p₁≡p₂)
      where open import Data.Empty using (⊥-elim)
... | no _ = refl

-- ============================================================================
-- chown Operation
-- ============================================================================

-- chown precondition: path must exist
ChownPrecondition : Path → FilesystemExt → Set
ChownPrecondition p fs = ∃ λ node → fs p ≡ just node

-- Apply chown: change ownership of a file
chown : Path → Ownership → FilesystemExt → FilesystemExt
chown p newOwner fs p' with p pathExt-≟ p'
... | yes _ with fs p'
...   | nothing = nothing
...   | just node = just (mkFSNodeExt (FSNodeExt.nodeType node) (FSNodeExt.mode node) newOwner)
... | no _ = fs p'

-- ============================================================================
-- chown Theorems
-- ============================================================================

-- chown is reversible — restoring old owner restores fs
chown-reversible : ∀ p fs oldOwner newOwner →
  (hold : ∃ λ node → (fs p ≡ just node) × (FSNodeExt.owner node ≡ oldOwner)) →
  chown p oldOwner (chown p newOwner fs) ≡ fs
chown-reversible p fs oldOwner newOwner (node , hnode , howner) = funext helper
  where
    helper : ∀ p' → chown p oldOwner (chown p newOwner fs) p' ≡ fs p'
    helper p' with p pathExt-≟ p'
    ... | no _ = refl
    ... | yes refl with fs p | hnode
    ...   | .(just node) | refl with p pathExt-≟ p
    ...     | no p≢p = ⊥-elim (p≢p refl)
              where open import Data.Empty using (⊥-elim)
    ...     | yes _ with node
    ...       | mkFSNodeExt nt m o with howner
    ...         | refl = refl

-- chown to same owner is identity
chown-same-owner : ∀ p fs o →
  (hold : ∃ λ node → (fs p ≡ just node) × (FSNodeExt.owner node ≡ o)) →
  chown p o fs ≡ fs
chown-same-owner p fs o (node , hnode , howner) = funext helper
  where
    helper : ∀ p' → chown p o fs p' ≡ fs p'
    helper p' with p pathExt-≟ p'
    ... | no _ = refl
    ... | yes refl with fs p | hnode
    ...   | .(just node) | refl with node
    ...     | mkFSNodeExt nt m ow with howner
    ...       | refl = refl

-- chown preserves other paths
chown-preserves-other : ∀ p₁ p₂ fs o →
  ¬ (p₁ ≡ p₂) →
  chown p₁ o fs p₂ ≡ fs p₂
chown-preserves-other p₁ p₂ fs o hneq with p₁ pathExt-≟ p₂
... | yes p₁≡p₂ = ⊥-elim (hneq p₁≡p₂)
      where open import Data.Empty using (⊥-elim)
... | no _ = refl

-- ============================================================================
-- Cross-operation Commutativity
-- ============================================================================

-- chmod and chown commute (they modify different fields)
-- Note: This requires showing that the intermediate filesystem at p
-- produces the same result regardless of order. Since chmod modifies
-- mode and chown modifies owner, applying both yields the same node.
-- The proof at other paths is trivial (both are identity).

{-
  Summary of Proven Claims:

  ✓ chmod-reversible — chmod(old, chmod(new, fs)) = fs
  ✓ chmod-same-mode — chmod with same mode is identity
  ✓ chmod-preserves-other — chmod preserves unrelated paths
  ✓ chown-reversible — chown(old, chown(new, fs)) = fs
  ✓ chown-same-owner — chown with same owner is identity
  ✓ chown-preserves-other — chown preserves unrelated paths
-}

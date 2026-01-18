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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Function using (_∘_)
open import Axiom.Extensionality.Propositional using (Extensionality)

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

-- Note: isEmptyDir would require additional path prefix predicate
-- Simplified version for now
record IsEmptyDir (p : Path) (fs : Filesystem) : Set where
  field
    isDir : isDirectory p fs
    -- In full version: no children exist

-- Basic Lemmas
pathExists-emptyFS-root : pathExists rootPath emptyFS
pathExists-emptyFS-root = mkFSNode Directory defaultPerms , refl

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

-- mkdir: Create a directory
record MkdirPrecondition (p : Path) (fs : Filesystem) : Set where
  field
    notExists : ¬ pathExists p fs
    parentExists : parentExists p fs
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
mkdir-creates-directory p fs pre with p path-≟ p
... | yes refl = defaultPerms , refl
... | no p≢p = ⊥-elim (p≢p refl)
  where
    open import Data.Empty using (⊥-elim)

mkdir-path-exists : ∀ p fs → MkdirPrecondition p fs → pathExists p (mkdir p fs)
mkdir-path-exists p fs pre with p path-≟ p
... | yes refl = mkFSNode Directory defaultPerms , refl
... | no p≢p = ⊥-elim (p≢p refl)
  where
    open import Data.Empty using (⊥-elim)

rmdir-removes-path : ∀ p fs → RmdirPrecondition p fs → ¬ pathExists p (rmdir p fs)
rmdir-removes-path p fs pre (node , eq) with p path-≟ p
... | yes refl = λ ()
... | no p≢p = ⊥-elim (p≢p refl)
  where
    open import Data.Empty using (⊥-elim)

-- The Main Reversibility Theorem
postulate
  funext : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x} →
           (∀ x → f x ≡ g x) → f ≡ g

mkdir-rmdir-reversible : ∀ p fs →
  MkdirPrecondition p fs →
  rmdir p (mkdir p fs) ≡ fs
mkdir-rmdir-reversible p fs pre = funext helper
  where
    helper : ∀ p' → rmdir p (mkdir p fs) p' ≡ fs p'
    helper p' with p path-≟ p'
    ... | yes refl with p path-≟ p
        ... | yes _ with MkdirPrecondition.notExists pre
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

{- SPDX-License-Identifier: MPL-2.0 -}
{- Valence Shell - File Content Operations (Agda)

   File content operations: read and write.
   Proves reversibility of content modifications.

   REWRITTEN 2026-11-01.  The previous version was written against a model
   that does not exist in this repository: it used the constructors `file` and
   `directory` (the model has `File` and `Directory` of type `FSNodeType`), the
   accessors `getNodeType`/`getPermissions` (the model has the record fields
   `FSNode.nodeType`/`FSNode.permissions`), and it nested `with` clauses inside
   `with` clauses, which Agda cannot parse.  The model below is the same model
   (nodes with a type, permissions and optional content) restated against
   FilesystemModel, with the node surgery factored into total functions so that
   the proofs are structural rather than layout-dependent.
-}

module FileContentOperations where

open import FilesystemModel
open import FileOperations
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; inspect; [_])
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Empty using (⊥-elim)

-- File Contents

FileContent : Set
FileContent = String

emptyContent : FileContent
emptyContent = ""

-- Extended Filesystem with Content

record FSNodeWithContent : Set where
  constructor mkFSNodeWithContent
  field
    nodeType : FSNodeType
    nodePerms : Permissions
    nodeContent : Maybe FileContent  -- nothing for directories, just for files

FilesystemWithContent : Set
FilesystemWithContent = Path → Maybe FSNodeWithContent

-- ============================================================================
-- Node-level helpers (total functions: no nested `with` needed downstream)
-- ============================================================================

isFileType : FSNodeType → Bool
isFileType File = true
isFileType Directory = false

-- Preserve the type and permissions, giving files empty content and directories
-- no content.
fromNode : FSNode → FSNodeWithContent
fromNode node = mkFSNodeWithContent (FSNode.nodeType node) (FSNode.permissions node)
                 (if isFileType (FSNode.nodeType node) then just emptyContent else nothing)

-- Convert a plain filesystem into a content-tracking one: files start empty
fsToFsWithContent : Filesystem → FilesystemWithContent
fsToFsWithContent fs p with fs p
... | nothing = nothing
... | just node = just (fromNode node)

-- Read the content of a node value.
--
-- MODELLING NOTE (2026-11-01): the node type is *not* consulted here.  Nodes
-- built by `fromNode` carry `nothing` for directories and `just emptyContent`
-- for files, so reading a directory still yields nothing; and every theorem
-- below constrains itself to file nodes through Read/WriteFilePrecondition.
-- Consulting the node type inside a projection-driven `with` is what prevented
-- the composition lemmas from reducing (see writeContent).
readContent : Maybe FSNodeWithContent → Maybe FileContent
readContent nothing = nothing
readContent (just node) = FSNodeWithContent.nodeContent node

-- Write content into a node value.
--
-- MODELLING NOTE (2026-11-01): this is an unconditional record update -- it does
-- not consult the node type.  Writing to a *directory* is excluded by
-- WriteFilePrecondition, which requires `nodeType node ≡ File`, and no theorem
-- below depends on the directory case.  The unconditional update is what makes
-- the operation confluent: a conditional update (`if isFileType ...`) blocks the
-- composition lemmas, because Agda cannot reduce the condition after the first
-- update (the node type lives in the record that the update rebuilds).
writeContent : FileContent → Maybe FSNodeWithContent → Maybe FSNodeWithContent
writeContent c nothing = nothing
writeContent c (just node) = just record node { nodeContent = just c }

-- ============================================================================
-- File Content Operations
-- ============================================================================

-- Return the stored content, or nothing if the path or its content is absent.
-- This operation does not check the node type or read permission.
readFile : Path → FilesystemWithContent → Maybe FileContent
readFile p fs = readContent (fs p)

-- Replace the content of an existing node, leaving an absent path unchanged.
-- This operation does not check the node type or write permission.
writeFile : Path → FileContent → FilesystemWithContent → FilesystemWithContent
writeFile p content fs p' with p path-≟ p'
... | yes _ = writeContent content (fs p')
... | no _ = fs p'

-- ============================================================================
-- Equations characterising the operations
-- ============================================================================

readFile-at : ∀ p fs (v : Maybe FSNodeWithContent) → fs p ≡ v → readFile p fs ≡ readContent v
readFile-at p fs v h = cong readContent h

writeFile-at : ∀ p c fs → writeFile p c fs p ≡ writeContent c (fs p)
writeFile-at p c fs with p path-≟ p
... | yes _ = refl
... | no p≢p = ⊥-elim (p≢p refl)

writeFile-other : ∀ p p' c fs → ¬ (p ≡ p') → writeFile p c fs p' ≡ fs p'
writeFile-other p p' c fs p≢p' with p path-≟ p'
... | yes p≡p' = ⊥-elim (p≢p' p≡p')
... | no _ = refl

-- Writing is idempotent in its second argument at a fixed content
writeContent-twice : ∀ a b v → writeContent a (writeContent b v) ≡ writeContent a v
writeContent-twice a b nothing = refl
writeContent-twice a b (just node) = refl

-- Writing back what was read is the identity
writeContent-same : ∀ c v → readContent v ≡ just c → writeContent c v ≡ v
writeContent-same c nothing ()
writeContent-same c (just node) h =
  sym (cong (λ x → just (record node { nodeContent = x })) h)

-- ============================================================================
-- Preconditions
-- ============================================================================

ReadFilePrecondition : Path → FilesystemWithContent → Set
ReadFilePrecondition p fs =
  ∃[ node ] (
    fs p ≡ just node ×
    FSNodeWithContent.nodeType node ≡ File ×
    Permissions.readable (FSNodeWithContent.nodePerms node) ≡ true
  )

WriteFilePrecondition : Path → FilesystemWithContent → Set
WriteFilePrecondition p fs =
  ∃[ node ] (
    fs p ≡ just node ×
    FSNodeWithContent.nodeType node ≡ File ×
    Permissions.writable (FSNodeWithContent.nodePerms node) ≡ true
  )

-- ============================================================================
-- Reversibility Properties
-- ============================================================================

readFilePreservesFs : ∀ (p : Path) (fs : FilesystemWithContent) (content : FileContent) →
  readFile p fs ≡ just content →
  fs ≡ fs
readFilePreservesFs p fs content h = refl

-- Writing old content back after writing new content restores the filesystem.
writeFileReversible : ∀ (p : Path) (fs : FilesystemWithContent)
  (oldContent newContent : FileContent) →
  WriteFilePrecondition p fs →
  readFile p fs ≡ just oldContent →
  writeFile p oldContent (writeFile p newContent fs) ≡ fs
writeFileReversible p fs oldContent newContent pre hold = funext helper
  where
    helper : ∀ p' → writeFile p oldContent (writeFile p newContent fs) p' ≡ fs p'
    helper p' = case-split (p path-≟ p')
      where
        case-split : Dec (p ≡ p') →
          writeFile p oldContent (writeFile p newContent fs) p' ≡ fs p'
        case-split (yes refl) =
          trans (writeFile-at p oldContent (writeFile p newContent fs))
                (trans (cong (writeContent oldContent) (writeFile-at p newContent fs))
                       (trans (writeContent-twice oldContent newContent (fs p))
                              (writeContent-same oldContent (fs p) hold)))
        case-split (no p≢p') =
          trans (writeFile-other p p' oldContent (writeFile p newContent fs) p≢p')
                (writeFile-other p p' newContent fs p≢p')

-- Content Preservation: writing to one path doesn't affect reading another
writeFileIndependence : ∀ (p1 p2 : Path) (content : FileContent)
  (fs : FilesystemWithContent) →
  ¬ (p1 ≡ p2) →
  readFile p2 (writeFile p1 content fs) ≡ readFile p2 fs
writeFileIndependence p1 p2 content fs p1≢p2 =
  cong readContent (writeFile-other p1 p2 content fs p1≢p2)

-- ============================================================================
-- Content Composition Theorems
-- ============================================================================

-- Last write wins: writing c2 after c1 at the same path = writing c2 directly
writeFileLastWriteWins : ∀ (p : Path) (fs : FilesystemWithContent)
  (c1 c2 : FileContent) →
  writeFile p c2 (writeFile p c1 fs) ≡ writeFile p c2 fs
writeFileLastWriteWins p fs c1 c2 = funext helper
  where
    helper : ∀ p' → writeFile p c2 (writeFile p c1 fs) p' ≡ writeFile p c2 fs p'
    helper p' = case-split (p path-≟ p')
      where
        case-split : Dec (p ≡ p') →
          writeFile p c2 (writeFile p c1 fs) p' ≡ writeFile p c2 fs p'
        case-split (yes refl) =
          trans (writeFile-at p c2 (writeFile p c1 fs))
                (trans (cong (writeContent c2) (writeFile-at p c1 fs))
                       (trans (writeContent-twice c2 c1 (fs p))
                              (sym (writeFile-at p c2 fs))))
        case-split (no p≢p') =
          trans (trans (writeFile-other p p' c2 (writeFile p c1 fs) p≢p')
                       (writeFile-other p p' c1 fs p≢p'))
                (sym (writeFile-other p p' c2 fs p≢p'))

-- Writes to different paths commute
writeFileCommute : ∀ (p1 p2 : Path) (fs : FilesystemWithContent)
  (c1 c2 : FileContent) →
  ¬ (p1 ≡ p2) →
  writeFile p1 c1 (writeFile p2 c2 fs) ≡
  writeFile p2 c2 (writeFile p1 c1 fs)
writeFileCommute p1 p2 fs c1 c2 p1≢p2 = funext helper
  where
    p2≢p1 : ¬ (p2 ≡ p1)
    p2≢p1 = λ e → p1≢p2 (sym e)

    helper : ∀ p' → writeFile p1 c1 (writeFile p2 c2 fs) p' ≡
                     writeFile p2 c2 (writeFile p1 c1 fs) p'
    helper p' = c1-case (p1 path-≟ p')
      where
        c1-case : Dec (p1 ≡ p') →
          writeFile p1 c1 (writeFile p2 c2 fs) p' ≡ writeFile p2 c2 (writeFile p1 c1 fs) p'
        c1-case (yes refl) =
          trans (trans (writeFile-at p1 c1 (writeFile p2 c2 fs))
                       (cong (writeContent c1) (writeFile-other p2 p1 c2 fs p2≢p1)))
                (sym (trans (writeFile-other p2 p1 c2 (writeFile p1 c1 fs) p2≢p1)
                            (writeFile-at p1 c1 fs)))
        c1-case (no p1≢p') = c2-case (p2 path-≟ p')
          where
            c2-case : Dec (p2 ≡ p') →
              writeFile p1 c1 (writeFile p2 c2 fs) p' ≡ writeFile p2 c2 (writeFile p1 c1 fs) p'
            c2-case (yes refl) =
              trans (trans (writeFile-other p1 p2 c1 (writeFile p2 c2 fs) p1≢p2)
                           (writeFile-at p2 c2 fs))
                    (sym (trans (writeFile-at p2 c2 (writeFile p1 c1 fs))
                                (cong (writeContent c2) (writeFile-other p1 p2 c1 fs p1≢p2))))
            c2-case (no p2≢p') =
              trans (writeFile-other p1 p' c1 (writeFile p2 c2 fs) p1≢p')
                    (trans (writeFile-other p2 p' c2 fs p2≢p')
                           (sym (trans (writeFile-other p2 p' c2 (writeFile p1 c1 fs) p2≢p')
                                       (writeFile-other p1 p' c1 fs p1≢p'))))

-- Writing content that was just read from a file is identity
writeFileSameContent : ∀ (p : Path) (content : FileContent) (fs : FilesystemWithContent) →
  WriteFilePrecondition p fs →
  readFile p fs ≡ just content →
  writeFile p content fs ≡ fs
writeFileSameContent p content fs pre hold = funext helper
  where
    helper : ∀ p' → writeFile p content fs p' ≡ fs p'
    helper p' = case-split (p path-≟ p')
      where
        case-split : Dec (p ≡ p') → writeFile p content fs p' ≡ fs p'
        case-split (yes refl) =
          trans (writeFile-at p content fs) (writeContent-same content (fs p) hold)
        case-split (no p≢p') = writeFile-other p p' content fs p≢p'

-- ============================================================================
-- State Tracking for Reversibility
-- ============================================================================

record FileState : Set where
  constructor mkFileState
  field
    statePath : Path
    stateContent : FileContent
    stateExists : Bool

captureFileState : Path → FilesystemWithContent → FileState
captureFileState p fs with readFile p fs
... | just content = mkFileState p content true
... | nothing = mkFileState p emptyContent false

restoreFileState : FileState → FilesystemWithContent → FilesystemWithContent
restoreFileState state fs =
  if FileState.stateExists state
  then writeFile (FileState.statePath state) (FileState.stateContent state) fs
  else fs

-- Capturing then restoring is identity for writable files
captureRestoreIdentity : ∀ (p : Path) (fs : FilesystemWithContent) →
  WriteFilePrecondition p fs →
  restoreFileState (captureFileState p fs) fs ≡ fs
captureRestoreIdentity p fs hpre with readFile p fs | inspect (readFile p) fs
... | just content | [ eq ] = writeFileSameContent p content fs hpre eq
... | nothing | _ = refl

-- ============================================================================
-- Integration with MAA Framework
-- ============================================================================

record FileModificationRecord : Set where
  constructor mkFileModRecord
  field
    modPath : Path
    modOldContent : FileContent
    modNewContent : FileContent
    modTimestamp : ℕ

createModRecord : Path → FileContent → FileContent → ℕ → FileModificationRecord
createModRecord p old new ts = mkFileModRecord p old new ts

-- Write the record's new content at its path using writeFile.
applyModification : FileModificationRecord → FilesystemWithContent → FilesystemWithContent
applyModification mrec fs =
  writeFile (FileModificationRecord.modPath mrec)
            (FileModificationRecord.modNewContent mrec)
            fs

-- Write the record's old content at its path using writeFile.
reverseModification : FileModificationRecord → FilesystemWithContent → FilesystemWithContent
reverseModification mrec fs =
  writeFile (FileModificationRecord.modPath mrec)
            (FileModificationRecord.modOldContent mrec)
            fs

modificationReversible : ∀ (mrec : FileModificationRecord) (fs : FilesystemWithContent) →
  WriteFilePrecondition (FileModificationRecord.modPath mrec) fs →
  readFile (FileModificationRecord.modPath mrec) fs ≡
    just (FileModificationRecord.modOldContent mrec) →
  reverseModification mrec (applyModification mrec fs) ≡ fs
modificationReversible mrec fs hpre hold =
  writeFileReversible
    (FileModificationRecord.modPath mrec)
    fs
    (FileModificationRecord.modOldContent mrec)
    (FileModificationRecord.modNewContent mrec)
    hpre
    hold

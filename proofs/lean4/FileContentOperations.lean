/- Valence Shell - File Content Operations (Lean 4)

   File content operations: read and write
   Proves reversibility of content modifications
   Extends the verified filesystem with content tracking
-/

import FilesystemModel
import FileOperations

-- Type alias for compatibility
abbrev NodeType := FSNodeType

-- Helper functions for FSNode accessors
def getNodeType (n : FSNode) : FSNodeType := n.nodeType
def getPermissions (n : FSNode) : Permissions := n.permissions

-- File Contents

/-- File content represented as String -/
def FileContent := String

/-- Empty content -/
def emptyContent : FileContent := ""

-- Extended Filesystem with Content

/-- Filesystem node with content -/
structure FSNodeWithContent where
  nodeType : NodeType
  nodePerms : Permissions
  nodeContent : Option FileContent  -- None for directories, Some for files

/-- Extended filesystem mapping paths to nodes with content -/
def FilesystemWithContent := Path → Option FSNodeWithContent

-- Conversion Functions

/-- Convert basic filesystem to filesystem with content -/
def fsToFsWithContent (fs : Filesystem) : FilesystemWithContent :=
  fun p =>
    match fs p with
    | none => none
    | some node =>
        some {
          nodeType := node.nodeType,
          nodePerms := node.permissions,
          nodeContent :=
            match node.nodeType with
            | .file => some emptyContent
            | .directory => none
        }

-- File Content Operations

/-- Read file content -/
def readFile (p : Path) (fs : FilesystemWithContent) : Option FileContent :=
  match fs p with
  | none => none  -- File doesn't exist
  | some node =>
      match node.nodeType with
      | .file => node.nodeContent
      | .directory => none  -- Can't read directory as file

/-- Write file content -/
def writeFile (p : Path) (content : FileContent) (fs : FilesystemWithContent)
    : FilesystemWithContent :=
  fun p' =>
    if p = p' then
      match fs p' with
      | none => none  -- Can't write to non-existent file
      | some node =>
          match node.nodeType with
          | .file =>
              some {
                nodeType := node.nodeType,
                nodePerms := node.nodePerms,
                nodeContent := some content
              }
          | .directory => some node  -- No-op for directories
    else
      fs p'

-- Preconditions

/-- Can read file if it exists and is a file with read permissions -/
def ReadFilePrecondition (p : Path) (fs : FilesystemWithContent) : Prop :=
  ∃ node,
    fs p = some node ∧
    node.nodeType = FSNodeType.file ∧
    node.nodePerms.readable = true

/-- Can write file if it exists and is a file with write permissions -/
def WriteFilePrecondition (p : Path) (fs : FilesystemWithContent) : Prop :=
  ∃ node,
    fs p = some node ∧
    node.nodeType = FSNodeType.file ∧
    node.nodePerms.writable = true

-- Reversibility Properties

/-- Reading doesn't change the filesystem -/
theorem readFilePreservesFs (p : Path) (fs : FilesystemWithContent) (content : FileContent)
    (h : readFile p fs = some content) :
    fs = fs := by
  rfl

/-- Writing old content back restores filesystem -/
theorem writeFileReversible (p : Path) (fs : FilesystemWithContent)
    (oldContent newContent : FileContent)
    (hpre : WriteFilePrecondition p fs)
    (hold : readFile p fs = some oldContent) :
    writeFile p oldContent (writeFile p newContent fs) = fs := by
  funext p'
  unfold writeFile
  by_cases h : p = p'
  · subst h
    simp only [ite_true]
    obtain ⟨node, hnode, htype, _⟩ := hpre
    rw [hnode]
    simp only
    unfold readFile at hold
    rw [hnode] at hold
    simp only at hold
    cases hn : node.nodeType with
    | file =>
      simp only [hn] at hold
      simp only [hn]
      cases node with
      | mk nt np nc =>
        simp only at hn
        simp only [hn] at hold
        cases nc with
        | none => simp at hold
        | some c =>
          simp only [Option.some.injEq] at hold
          simp only [hn, hold]
    | directory =>
      rw [hn] at htype
      cases htype
  · simp only [h, ite_false]

-- Content Preservation

/-- Writing to one file doesn't affect others -/
theorem writeFileIndependence (p1 p2 : Path) (content : FileContent)
    (fs : FilesystemWithContent) (hneq : p1 ≠ p2) :
    readFile p2 (writeFile p1 content fs) = readFile p2 fs := by
  unfold writeFile readFile
  simp only [hneq, ite_false]

-- Content Composition Theorems

/-- Last write wins when writing the same path twice -/
theorem writeFileLastWriteWins (p : Path) (fs : FilesystemWithContent)
    (c1 c2 : FileContent) :
    writeFile p c2 (writeFile p c1 fs) = writeFile p c2 fs := by
  funext p'
  unfold writeFile
  by_cases h : p = p'
  · subst h
    cases hfs : fs p with
    | none => simp [hfs]
    | some node =>
        cases hnt : node.nodeType <;> simp [hfs, hnt]
  · simp [h]

/-- Writes to different paths commute -/
theorem writeFileCommute (p1 p2 : Path) (fs : FilesystemWithContent)
    (c1 c2 : FileContent) (hneq : p1 ≠ p2) :
    writeFile p1 c1 (writeFile p2 c2 fs) =
    writeFile p2 c2 (writeFile p1 c1 fs) := by
  funext p'
  unfold writeFile
  by_cases h2 : p2 = p'
  · subst h2
    have h1 : p1 ≠ p2 := hneq
    cases hfs : fs p2 with
    | none => simp [hfs, h1]
    | some node =>
        cases hnt : node.nodeType <;> simp [hfs, hnt, h1]
  · by_cases h1 : p1 = p'
    · subst h1
      cases hfs : fs p1 with
      | none => simp [hfs, h2]
      | some node =>
          cases hnt : node.nodeType <;> simp [hfs, hnt, h2]
    · simp [h2, h1]

-- Content Operations and Basic Operations

/-- Creating a file initializes empty content -/
theorem createFileEmptyContent (p : Path) (fs : Filesystem)
    (hpre : CreateFilePrecondition p fs) :
    readFile p (fsToFsWithContent (createFile p fs)) = some emptyContent := by
  -- Expand definitions step by step
  unfold readFile fsToFsWithContent createFile fsUpdate
  -- After createFile, fs p = some ⟨FSNodeType.file, defaultPerms⟩
  -- The condition p = p is trivially true, so simp closes the goal
  simp

-- State Tracking for Reversibility

/-- Record of file state for undo/redo -/
structure FileState where
  statePath : Path
  stateContent : FileContent
  stateExists : Bool

/-- Capture current file state -/
def captureFileState (p : Path) (fs : FilesystemWithContent) : FileState :=
  match readFile p fs with
  | some content => { statePath := p, stateContent := content, stateExists := true }
  | none => { statePath := p, stateContent := emptyContent, stateExists := false }

/-- Restore file state -/
def restoreFileState (state : FileState) (fs : FilesystemWithContent)
    : FilesystemWithContent :=
  if state.stateExists then
    writeFile state.statePath state.stateContent fs
  else
    fs  -- Would need delete operation

/-- Writing the same content back is identity -/
theorem writeFileSameContent (p : Path) (fs : FilesystemWithContent)
    (content : FileContent)
    (hpre : WriteFilePrecondition p fs)
    (hread : readFile p fs = some content) :
    writeFile p content fs = fs := by
  funext p'
  unfold writeFile
  by_cases h : p = p'
  · subst h
    simp only [ite_true]
    obtain ⟨node, hnode, htype, _⟩ := hpre
    rw [hnode]
    unfold readFile at hread
    rw [hnode] at hread
    simp only at hread
    cases hn : node.nodeType with
    | file =>
      simp only [hn] at hread
      simp only [hn]
      cases node with
      | mk nt np nc =>
        simp only at hn
        simp only [hn] at hread
        cases nc with
        | none => simp at hread
        | some c =>
          simp only [Option.some.injEq] at hread
          simp only [hn, hread]
    | directory =>
      rw [hn] at htype
      cases htype
  · simp only [h, ite_false]

/-- Capturing and restoring is identity (for existing files) -/
theorem captureRestoreIdentity (p : Path) (fs : FilesystemWithContent)
    (hpre : WriteFilePrecondition p fs) :
    restoreFileState (captureFileState p fs) fs = fs := by
  unfold restoreFileState captureFileState
  cases h : readFile p fs with
  | none => simp only [Bool.false_eq_true, ↓reduceIte]
  | some content =>
    simp only [↓reduceIte]
    exact writeFileSameContent p fs content hpre h

-- Integration with MAA Framework

/-- File modification record for audit trail -/
structure FileModificationRecord where
  modPath : Path
  modOldContent : FileContent
  modNewContent : FileContent
  modTimestamp : Nat  -- Simplified timestamp

/-- Create modification record -/
def createModRecord (p : Path) (oldContent newContent : FileContent)
    (timestamp : Nat) : FileModificationRecord :=
  { modPath := p, modOldContent := oldContent, modNewContent := newContent, modTimestamp := timestamp }

/-- Apply modification -/
def applyModification (record : FileModificationRecord)
    (fs : FilesystemWithContent) : FilesystemWithContent :=
  writeFile record.modPath record.modNewContent fs

/-- Reverse modification -/
def reverseModification (record : FileModificationRecord)
    (fs : FilesystemWithContent) : FilesystemWithContent :=
  writeFile record.modPath record.modOldContent fs

/-- Modification is reversible -/
theorem modificationReversible (record : FileModificationRecord)
    (fs : FilesystemWithContent)
    (hpre : WriteFilePrecondition record.modPath fs)
    (hold : readFile record.modPath fs = some record.modOldContent) :
    reverseModification record (applyModification record fs) = fs := by
  unfold reverseModification applyModification
  exact writeFileReversible record.modPath fs record.modOldContent record.modNewContent hpre hold

-- Summary: File content operations in Lean 4
-- Extends verified filesystem with content tracking
-- Maintains reversibility guarantees

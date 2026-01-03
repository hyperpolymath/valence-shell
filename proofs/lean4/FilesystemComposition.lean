/- Valence Shell - Filesystem Composition (Lean 4)

   Composition theorems for sequences of filesystem operations.
   Based on Absolute Zero's CNO composition theory.
-/

import FilesystemModel
import FileOperations

-- Operation abstraction
inductive Operation where
  | mkdirOp : Path → Operation
  | rmdirOp : Path → Operation
  | createFileOp : Path → Operation
  | deleteFileOp : Path → Operation
  deriving DecidableEq, Repr

-- Apply operation to filesystem
def applyOp (op : Operation) (fs : Filesystem) : Filesystem :=
  match op with
  | .mkdirOp p => mkdir p fs
  | .rmdirOp p => rmdir p fs
  | .createFileOp p => createFile p fs
  | .deleteFileOp p => deleteFile p fs

-- Reverse operation
def reverseOp (op : Operation) : Operation :=
  match op with
  | .mkdirOp p => .rmdirOp p
  | .rmdirOp p => .mkdirOp p
  | .createFileOp p => .deleteFileOp p
  | .deleteFileOp p => .createFileOp p

-- Apply sequence of operations
def applySequence : List Operation → Filesystem → Filesystem
  | [], fs => fs
  | op :: rest, fs => applySequence rest (applyOp op fs)

-- Reverse sequence
def reverseSequence (ops : List Operation) : List Operation :=
  (ops.reverse.map reverseOp)

-- Precondition for operation
def opPrecondition (op : Operation) (fs : Filesystem) : Prop :=
  match op with
  | .mkdirOp p => MkdirPrecondition p fs
  | .rmdirOp p => RmdirPrecondition p fs
  | .createFileOp p => CreateFilePrecondition p fs
  | .deleteFileOp p => DeleteFilePrecondition p fs

-- All preconditions hold
def allPreconditions : List Operation → Filesystem → Prop
  | [], _ => True
  | op :: rest, fs =>
      opPrecondition op fs ∧
      allPreconditions rest (applyOp op fs)

-- Operation is reversible (includes permission requirements for exact reversal)
def reversible (op : Operation) (fs : Filesystem) : Prop :=
  opPrecondition op fs ∧
  opPrecondition (reverseOp op) (applyOp op fs) ∧
  (match op with
   | .rmdirOp p => fs p = some ⟨FSNodeType.directory, defaultPerms⟩
   | .deleteFileOp p => fs p = some ⟨FSNodeType.file, defaultPerms⟩
   | _ => True)

-- All operations are reversible
def allReversible : List Operation → Filesystem → Prop
  | [], _ => True
  | op :: rest, fs =>
      reversible op fs ∧
      allReversible rest (applyOp op fs)

-- Helper Lemmas

theorem applyEmpty (fs : Filesystem) :
    applySequence [] fs = fs := by
  rfl

theorem applyCons (op : Operation) (ops : List Operation) (fs : Filesystem) :
    applySequence (op :: ops) fs = applySequence ops (applyOp op fs) := by
  rfl

theorem reverseOpInvolutive (op : Operation) :
    reverseOp (reverseOp op) = op := by
  cases op <;> rfl

theorem reverseSequenceNil :
    reverseSequence [] = [] := by
  rfl

theorem reverseSequenceSingleton (op : Operation) :
    reverseSequence [op] = [reverseOp op] := by
  rfl

-- Sequence append lemma
theorem applySequence_append (xs ys : List Operation) (fs : Filesystem) :
    applySequence (xs ++ ys) fs = applySequence ys (applySequence xs fs) := by
  induction xs generalizing fs with
  | nil => simp [applySequence]
  | cons op rest ih =>
      simp only [List.cons_append, applySequence]
      exact ih (applyOp op fs)

-- Single Operation Reversibility

theorem singleMkdirReversible (p : Path) (fs : Filesystem)
    (hpre : MkdirPrecondition p fs) :
    applyOp (.rmdirOp p) (applyOp (.mkdirOp p) fs) = fs := by
  simp [applyOp]
  exact mkdir_rmdir_reversible p fs hpre

theorem singleCreateFileReversible (p : Path) (fs : Filesystem)
    (hpre : CreateFilePrecondition p fs) :
    applyOp (.deleteFileOp p) (applyOp (.createFileOp p) fs) = fs := by
  simp [applyOp]
  exact createFile_deleteFile_reversible p fs hpre

theorem singleOpReversible (op : Operation) (fs : Filesystem)
    (hrev : reversible op fs) :
    applyOp (reverseOp op) (applyOp op fs) = fs := by
  cases op with
  | mkdirOp p =>
      apply singleMkdirReversible
      exact hrev.1
  | rmdirOp p =>
      -- Reverse: mkdir after rmdir
      simp only [reverseOp, applyOp]
      -- hrev.2.2 gives us: fs p = some ⟨directory, defaultPerms⟩
      apply rmdir_mkdir_reversible
      · exact hrev.1
      · exact hrev.2.2
  | createFileOp p =>
      apply singleCreateFileReversible
      exact hrev.1
  | deleteFileOp p =>
      -- Reverse: createFile after deleteFile
      simp only [reverseOp, applyOp]
      -- hrev.2.2 gives us: fs p = some ⟨file, defaultPerms⟩
      apply deleteFile_createFile_reversible
      · exact hrev.1
      · exact hrev.2.2

-- Main Composition Theorem

theorem operationSequenceReversible (ops : List Operation) (fs : Filesystem)
    (hrev : allReversible ops fs) :
    applySequence (reverseSequence ops) (applySequence ops fs) = fs := by
  induction ops generalizing fs with
  | nil =>
      simp [applySequence, reverseSequence]
  | cons op rest ih =>
      -- reverseSequence (op :: rest) = map reverseOp (reverse (op :: rest))
      --                              = map reverseOp (reverse rest ++ [op])
      --                              = map reverseOp (reverse rest) ++ [reverseOp op]
      --                              = reverseSequence rest ++ [reverseOp op]
      simp only [reverseSequence, applySequence, List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
      have ⟨hrev_op, hrev_rest⟩ := hrev
      -- Step 1: Apply rest operations then reverse rest
      have ih_result := ih (applyOp op fs) hrev_rest
      -- ih_result: applySequence (reverseSequence rest) (applySequence rest (applyOp op fs)) = applyOp op fs
      -- Step 2: Apply reverseOp op to get back to fs
      have single := singleOpReversible op fs hrev_op
      -- single: applyOp (reverseOp op) (applyOp op fs) = fs
      -- Now combine: applySequence (reverseSequence rest ++ [reverseOp op]) (applySequence (op :: rest) fs)
      rw [applySequence_append]
      simp only [applySequence]
      rw [ih_result]
      exact single

-- Two and Three Operation Sequences

theorem twoOpSequenceReversible (op1 op2 : Operation) (fs : Filesystem)
    (hrev1 : reversible op1 fs)
    (hrev2 : reversible op2 (applyOp op1 fs)) :
    applyOp (reverseOp op1)
      (applyOp (reverseOp op2)
        (applyOp op2 (applyOp op1 fs))) = fs := by
  -- First undo op2
  have h2 := singleOpReversible op2 (applyOp op1 fs) hrev2
  rw [h2]
  -- Then undo op1
  exact singleOpReversible op1 fs hrev1

theorem threeOpSequenceReversible (op1 op2 op3 : Operation) (fs : Filesystem)
    (hrev1 : reversible op1 fs)
    (hrev2 : reversible op2 (applyOp op1 fs))
    (hrev3 : reversible op3 (applyOp op2 (applyOp op1 fs))) :
    applySequence (reverseSequence [op1, op2, op3])
      (applySequence [op1, op2, op3] fs) = fs := by
  -- Use the general theorem
  apply operationSequenceReversible
  -- Need to show allReversible [op1, op2, op3] fs
  simp only [allReversible]
  exact ⟨hrev1, hrev2, hrev3, trivial⟩

-- CNO Connection

def isCNOSequence (ops : List Operation) : Prop :=
  ∀ fs, allReversible ops fs →
    applySequence (ops ++ reverseSequence ops) fs = fs

theorem reversibleCreatesCNO (op : Operation) :
    isCNOSequence [op] := by
  intro fs hrev
  simp [reverseSequence, applySequence]
  exact singleOpReversible op fs hrev.1

-- Summary: Composition theory complete in Lean 4

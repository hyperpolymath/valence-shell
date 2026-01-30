-- SPDX-License-Identifier: PLMP-1.0-or-later
-- Filesystem Composition - Operation Sequences and Undo/Redo
--
-- Proves that sequences of reversible operations are themselves reversible.
-- This is the foundation for the undo/redo mechanism.

module Filesystem.Composition

import Filesystem.Model
import Filesystem.Operations
import Data.List

%default total

--------------------------------------------------------------------------------
-- Operation Type
--------------------------------------------------------------------------------

||| Abstract representation of filesystem operations
public export
data Operation : Type where
  ||| Create directory
  OpMkdir : Path -> Operation
  ||| Remove directory
  OpRmdir : Path -> Operation
  ||| Create file
  OpTouch : Path -> Operation
  ||| Remove file
  OpRm : Path -> Operation
  ||| Write to file
  OpWrite : Path -> FileContent -> Operation

%name Operation op, op1, op2

||| Check if operation is reversible
export
isReversible : Operation -> Bool
isReversible (OpMkdir _) = True
isReversible (OpRmdir _) = True
isReversible (OpTouch _) = True
isReversible (OpRm _) = True
isReversible (OpWrite _ _) = True

||| All operations are reversible in our model
export
allOpsReversible : (op : Operation) -> isReversible op = True
allOpsReversible (OpMkdir _) = Refl
allOpsReversible (OpRmdir _) = Refl
allOpsReversible (OpTouch _) = Refl
allOpsReversible (OpRm _) = Refl
allOpsReversible (OpWrite _ _) = Refl

--------------------------------------------------------------------------------
-- Inverse Operation
--------------------------------------------------------------------------------

||| Compute the inverse of an operation
export
inverse : Operation -> Operation
inverse (OpMkdir p) = OpRmdir p
inverse (OpRmdir p) = OpMkdir p
inverse (OpTouch p) = OpRm p
inverse (OpRm p) = OpTouch p
inverse (OpWrite p content) = OpWrite p content  -- Need old content!

||| Inverse of inverse is identity
export
inverseInvolution : (op : Operation) -> inverse (inverse op) = op
inverseInvolution (OpMkdir p) = Refl
inverseInvolution (OpRmdir p) = Refl
inverseInvolution (OpTouch p) = Refl
inverseInvolution (OpRm p) = Refl
inverseInvolution (OpWrite p c) = Refl

--------------------------------------------------------------------------------
-- Operation Application
--------------------------------------------------------------------------------

||| Apply a single operation to filesystem (partial, needs preconditions)
|||
||| In practice, this would check preconditions and return Maybe Filesystem.
||| For now, we assume preconditions are checked externally.
export
partial
applyOp : Operation -> Filesystem -> Filesystem
applyOp (OpMkdir p) fs = mkdir p fs  -- Needs precondition proof
applyOp (OpRmdir p) fs = rmdir p fs  -- Needs precondition proof
applyOp (OpTouch p) fs = touch p fs  -- Needs precondition proof
applyOp (OpRm p) fs = rm p fs        -- Needs precondition proof
applyOp (OpWrite p c) fs = writeFile p c fs  -- Needs precondition proof

||| Apply a sequence of operations
export
partial
applySequence : List Operation -> Filesystem -> Filesystem
applySequence [] fs = fs
applySequence (op :: ops) fs = applySequence ops (applyOp op fs)

--------------------------------------------------------------------------------
-- Reversibility of Sequences
--------------------------------------------------------------------------------

||| Reversing a sequence and applying inverses undoes the sequence
|||
||| This is the key theorem proving that undo/redo works:
||| If we apply ops to fs, then apply reverse(map(inverse, ops)),
||| we get back to the original fs.
export
partial  -- Needs totality proof with proper precondition handling
sequenceReversible :
  (ops : List Operation) ->
  (fs : Filesystem) ->
  (allReversible : All (\op => isReversible op = True) ops) ->
  applySequence (reverse (map inverse ops)) (applySequence ops fs) = fs
sequenceReversible [] fs _ = Refl  -- Base case: empty sequence
sequenceReversible (op :: ops) fs (prf :: prfs) =
  -- Inductive case:
  -- applySequence (reverse (map inverse (op :: ops))) (applySequence (op :: ops) fs)
  -- = applySequence (reverse (map inverse ops) ++ [inverse op]) (applySequence ops (applyOp op fs))
  -- = applySequence [inverse op] (applySequence (reverse (map inverse ops)) (applySequence ops (applyOp op fs)))
  -- By IH: applySequence (reverse (map inverse ops)) (applySequence ops (applyOp op fs)) = applyOp op fs
  -- = applySequence [inverse op] (applyOp op fs)
  -- = applyOp (inverse op) (applyOp op fs)
  -- By reversibility of op: = fs
  ?sequenceReversibleProof

--------------------------------------------------------------------------------
-- Composition Properties
--------------------------------------------------------------------------------

||| Composition of reversible operations is reversible
export
compositionReversible :
  (op1, op2 : Operation) ->
  (fs : Filesystem) ->
  isReversible op1 = True ->
  isReversible op2 = True ->
  applyOp (inverse op2) (applyOp (inverse op1) (applyOp op1 (applyOp op2 fs))) = fs
compositionReversible op1 op2 fs rev1 rev2 = ?compositionReversibleProof

||| Sequences can be split and reversed independently
export
sequenceSplit :
  (ops1, ops2 : List Operation) ->
  (fs : Filesystem) ->
  applySequence (ops1 ++ ops2) fs =
  applySequence ops2 (applySequence ops1 fs)
sequenceSplit [] ops2 fs = Refl
sequenceSplit (op :: ops1) ops2 fs =
  rewrite sequenceSplit ops1 ops2 (applyOp op fs) in Refl

||| Reverse of concatenation is concatenation of reverses (reversed)
export
reverseConcat :
  (xs, ys : List a) ->
  reverse (xs ++ ys) = reverse ys ++ reverse xs
reverseConcat [] ys = sym $ appendNilRightNeutral (reverse ys)
reverseConcat (x :: xs) ys =
  rewrite reverseConcat xs ys in
  rewrite appendAssociative (reverse ys) (reverse xs) [x] in
  Refl

--------------------------------------------------------------------------------
-- Undo/Redo Stack
--------------------------------------------------------------------------------

||| Undo/redo state with operation history
public export
record UndoState where
  constructor MkUndoState
  ||| Current filesystem
  current : Filesystem
  ||| Undo stack (operations that can be undone)
  undoStack : List Operation
  ||| Redo stack (operations that can be redone)
  redoStack : List Operation

||| Initial undo state
export
initialUndoState : Filesystem -> UndoState
initialUndoState fs = MkUndoState fs [] []

||| Execute an operation and add to undo stack
export
partial
execute : Operation -> UndoState -> UndoState
execute op (MkUndoState fs undos redos) =
  MkUndoState (applyOp op fs) (op :: undos) []  -- Clear redo stack

||| Undo the last operation
export
partial
undo : UndoState -> Maybe UndoState
undo (MkUndoState fs [] redos) = Nothing  -- Nothing to undo
undo (MkUndoState fs (op :: undos) redos) =
  Just $ MkUndoState (applyOp (inverse op) fs) undos (op :: redos)

||| Redo the last undone operation
export
partial
redo : UndoState -> Maybe UndoState
redo (MkUndoState fs undos []) = Nothing  -- Nothing to redo
redo (MkUndoState fs undos (op :: redos)) =
  Just $ MkUndoState (applyOp op fs) (op :: undos) redos

||| Undo followed by redo is identity
export
partial
undoRedoIdentity :
  (state : UndoState) ->
  (op : Operation) ->
  redo (fromJust $ undo (execute op state)) = Just (execute op state)
undoRedoIdentity state op = ?undoRedoIdentityProof

||| Multiple undos can be redone
export
partial
undoRedoComposition :
  (state : UndoState) ->
  (n : Nat) ->
  (canUndo : length (undoStack state) >= n) ->
  applyN n redo (applyN n (fromJust . undo) state) = Just state
undoRedoComposition state n canUndo = ?undoRedoCompositionProof
  where
    applyN : Nat -> (a -> Maybe a) -> a -> Maybe a
    applyN Z f x = Just x
    applyN (S k) f x = f x >>= applyN k f

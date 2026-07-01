-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-- Filesystem Composition - Operation Sequences and Undo/Redo
--
-- Proves that sequences of reversible operations are themselves reversible.
-- This is the foundation for the undo/redo mechanism.

module Filesystem.Composition

import Filesystem.Model
import Filesystem.Operations
import Data.List
import Data.List.Quantifiers
import Data.Nat

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

||| Apply a single operation to filesystem.
|||
||| Total: bypasses the precondition-requiring wrappers from `Filesystem.
||| Operations` (mkdir/rmdir/touch/rm/writeFile) by calling the underlying
||| primitives from `Filesystem.Model` directly. The semantics match: the
||| precondition-checking wrappers' bodies are `addEntry p Dir fs` etc.
||| Precondition-aware variants live in `Filesystem.Operations` for
||| theorem-proving contexts; this one is for sequence composition.
public export
applyOp : Operation -> Filesystem -> Filesystem
applyOp (OpMkdir p) fs   = addEntry p Dir fs
applyOp (OpRmdir p) fs   = removeEntry p fs
applyOp (OpTouch p) fs   = addEntry p (File []) fs
applyOp (OpRm p) fs      = removeEntry p fs
applyOp (OpWrite p c) fs = updateEntry p (File c) fs

||| Apply a sequence of operations
public export
applySequence : List Operation -> Filesystem -> Filesystem
applySequence [] fs = fs
applySequence (op :: ops) fs = applySequence ops (applyOp op fs)

--------------------------------------------------------------------------------
-- Single-operation reversibility
--------------------------------------------------------------------------------

||| When an operation may be cleanly undone-then-redone at a given state.
||| The additive operations (mkdir/touch) require their path to be absent —
||| otherwise the create shadows an existing entry and the round-trip loses
||| it. The subtractive and write operations are always applicable in this
||| (redo) sense.
public export
Applicable : Operation -> Filesystem -> Type
Applicable (OpMkdir p)   fs = lookup p (entries fs) = Nothing
Applicable (OpTouch p)   fs = lookup p (entries fs) = Nothing
Applicable (OpRmdir p)   fs = Unit
Applicable (OpRm p)      fs = Unit
Applicable (OpWrite p c) fs = Unit

||| Operation-level redo law: re-applying `op` after undoing it, on top of
||| `applyOp op fs`, returns to `applyOp op fs`. This
||| `op ∘ inverse op ∘ op = op` identity is exactly what makes the
||| undo→redo round-trip an identity (see `undoRedoIdentity`). Proved by
||| cases: additive ops via `removeAddAbsent` (needing `Applicable`),
||| subtractive ops via `removeAddRemove`, the write op via `updateOverwrite`.
export
opInvOpId : (op : Operation) -> (fs : Filesystem) -> Applicable op fs ->
            applyOp op (applyOp (inverse op) (applyOp op fs)) = applyOp op fs
opInvOpId (OpMkdir p) fs prf =
  cong (addEntry p Dir) (removeAddAbsent p Dir fs prf)
opInvOpId (OpTouch p) fs prf =
  cong (addEntry p (File [])) (removeAddAbsent p (File []) fs prf)
opInvOpId (OpRmdir p) fs _ = removeAddRemove p Dir fs
opInvOpId (OpRm p) fs _ = removeAddRemove p (File []) fs
opInvOpId (OpWrite p c) fs _ =
  trans (updateOverwrite p (File c) (File c) (updateEntry p (File c) fs))
        (updateOverwrite p (File c) (File c) fs)

--------------------------------------------------------------------------------
-- Reversibility of Sequences
--------------------------------------------------------------------------------

||| Sequences can be split and reversed independently.
export
sequenceSplit :
  (ops1, ops2 : List Operation) ->
  (fs : Filesystem) ->
  applySequence (ops1 ++ ops2) fs =
  applySequence ops2 (applySequence ops1 fs)
sequenceSplit [] ops2 fs = Refl
sequenceSplit (op :: ops1) ops2 fs =
  rewrite sequenceSplit ops1 ops2 (applyOp op fs) in Refl

||| Reverse of concatenation is concatenation of reverses (reversed).
||| Closes via `Data.List.revAppend` from Idris2 0.8.0's base stdlib.
||| The stdlib lemma is stated with the equality symmetric to ours
||| (`revAppend xs ys : reverse ys ++ reverse xs = reverse (xs ++ ys)`),
||| so we apply `sym`. The local restatement keeps call sites stable
||| and matches the conventional "concatenation distributes over
||| reverse" framing.
export
reverseConcat :
  (xs, ys : List a) ->
  reverse (xs ++ ys) = reverse ys ++ reverse xs
reverseConcat xs ys = sym (revAppend xs ys)

||| A trace is reversible when every operation genuinely inverts at the
||| state it runs on. This replaces the vacuous `All (isReversible op =
||| True)` premise (`isReversible` is constantly `True`, so it carried no
||| information): the real content of "the sequence can be undone" is that
||| each step's inverse actually restores that step's input state.
public export
data TraceReversible : List Operation -> Filesystem -> Type where
  ||| The empty trace is reversible from any state.
  TNil : TraceReversible [] fs
  ||| A `op :: ops` trace is reversible from `fs` when `op` inverts at `fs`
  ||| and `ops` is reversible from the resulting state `applyOp op fs`.
  TCons : {0 op : Operation} -> {0 ops : List Operation} -> {0 fs : Filesystem} ->
          (applyOp (inverse op) (applyOp op fs) = fs) ->
          TraceReversible ops (applyOp op fs) ->
          TraceReversible (op :: ops) fs

||| `reverse` peels its head to the tail end. Derived from the local
||| `reverseConcat` (concatenation distributes over reverse).
reverseCons : (x : a) -> (xs : List a) -> reverse (x :: xs) = reverse xs ++ [x]
reverseCons x xs = reverseConcat [x] xs

||| Reversing a sequence and applying inverses undoes the sequence.
|||
||| The key theorem behind undo/redo: applying `ops` to `fs` and then the
||| reversed list of inverses returns to `fs` — provided the trace is
||| genuinely reversible (`TraceReversible`). By induction on that witness:
||| the head's inverse cancels the head (its `applyOp (inverse op) ∘ applyOp
||| op = id` field) while the inductive hypothesis cancels the tail,
||| stitched together with `reverseCons` and `sequenceSplit`.
export
sequenceReversible :
  (ops : List Operation) ->
  (fs : Filesystem) ->
  TraceReversible ops fs ->
  applySequence (reverse (map Composition.inverse ops)) (applySequence ops fs) = fs
sequenceReversible [] fs TNil = Refl
sequenceReversible (op :: ops) fs (TCons revOp rest) =
  rewrite reverseCons (inverse op) (map Composition.inverse ops) in
  rewrite sequenceSplit (reverse (map Composition.inverse ops)) [inverse op]
                        (applySequence ops (applyOp op fs)) in
  rewrite sequenceReversible ops (applyOp op fs) rest in
  revOp

--------------------------------------------------------------------------------
-- Composition Properties
--------------------------------------------------------------------------------

||| Composition of reversible operations is reversible.
|||
||| The previous `isReversible op = True` hypotheses were vacuous (every op
||| satisfies that boolean), so the old statement was a non-theorem — e.g.
||| `OpWrite` discards the old content and does not actually invert. The
||| faithful hypotheses are the genuine per-step reversibility facts:
||| `op1` reverses at the intermediate state `applyOp op2 fs`, and `op2`
||| reverses at `fs`. Given those, the composite reverses by rewriting the
||| inner step then discharging the outer. Callers supply the hypotheses
||| from the single-op reversibility theorems (`removeAddAbsent`,
||| `mkdirRmdirReversible`, …).
export
compositionReversible :
  (op1, op2 : Operation) ->
  (fs : Filesystem) ->
  (rev1 : applyOp (inverse op1) (applyOp op1 (applyOp op2 fs)) = applyOp op2 fs) ->
  (rev2 : applyOp (inverse op2) (applyOp op2 fs) = fs) ->
  applyOp (inverse op2) (applyOp (inverse op1) (applyOp op1 (applyOp op2 fs))) = fs
compositionReversible op1 op2 fs rev1 rev2 = rewrite rev1 in rev2

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
public export
execute : Operation -> UndoState -> UndoState
execute op (MkUndoState fs undos redos) =
  MkUndoState (applyOp op fs) (op :: undos) []  -- Clear redo stack

||| Undo the last operation
public export
undo : UndoState -> Maybe UndoState
undo (MkUndoState fs [] redos) = Nothing  -- Nothing to undo
undo (MkUndoState fs (op :: undos) redos) =
  Just $ MkUndoState (applyOp (Composition.inverse op) fs) undos (op :: redos)

||| Redo the last undone operation
public export
redo : UndoState -> Maybe UndoState
redo (MkUndoState fs undos []) = Nothing  -- Nothing to redo
redo (MkUndoState fs undos (op :: redos)) =
  Just $ MkUndoState (applyOp op fs) (op :: undos) redos

||| Undo followed by redo is identity.
|||
||| After `execute op`, one `undo` then one `redo` returns to the executed
||| state. Reduces (via the `public export` execute/undo/redo) to the
||| operation-level redo law `applyOp op ∘ applyOp (inverse op) ∘ applyOp
||| op = applyOp op`, i.e. `opInvOpId`, whence the `Applicable op` premise
||| (needed only so additive ops are not shadowing an existing entry).
||| `fromJust` (partial, undefined in Idris2 0.8.0) is avoided via the
||| Maybe-monadic `undo >>= redo` shape.
export
undoRedoIdentity :
  (state : UndoState) ->
  (op : Operation) ->
  Applicable op (current state) ->
  (Composition.undo (execute op state) >>= Composition.redo) = Just (execute op state)
undoRedoIdentity (MkUndoState fs u r) op prf =
  cong (\x => Just (MkUndoState x (op :: u) [])) (opInvOpId op fs prf)

||| Apply a Maybe-returning function n times.
public export
applyN : Nat -> (a -> Maybe a) -> a -> Maybe a
applyN Z f x = Just x
applyN (S k) f x = f x >>= applyN k f

||| Right identity for the `Maybe` bind.
bindRightId : (m : Maybe a) -> (m >>= Just) = m
bindRightId Nothing  = Refl
bindRightId (Just x) = Refl

||| Associativity of the `Maybe` bind.
bindAssoc : (m : Maybe a) -> (f : a -> Maybe b) -> (g : b -> Maybe c) ->
            ((m >>= f) >>= g) = (m >>= (\x => f x >>= g))
bindAssoc Nothing  f g = Refl
bindAssoc (Just x) f g = Refl

||| Congruence for the `Maybe` bind under a pointwise-equal continuation.
||| Proved by casing on the `Maybe`, so it needs no functional
||| extensionality.
bindCong : (m : Maybe a) -> {0 g1, g2 : a -> Maybe b} ->
           ((y : a) -> g1 y = g2 y) -> (m >>= g1) = (m >>= g2)
bindCong Nothing  h = Refl
bindCong (Just y) h = h y

||| `applyN (S n)` peels its last iteration to the end: iterating `f`
||| `n + 1` times equals iterating `n` times then once more. Kleisli
||| associativity for the `n`-fold composition — the lemma that lets the
||| final redo line up with the first undo.
applyNSnoc : (n : Nat) -> (f : a -> Maybe a) -> (x : a) ->
             applyN (S n) f x = (applyN n f x >>= f)
applyNSnoc Z     f x = trans (bindCong (f x) (\y => Refl)) (bindRightId (f x))
applyNSnoc (S k) f x =
  trans (bindCong (f x) (\y => applyNSnoc k f y))
        (sym (bindAssoc (f x) (applyN k f) f))

||| A state is `n`-fold undoable when each of the next `n` undos is exactly
||| cancelled by a redo. Honest replacement for the old
||| `LTE n (length (undoStack state))` premise: stack depth alone does not
||| guarantee the round-trip (the operations must actually reverse). This
||| witness records, level by level, that `undo` then `redo` returns to the
||| same state — the undo/redo-stack analogue of `TraceReversible`.
public export
data Undoable : Nat -> UndoState -> Type where
  ||| Zero undos: trivially undoable.
  UZ : Undoable Z st
  ||| One undo to `s'` that a `redo` cancels, then `n` more from `s'`.
  US : {0 st : UndoState} -> {0 n : Nat} ->
       (s' : UndoState) ->
       undo st = Just s' ->
       redo s' = Just st ->
       Undoable n s' ->
       Undoable (S n) st

||| Multiple undos can all be redone: `n` undos followed by `n` redos is
||| the identity, for any `n`-fold-undoable state.
|||
||| The previous `LTE n (length (undoStack state))` premise was not enough
||| to make this true — a deep stack of *irreversible* steps would not
||| round-trip — so the theorem is stated over the `Undoable` witness that
||| supplies the per-level cancellation. Proof by induction on that
||| witness: `applyNSnoc` untangles the interleaving (redo peels off in the
||| reverse order the undos were pushed), the `Maybe` monad laws
||| (`bindAssoc`, `bindCong`) re-associate the composition, and each level's
||| `undo`/`redo` fields close the round-trip.
export
undoRedoComposition :
  (state : UndoState) ->
  (n : Nat) ->
  Undoable n state ->
  (applyN n Composition.undo state >>= applyN n Composition.redo) = Just state
undoRedoComposition state Z UZ = Refl
undoRedoComposition state (S n) (US s' uEq rEq inner) =
  rewrite uEq in
  trans (bindCong (applyN n Composition.undo s')
                  (\z => applyNSnoc n Composition.redo z))
        (trans (sym (bindAssoc (applyN n Composition.undo s')
                               (applyN n Composition.redo) Composition.redo))
               (rewrite undoRedoComposition s' n inner in rEq))

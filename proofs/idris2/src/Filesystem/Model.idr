-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-- Filesystem Model - Core Types and Definitions
--
-- This module defines the abstract filesystem model used throughout
-- the valence-shell verification. All operations are total and proven
-- to terminate.

module Filesystem.Model

import Data.Bool
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.String
import Decidable.Equality

import Filesystem.Axioms

%default total

--------------------------------------------------------------------------------
-- Path Representation
--------------------------------------------------------------------------------

||| A filesystem path represented as a list of components
||| Root is the empty list, /foo/bar is ["foo", "bar"]
public export
data Path : Type where
  ||| Root path /
  Root : Path
  ||| Path component
  Cons : String -> Path -> Path

%name Path p, q, r

||| Convert path to string for display
export
pathToString : Path -> String
pathToString Root = "/"
pathToString (Cons comp rest) =
  "/" ++ comp ++ pathToString rest

||| Path equality is decidable
export
DecEq Path where
  decEq Root Root = Yes Refl
  decEq Root (Cons _ _) = No (\case Refl impossible)
  decEq (Cons _ _) Root = No (\case Refl impossible)
  decEq (Cons x xs) (Cons y ys) with (decEq x y)
    decEq (Cons x xs) (Cons x ys) | Yes Refl with (decEq xs ys)
      decEq (Cons x xs) (Cons x xs) | Yes Refl | Yes Refl = Yes Refl
      decEq (Cons x xs) (Cons x ys) | Yes Refl | No contra =
        No (\Refl => contra Refl)
    decEq (Cons x xs) (Cons y ys) | No contra =
      No (\Refl => contra Refl)

||| Boolean equality on paths (required by Data.List.lookup / elem)
public export
Eq Path where
  Root         == Root         = True
  (Cons x xs)  == (Cons y ys)  = x == y && xs == ys
  _            == _            = False

||| Parent of a path
export
parent : Path -> Maybe Path
parent Root = Nothing
parent (Cons _ p) = Just p

||| Check if path is root
export
isRoot : Path -> Bool
isRoot Root = True
isRoot _ = False

--------------------------------------------------------------------------------
-- Filesystem State
--------------------------------------------------------------------------------

||| File content represented as list of bytes
public export
FileContent : Type
FileContent = List Bits8

||| A filesystem entry - either directory or file
public export
data FSEntry : Type where
  ||| Directory entry
  Dir : FSEntry
  ||| File entry with content
  File : FileContent -> FSEntry

||| Boolean equality on filesystem entries
public export
Eq FSEntry where
  Dir          == Dir          = True
  (File c1)    == (File c2)    = c1 == c2
  _            == _            = False

||| Filesystem state mapping paths to entries
public export
record Filesystem where
  constructor MkFS
  ||| Mapping from paths to entries
  entries : List (Path, FSEntry)

%name Filesystem fs, fs1, fs2

||| Empty filesystem (only root directory)
export
empty : Filesystem
empty = MkFS []

--------------------------------------------------------------------------------
-- Filesystem Queries
--------------------------------------------------------------------------------

||| Check if a path exists in the filesystem
export
pathExists : Path -> Filesystem -> Bool
pathExists p (MkFS entries) =
  isJust $ lookup p entries

||| Get entry at path
export
getEntry : Path -> Filesystem -> Maybe FSEntry
getEntry p (MkFS entries) = lookup p entries

||| Check if path is a directory
export
isDirectory : Path -> Filesystem -> Bool
isDirectory p fs = case getEntry p fs of
  Just Dir => True
  _ => False

||| Check if path is a file
export
isFile : Path -> Filesystem -> Bool
isFile p fs = case getEntry p fs of
  Just (File _) => True
  _ => False

||| Get file content
export
getFileContent : Path -> Filesystem -> Maybe FileContent
getFileContent p fs = case getEntry p fs of
  Just (File content) => Just content
  _ => Nothing

||| Check if directory is empty
export
isDirEmpty : Path -> Filesystem -> Bool
isDirEmpty p (MkFS entries) =
  let children = filter (\(q, _) => parent q == Just p) entries
  in null children

--------------------------------------------------------------------------------
-- Filesystem Modification
--------------------------------------------------------------------------------

||| Add an entry to filesystem
export
addEntry : Path -> FSEntry -> Filesystem -> Filesystem
addEntry p entry (MkFS entries) =
  MkFS ((p, entry) :: entries)

||| Predicate: keep entries at paths other than `p`. Named (rather than
||| inlined as a lambda) so that proofs about `removeEntry` can refer to
||| the *same* predicate as the implementation — anonymous lambdas at
||| separate call sites don't unify in Idris2 0.8.0.
public export
keepIfNotP : Path -> (Path, FSEntry) -> Bool
keepIfNotP p (q, _) = p /= q

||| Remove an entry from filesystem
export
removeEntry : Path -> Filesystem -> Filesystem
removeEntry p (MkFS entries) =
  MkFS (filter (keepIfNotP p) entries)

||| `removeEntry p` depends only on the `keepIfNotP p` projection of the
||| entries list. If two filesystems agree on this projection, they are
||| observationally identical after `removeEntry p`. This is the
||| structural lemma underlying RMO's non-injectivity (see
||| `Filesystem.RMO.secureDeleteNotInjective`, which mirrors Coq's
||| `obliterate_not_injective`).
public export
removeEntryDeterminedByFilter :
  (p : Path) ->
  (fs1, fs2 : Filesystem) ->
  filter (keepIfNotP p) (entries fs1)
    = filter (keepIfNotP p) (entries fs2) ->
  removeEntry p fs1 = removeEntry p fs2
removeEntryDeterminedByFilter p (MkFS e1) (MkFS e2) agreeOff =
  cong MkFS agreeOff

||| Update entry at path
export
updateEntry : Path -> FSEntry -> Filesystem -> Filesystem
updateEntry p entry fs =
  addEntry p entry (removeEntry p fs)

--------------------------------------------------------------------------------
-- Filesystem Equivalence
--------------------------------------------------------------------------------

||| Two filesystems are equivalent if they have the same entries
||| (ignoring order)
export
equiv : Filesystem -> Filesystem -> Bool
equiv (MkFS entries1) (MkFS entries2) =
  all (\e => elem e entries2) entries1 &&
  all (\e => elem e entries1) entries2

--------------------------------------------------------------------------------
-- Primitive-eq reflexivity (lifted from Filesystem.Axioms)
--------------------------------------------------------------------------------

||| `Path` equality is reflexive — proved by structural induction over
||| `Path`, using `axStringEqRefl` at the leaf for each `String` component.
export
pathEqRefl : (p : Path) -> (p == p) = True
pathEqRefl Root = Refl
pathEqRefl (Cons s rest) =
  rewrite axStringEqRefl s in
  rewrite pathEqRefl rest in
  Refl

||| `FSEntry` equality is reflexive — `Dir == Dir = True` by definition,
||| `File c == File c = c == c = True` via `fileContentEqRefl`.
export
fsEntryEqRefl : (e : FSEntry) -> (e == e) = True
fsEntryEqRefl Dir = Refl
fsEntryEqRefl (File c) = fileContentEqRefl c

||| Tuple `(Path, FSEntry)` equality reflexivity — combines `pathEqRefl`
||| and `fsEntryEqRefl` through the derived `Eq` instance.
export
entryEqRefl : (e : (Path, FSEntry)) -> (e == e) = True
entryEqRefl (p, fe) =
  rewrite pathEqRefl p in
  rewrite fsEntryEqRefl fe in
  Refl

--------------------------------------------------------------------------------
-- Internal helpers for `elem` / `all` reflexivity
--
-- Idris2 0.8.0's `elem` desugars through the `Foldable` interface to
-- `foldl (\acc, e => acc || Delay (x == e)) False xs`, not the textbook
-- `(x == y) || elem x ys` recursion. So the proofs below pattern-match
-- the foldl form directly.
--------------------------------------------------------------------------------

||| Once the foldl accumulator hits `True`, the result is `True`
||| regardless of the remaining list. `True || _` reduces by the first
||| pattern of `Prelude.Bool.||` without forcing the lazy argument.
private
foldlOrTrueIdempotent : (xs : List a) -> (g : a -> Lazy Bool) ->
                        foldl (\acc, e => acc || g e) True xs = True
foldlOrTrueIdempotent []        _ = Refl
foldlOrTrueIdempotent (_ :: ys) g = foldlOrTrueIdempotent ys g

||| `elem x (x :: ys) = True` given `x == x = True`.
||| Threads the accumulator from `False || (x == x)` to `True`, then
||| relies on `foldlOrTrueIdempotent` for the tail.
private
elemHere : Eq a => (x : a) -> (refl : (x == x) = True) -> (ys : List a) ->
           elem x (x :: ys) = True
elemHere x refl ys =
  rewrite refl in foldlOrTrueIdempotent ys (\e => x == e)

||| If the accumulator starts `True` instead of `False`, the foldl
||| stays `True` regardless of the list / element comparisons. This is
||| the structural lift used by `elemWeaken`.
private
foldlOrAccTrueStays : (xs : List a) -> (g : a -> Lazy Bool) -> (b : Bool) ->
                      foldl (\acc, e => acc || g e) b xs = True ->
                      foldl (\acc, e => acc || g e) (b || True) xs = True
foldlOrAccTrueStays xs g True  prf = prf
foldlOrAccTrueStays xs g False prf = foldlOrTrueIdempotent xs g

||| `elem` weakens on the right via the foldl form: an extra cons in
||| front does not change the result once the accumulator has been
||| forced True somewhere in the tail.
private
elemWeaken : Eq a => (x, y : a) -> (ys : List a) ->
             elem x ys = True -> elem x (y :: ys) = True
elemWeaken x y ys prf with (x == y)
  elemWeaken x y ys prf | True  = foldlOrTrueIdempotent ys (\e => x == e)
  elemWeaken x y ys prf | False = prf

||| For a list of entries where `==` is reflexive on the element type,
||| every element is `elem` of the list (with `Elem` witness).
private
allElemSelfHelper :
  (xs, fullList : List (Path, FSEntry)) ->
  ((e : (Path, FSEntry)) -> Elem e xs -> elem e fullList = True) ->
  all (\e => elem e fullList) xs = True
allElemSelfHelper []        _        _   = Refl
allElemSelfHelper (x :: rs) fullList prf =
  rewrite prf x Here in
  allElemSelfHelper rs fullList (\e, isIn => prf e (There isIn))

||| Every element of an entries list is `elem` of itself.
private
allElemSelf :
  (xs : List (Path, FSEntry)) -> all (\e => elem e xs) xs = True
allElemSelf xs = allElemSelfHelper xs xs (\e, isIn => elemSelfWitness e xs isIn)
  where
    elemSelfWitness :
      (e : (Path, FSEntry)) -> (ys : List (Path, FSEntry)) ->
      Elem e ys -> elem e ys = True
    elemSelfWitness e (e :: rest)  Here          =
      elemHere e (entryEqRefl e) rest
    elemSelfWitness e (y :: rest) (There later) =
      elemWeaken e y rest (elemSelfWitness e rest later)

||| Reflexivity of equivalence. Closure path (Q1-C pilot, 2026-06-02 PM):
||| structural induction over the entries list using the primitive-eq
||| axioms registered in `Filesystem.Axioms`.
export
equivRefl : (fs : Filesystem) -> equiv fs fs = True
equivRefl (MkFS entries) =
  rewrite allElemSelf entries in Refl

||| Symmetry of equivalence.
|||
||| Closed via `Data.Bool.andCommutative` from Idris2 0.8.0's base
||| stdlib. The two `all`-predicates inside `equiv` are conjoined; the
||| reverse-direction goal is the same conjunction commuted, so a
||| single rewrite by `andCommutative` collapses it to the premise.
|||
||| Does NOT need primitive String/Bits8 `==` reflexivity — this is
||| pure boolean algebra over the already-evaluated predicate values.
||| Contrast with `equivRefl` / `equivTrans`, which DO require leaf-
||| level eq-reflexivity (tracked separately under issue #119).
export
equivSym : (fs1, fs2 : Filesystem) ->
           equiv fs1 fs2 = True ->
           equiv fs2 fs1 = True
equivSym (MkFS e1) (MkFS e2) prf =
  rewrite andCommutative (all (\e => elem e e1) e2)
                         (all (\e => elem e e2) e1)
  in prf

||| Transitivity of equivalence
export
equivTrans : (fs1, fs2, fs3 : Filesystem) ->
             equiv fs1 fs2 = True ->
             equiv fs2 fs3 = True ->
             equiv fs1 fs3 = True
equivTrans fs1 fs2 fs3 prf1 prf2 = ?equivTransProof

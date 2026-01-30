-- SPDX-License-Identifier: PLMP-1.0-or-later
-- Filesystem Model - Core Types and Definitions
--
-- This module defines the abstract filesystem model used throughout
-- the valence-shell verification. All operations are total and proven
-- to terminate.

module Filesystem.Model

import Data.List
import Data.String
import Decidable.Equality

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
  decEq Root (Cons _ _) = No absurd
  decEq (Cons _ _) Root = No absurd
  decEq (Cons x xs) (Cons y ys) with (decEq x y)
    decEq (Cons x xs) (Cons x ys) | Yes Refl with (decEq xs ys)
      decEq (Cons x xs) (Cons x xs) | Yes Refl | Yes Refl = Yes Refl
      decEq (Cons x xs) (Cons x ys) | Yes Refl | No contra =
        No (\Refl => contra Refl)
    decEq (Cons x xs) (Cons y ys) | No contra =
      No (\Refl => contra Refl)

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

||| Remove an entry from filesystem
export
removeEntry : Path -> Filesystem -> Filesystem
removeEntry p (MkFS entries) =
  MkFS (filter (\(q, _) => p /= q) entries)

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

||| Reflexivity of equivalence
export
equivRefl : (fs : Filesystem) -> equiv fs fs = True
equivRefl (MkFS entries) = Refl

||| Symmetry of equivalence
export
equivSym : (fs1, fs2 : Filesystem) ->
           equiv fs1 fs2 = True ->
           equiv fs2 fs1 = True
equivSym (MkFS e1) (MkFS e2) prf = ?equivSymProof

||| Transitivity of equivalence
export
equivTrans : (fs1, fs2, fs3 : Filesystem) ->
             equiv fs1 fs2 = True ->
             equiv fs2 fs3 = True ->
             equiv fs1 fs3 = True
equivTrans fs1 fs2 fs3 prf1 prf2 = ?equivTransProof

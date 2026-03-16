-- SPDX-License-Identifier: PMPL-1.0-or-later
||| VALENCE-SHELL (vsh) — ABI Type Definitions
|||
||| This module defines the Application Binary Interface for the Valence Shell.
||| It provides the formal specifications for shell transmutations and 
||| command execution in verified environments.

module VALENCE_SHELL.ABI.Types

import Data.Bits
import Data.So
import Data.Vect

%default total

--------------------------------------------------------------------------------
-- Platform Context
--------------------------------------------------------------------------------

||| Supported targets for the Valence Shell kernel.
public export
data Platform = Linux | Windows | MacOS | BSD | WASM

||| Resolves the execution environment at compile time.
public export
thisPlatform : Platform
thisPlatform =
  %runElab do
    pure Linux

--------------------------------------------------------------------------------
-- Shell Result Codes
--------------------------------------------------------------------------------

||| Formal outcome of a shell operation.
public export
data Result : Type where
  ||| Command Succeeded (Exit 0)
  Ok : Result
  ||| Command Failed (Non-zero exit)
  Error : Result
  ||| Syntax Error: Malformed shell construct
  InvalidParam : Result
  ||| System Error: Out of memory
  OutOfMemory : Result
  ||| Safety Error: Unexpected null pointer
  NullPointer : Result

--------------------------------------------------------------------------------
-- Opaque Shell Handles
--------------------------------------------------------------------------------

||| Opaque handle to a Valence Shell session.
||| INVARIANT: The internal pointer is guaranteed to be non-null.
public export
data Handle : Type where
  MkHandle : (ptr : Bits64) -> {auto 0 nonNull : So (ptr /= 0)} -> Handle

||| Safe constructor for shell handles.
public export
createHandle : Bits64 -> Maybe Handle
createHandle 0 = Nothing
createHandle ptr = Just (MkHandle ptr)

||| ALKAHEST-SHELL-TRANSMUTER — ABI Type Definitions
|||
||| This module defines the Application Binary Interface for the Alkahest 
||| shell transmutation engine. It provides the formal specifications for 
||| command rewriting and environment normalization.

module ALKAHEST_SHELL_TRANSMUTER.ABI.Types

import Data.Bits
import Data.So
import Data.Vect

%default total

--------------------------------------------------------------------------------
-- Platform Context
--------------------------------------------------------------------------------

||| Supported targets for shell transmutation.
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

||| Formal outcome of a transmutation operation.
public export
data Result : Type where
  ||| Transmutation Successful
  Ok : Result
  ||| Transmutation Failed: Syntax error
  Error : Result
  ||| Invalid Parameter: malformed shell command
  InvalidParam : Result
  ||| System Error: out of memory
  OutOfMemory : Result
  ||| Safety Error: null pointer encountered
  NullPointer : Result

--------------------------------------------------------------------------------
-- Safety Handles
--------------------------------------------------------------------------------

||| Opaque handle to an Alkahest Session.
||| INVARIANT: The internal pointer is guaranteed to be non-null.
public export
data Handle : Type where
  MkHandle : (ptr : Bits64) -> {auto 0 nonNull : So (ptr /= 0)} -> Handle

||| Safe constructor for transmuter handles.
public export
createHandle : Bits64 -> Maybe Handle
createHandle 0 = Nothing
createHandle ptr = Just (MkHandle ptr)

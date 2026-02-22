||| VALENCE-SHELL (vsh) — FFI Bridge Declarations
|||
||| This module defines the formal bridge to the valence-shell native 
||| implementation. It ensures that shell transmutations and command 
||| execution are handled with strict type safety.

module VALENCE_SHELL.ABI.Foreign

import VALENCE_SHELL.ABI.Types
import VALENCE_SHELL.ABI.Layout

%default total

--------------------------------------------------------------------------------
-- Lifecycle
--------------------------------------------------------------------------------

||| Initializes the shell transmutation engine.
export
%foreign "C:vsh_init, libvsh"
prim__init : PrimIO Bits64

||| Safe initialization wrapper.
export
init : IO (Maybe Handle)
init = do
  ptr <- primIO prim__init
  pure (createHandle ptr)

||| Releases shell engine resources.
export
%foreign "C:vsh_free, libvsh"
prim__free : Bits64 -> PrimIO ()

||| Safe cleanup wrapper.
export
free : Handle -> IO ()
free h = primIO (prim__free (handlePtr h))

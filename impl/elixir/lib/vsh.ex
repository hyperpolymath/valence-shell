# SPDX-License-Identifier: AGPL-3.0-or-later

defmodule VSH do
  @moduledoc """
  Valence Shell - Formally Verified Reversible Shell

  A thermodynamic shell where every operation can be undone.
  Backed by ~256 theorems across 6 proof systems:
  - Coq (Calculus of Inductive Constructions)
  - Lean 4 (Dependent Type Theory)
  - Agda (Intensional Type Theory)
  - Isabelle/HOL (Higher-Order Logic)
  - Mizar (Tarski-Grothendieck Set Theory)
  - Z3 (SMT Automated Verification)

  ## Architecture

  ```
  ┌─────────────────────────────────────────────────────────┐
  │                    Clients                              │
  │  ┌─────────┐  ┌──────────────┐  ┌─────────────────┐    │
  │  │ vsh CLI │  │ MCP Server   │  │ Other Clients   │    │
  │  │ (Rust)  │  │ (ReScript)   │  │ (Any Language)  │    │
  │  └────┬────┘  └──────┬───────┘  └────────┬────────┘    │
  │       │              │                    │             │
  │       └──────────────┼────────────────────┘             │
  │                      │                                  │
  │              Unix Socket / JSON-RPC                     │
  │                      │                                  │
  ├──────────────────────┼──────────────────────────────────┤
  │                      ▼                                  │
  │  ┌─────────────────────────────────────────────────┐   │
  │  │            VSH.Daemon (GenServer)               │   │
  │  │  - JSON-RPC request handling                    │   │
  │  │  - Protocol translation                         │   │
  │  └─────────────────────┬───────────────────────────┘   │
  │                        │                                │
  │                        ▼                                │
  │  ┌─────────────────────────────────────────────────┐   │
  │  │            VSH.State (GenServer)                │   │
  │  │  - Operation history with undo/redo             │   │
  │  │  - Transaction management                       │   │
  │  │  - Proof reference tracking                     │   │
  │  └─────────────────────┬───────────────────────────┘   │
  │                        │                                │
  │                        ▼                                │
  │  ┌─────────────────────────────────────────────────┐   │
  │  │           VSH.Filesystem                        │   │
  │  │  - POSIX operations with precondition checks    │   │
  │  │  - Matches Coq specification                    │   │
  │  └─────────────────────┬───────────────────────────┘   │
  │                        │                                │
  │                   (Future: NIF)                         │
  │                        │                                │
  │                        ▼                                │
  │  ┌─────────────────────────────────────────────────┐   │
  │  │           Zig FFI Layer                         │   │
  │  │  - Compiled precondition checking               │   │
  │  │  - Audit logging for MAA                        │   │
  │  │  - C ABI for cross-runtime use                  │   │
  │  └─────────────────────┬───────────────────────────┘   │
  │                        │                                │
  │                        ▼                                │
  │  ┌─────────────────────────────────────────────────┐   │
  │  │              POSIX Syscalls                     │   │
  │  └─────────────────────────────────────────────────┘   │
  │                                                         │
  │                     BEAM VM                             │
  └─────────────────────────────────────────────────────────┘
  ```

  ## Trust Model

  ✓ Formal proofs verified by proof assistant kernels
  ✓ Zig FFI layer checks preconditions
  ✓ Elixir/BEAM maintains undo stack
  ✓ Rust CLI provides user interface
  ○ POSIX semantics assumed correct (OS trust)

  ## Verification Gap

  The FFI layer is NOT mechanically verified.
  It implements precondition checks derived from proofs.
  Full end-to-end verification requires:
  - Formal POSIX semantics model
  - Refinement proof from abstract to concrete
  - Verified compilation chain
  """

  @doc """
  Get the version of the Valence Shell.
  """
  def version, do: "0.1.0"

  @doc """
  Get the number of theorems across all proof systems.
  """
  def theorem_count, do: 256

  @doc """
  Get the list of proof systems used.
  """
  def proof_systems do
    ["Coq", "Lean 4", "Agda", "Isabelle/HOL", "Mizar", "Z3"]
  end
end

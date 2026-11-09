# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

defmodule VSH do
  @moduledoc """
  Valence Shell - Formally Verified Reversible Shell

  A shell with *algorithmically* reversible operations: for the operations
  that are modelled as reversible, undo is proven in the abstract model.
  This is not thermodynamic (Landauer/Bennett) reversibility, and the
  irreversible `obliterate` operation is deliberately not undoable.
  Checked proof systems (per-obligation status: EXPLAINME.adoc#proof-ledger):
  - Agda (Intensional Type Theory) — theory source
  - Lean 4 (Dependent Type Theory) — recheck leg
  - Coq (Calculus of Inductive Constructions) — recheck leg
  - Z3 (SMT) — supplementary
  Isabelle/HOL and Mizar were archived unchecked on 2026-11-09.

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
  Theorem-candidate count from the 2026-06-01 census, which counted six proof
  systems. Isabelle/HOL and Mizar have since been archived unchecked, so this is
  a historical figure, not current checked evidence; see
  EXPLAINME.adoc#proof-ledger.
  """
  def theorem_count, do: 478

  @doc """
  Get the list of proof systems that are currently checked.
  """
  def proof_systems do
    ["Agda", "Lean 4", "Coq", "Z3"]
  end
end

-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
/- Valence Shell — Executable model oracle.

   A tiny CLI that drives the *proven* Lean filesystem model
   (`mkdir`/`rmdir`/`createFile`/`deleteFile`/`fsUpdate` from FilesystemModel +
   FileOperations — the exact `def`s the correspondence theorems are about) and
   reports the resulting node type at a set of probe paths.

   This makes the compiled proof artifact the oracle for differential testing
   against the Rust implementation (see impl/rust-cli/tests/model_oracle_correspondence.rs
   and docs/LEAN4_RUST_CORRESPONDENCE.md).

   Protocol (stdin):
     one operation per line, then a line "---", then one probe path per line.
     Operations: `MKDIR p`, `RMDIR p`, `TOUCH p`, `RM p`  (p is a '/'-joined path).
   Output (stdout): one line per probe, in order — `DIR`, `FILE`, or `NONE`.
-/
import FilesystemModel
import FileOperations

/-- Parse a '/'-joined string into a model `Path` (list of components). -/
def parsePath (s : String) : Path :=
  (s.splitOn "/").filter (· ≠ "")

/-- Apply one operation line to the model filesystem. Unknown verbs are no-ops. -/
def applyOp (fs : Filesystem) (line : String) : Filesystem :=
  match line.trim.splitOn " " with
  | verb :: rest =>
    let p := parsePath (String.intercalate " " rest)
    match verb with
    | "MKDIR" => mkdir p fs
    | "RMDIR" => rmdir p fs
    | "TOUCH" => createFile p fs
    | "RM"    => deleteFile p fs
    | _       => fs
  | [] => fs

/-- Query the model for the node type at a probe path. -/
def probe (fs : Filesystem) (s : String) : String :=
  match fs (parsePath s) with
  | none => "NONE"
  | some node =>
    match node.nodeType with
    | FSNodeType.directory => "DIR"
    | FSNodeType.file      => "FILE"

/-- Read all lines from a stream until EOF (getLine returns "" at end). -/
partial def readAllLines (s : IO.FS.Stream) (acc : List String) : IO (List String) := do
  let line ← s.getLine
  if line == "" then
    return acc.reverse
  else
    readAllLines s (line.trim :: acc)

def main : IO Unit := do
  let stdin ← IO.getStdin
  let raw : List String ← readAllLines stdin []
  let lines : List String := raw.filter (· ≠ "")
  let ops : List String := lines.takeWhile (· ≠ "---")
  let probes : List String := (lines.dropWhile (· ≠ "---")).drop 1
  let finalFS : Filesystem := ops.foldl applyOp emptyFS
  for pr in probes do
    IO.println (probe finalFS pr)

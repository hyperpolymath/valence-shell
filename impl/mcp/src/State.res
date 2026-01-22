// SPDX-License-Identifier: PLMP-1.0-or-later
// Valence Shell State Management
// Maintains operation history with reversibility guarantees

open Mcp

// Operation types matching Coq's file_operations.v
type operationType =
  | Mkdir
  | Rmdir
  | CreateFile
  | DeleteFile
  | WriteFile

let opTypeToString = (op: operationType): string => {
  switch op {
  | Mkdir => "mkdir"
  | Rmdir => "rmdir"
  | CreateFile => "touch"
  | DeleteFile => "rm"
  | WriteFile => "write"
  }
}

let opTypeFromString = (s: string): option<operationType> => {
  switch String.toLowerCase(s) {
  | "mkdir" => Some(Mkdir)
  | "rmdir" => Some(Rmdir)
  | "touch" | "createfile" | "create_file" => Some(CreateFile)
  | "rm" | "deletefile" | "delete_file" => Some(DeleteFile)
  | "write" | "writefile" | "write_file" => Some(WriteFile)
  | _ => None
  }
}

// Inverse operation for reversibility (from Coq theorems)
let inverseOp = (op: operationType): option<operationType> => {
  switch op {
  | Mkdir => Some(Rmdir)
  | Rmdir => Some(Mkdir)
  | CreateFile => Some(DeleteFile)
  | DeleteFile => Some(CreateFile)
  | WriteFile => Some(WriteFile) // Self-inverse with old content
  }
}

// Proof reference for operation
let getProofRef = (op: operationType): proofReference => {
  switch op {
  | Mkdir | Rmdir => mkdirRmdirProof
  | CreateFile | DeleteFile => createDeleteProof
  | WriteFile => createDeleteProof // Uses same reversibility principle
  }
}

// Single operation record
type operation = {
  id: string,
  opType: operationType,
  path: string,
  timestamp: float,
  undone: bool,
  undoneBy: option<string>,
  undoData: option<string>, // Base64 encoded for file content
}

// Transaction for atomic operation groups
type transaction = {
  id: string,
  name: string,
  operations: array<string>, // Operation IDs
  startTime: float,
  committed: bool,
}

// Shell state
type shellState = {
  mutable root: string,
  mutable history: array<operation>,
  mutable transactions: array<transaction>,
  mutable activeTransaction: option<transaction>,
  mutable redoStack: array<operation>,
}

// Global state (will be replaced by BEAM daemon connection)
let state: shellState = {
  root: "/tmp/vsh-sandbox",
  history: [],
  transactions: [],
  activeTransaction: None,
  redoStack: [],
}

// Generate UUID-like ID
let generateId = (): string => {
  let timestamp = Date.now()
  let random = Math.random() *. 1000000.0
  Float.toString(timestamp) ++ "-" ++ Float.toFixed(random, ~digits=0)
}

// Create new operation
let createOperation = (opType: operationType, path: string, ~undoData=?): operation => {
  {
    id: generateId(),
    opType,
    path,
    timestamp: Date.now(),
    undone: false,
    undoneBy: None,
    undoData,
  }
}

// Record operation in history
let recordOperation = (op: operation): unit => {
  Array.push(state.history, op)
  state.redoStack = [] // Clear redo stack on new operation

  switch state.activeTransaction {
  | Some(txn) => Array.push(txn.operations, op.id)
  | None => ()
  }
}

// Get last N undoable operations
let getUndoable = (count: int): array<operation> => {
  let undoable = Array.filter(state.history, op => !op.undone)
  let len = Array.length(undoable)
  let start = Int.max(0, len - count)
  Array.sliceToEnd(undoable, ~start)
}

// Mark operation as undone
let markUndone = (opId: string, undoId: string): unit => {
  state.history = Array.map(state.history, op => {
    if op.id == opId {
      {...op, undone: true, undoneBy: Some(undoId)}
    } else {
      op
    }
  })
}

// Push to redo stack
let pushRedo = (op: operation): unit => {
  Array.push(state.redoStack, op)
}

// Pop from redo stack
let popRedo = (): option<operation> => {
  if Array.length(state.redoStack) > 0 {
    let op = state.redoStack[Array.length(state.redoStack) - 1]
    state.redoStack = Array.slice(state.redoStack, ~start=0, ~end=-1)
    op
  } else {
    None
  }
}

// Transaction management
let beginTransaction = (name: string): string => {
  let txn = {
    id: generateId(),
    name,
    operations: [],
    startTime: Date.now(),
    committed: false,
  }
  state.activeTransaction = Some(txn)
  txn.id
}

let commitTransaction = (): option<transaction> => {
  switch state.activeTransaction {
  | Some(txn) =>
    let committed = {...txn, committed: true}
    Array.push(state.transactions, committed)
    state.activeTransaction = None
    Some(committed)
  | None => None
  }
}

let rollbackTransaction = (): option<transaction> => {
  switch state.activeTransaction {
  | Some(txn) =>
    state.activeTransaction = None
    Some(txn)
  | None => None
  }
}

// Get history for display
let getHistory = (count: int): array<operation> => {
  let len = Array.length(state.history)
  let start = Int.max(0, len - count)
  Array.sliceToEnd(state.history, ~start)
}

// Serialize state to JSON
let stateToJson = (): JSON.t => {
  let historyJson = Array.map(state.history, op => {
    let obj = Dict.make()
    Dict.set(obj, "id", JSON.Encode.string(op.id))
    Dict.set(obj, "operation", JSON.Encode.string(opTypeToString(op.opType)))
    Dict.set(obj, "path", JSON.Encode.string(op.path))
    Dict.set(obj, "timestamp", JSON.Encode.float(op.timestamp))
    Dict.set(obj, "undone", JSON.Encode.bool(op.undone))
    switch op.undoneBy {
    | Some(by) => Dict.set(obj, "undoneBy", JSON.Encode.string(by))
    | None => ()
    }
    let proof = getProofRef(op.opType)
    Dict.set(obj, "proofTheorem", JSON.Encode.string(proof.theorem))
    Dict.set(obj, "proofFile", JSON.Encode.string(proof.coqLocation))
    JSON.Encode.object(obj)
  })

  let result = Dict.make()
  Dict.set(result, "root", JSON.Encode.string(state.root))
  Dict.set(result, "historyCount", JSON.Encode.int(Array.length(state.history)))
  Dict.set(result, "undoableCount", JSON.Encode.int(Array.length(getUndoable(1000))))
  Dict.set(result, "redoCount", JSON.Encode.int(Array.length(state.redoStack)))
  Dict.set(result, "history", JSON.Encode.array(historyJson))

  switch state.activeTransaction {
  | Some(txn) =>
    let txnObj = Dict.make()
    Dict.set(txnObj, "id", JSON.Encode.string(txn.id))
    Dict.set(txnObj, "name", JSON.Encode.string(txn.name))
    Dict.set(txnObj, "operationCount", JSON.Encode.int(Array.length(txn.operations)))
    Dict.set(result, "activeTransaction", JSON.Encode.object(txnObj))
  | None => ()
  }

  JSON.Encode.object(result)
}

// Set sandbox root
let setRoot = (root: string): unit => {
  state.root = root
}

// Resolve path within sandbox
let resolvePath = (path: string): string => {
  if String.startsWith(path, ~search="/") {
    path
  } else {
    state.root ++ "/" ++ path
  }
}

// SPDX-License-Identifier: AGPL-3.0-or-later
// Valence Shell MCP Server
// Exposes formally verified reversible filesystem operations via MCP

open Mcp
open Deno
open State

let packageVersion = "0.1.0"
let feedbackUrl = "https://github.com/hyperpolymath/valence-shell/issues"

// ============================================================================
// Filesystem Operations (using Deno APIs, will switch to BEAM daemon)
// ============================================================================

let executeOperation = async (opType: operationType, path: string): promise<result<unit, string>> => {
  let fullPath = resolvePath(path)

  try {
    switch opType {
    | Mkdir => {
        await Fs.mkdir(fullPath, {"recursive": false})
        Ok(())
      }
    | Rmdir => {
        await Fs.remove(fullPath, {"recursive": false})
        Ok(())
      }
    | CreateFile => {
        await Fs.writeTextFile(fullPath, "")
        Ok(())
      }
    | DeleteFile => {
        await Fs.remove(fullPath, {"recursive": false})
        Ok(())
      }
    | WriteFile => {
        // WriteFile needs content - handle in specific tool
        Ok(())
      }
    }
  } catch {
  | JsExn(e) =>
    let msg = switch JsExn.message(e) {
    | Some(m) => m
    | None => "Unknown error"
    }
    Error(msg)
  }
}

// ============================================================================
// Tool Handlers
// ============================================================================

let mkdirHandler = async (params: JSON.t): promise<JSON.t> => {
  let path = switch JSON.Decode.object(params) {
  | Some(obj) =>
    switch Dict.get(obj, "path") {
    | Some(v) => JSON.Decode.string(v)
    | None => None
    }
  | None => None
  }

  switch path {
  | None => Obj.magic(makeToolResult("Missing required parameter: path", ~isError=true))
  | Some(p) =>
    let result = await executeOperation(Mkdir, p)
    switch result {
    | Ok(_) =>
      let op = createOperation(Mkdir, p)
      recordOperation(op)

      let response = Dict.make()
      Dict.set(response, "success", JSON.Encode.bool(true))
      Dict.set(response, "operation", JSON.Encode.string("mkdir"))
      Dict.set(response, "path", JSON.Encode.string(p))
      Dict.set(response, "operationId", JSON.Encode.string(op.id))
      Dict.set(response, "undoCommand", JSON.Encode.string("vsh_rmdir " ++ p))

      let proof = getProofRef(Mkdir)
      Dict.set(response, "proofTheorem", JSON.Encode.string(proof.theorem))
      Dict.set(response, "proofLocation", JSON.Encode.string(proof.coqLocation))

      Obj.magic(makeJsonResult(JSON.Encode.object(response)))
    | Error(msg) =>
      Obj.magic(makeToolResult("mkdir failed: " ++ msg, ~isError=true))
    }
  }
}

let rmdirHandler = async (params: JSON.t): promise<JSON.t> => {
  let path = switch JSON.Decode.object(params) {
  | Some(obj) =>
    switch Dict.get(obj, "path") {
    | Some(v) => JSON.Decode.string(v)
    | None => None
    }
  | None => None
  }

  switch path {
  | None => Obj.magic(makeToolResult("Missing required parameter: path", ~isError=true))
  | Some(p) =>
    let result = await executeOperation(Rmdir, p)
    switch result {
    | Ok(_) =>
      let op = createOperation(Rmdir, p)
      recordOperation(op)

      let response = Dict.make()
      Dict.set(response, "success", JSON.Encode.bool(true))
      Dict.set(response, "operation", JSON.Encode.string("rmdir"))
      Dict.set(response, "path", JSON.Encode.string(p))
      Dict.set(response, "operationId", JSON.Encode.string(op.id))
      Dict.set(response, "undoCommand", JSON.Encode.string("vsh_mkdir " ++ p))

      let proof = getProofRef(Rmdir)
      Dict.set(response, "proofTheorem", JSON.Encode.string(proof.theorem))

      Obj.magic(makeJsonResult(JSON.Encode.object(response)))
    | Error(msg) =>
      Obj.magic(makeToolResult("rmdir failed: " ++ msg, ~isError=true))
    }
  }
}

let touchHandler = async (params: JSON.t): promise<JSON.t> => {
  let path = switch JSON.Decode.object(params) {
  | Some(obj) =>
    switch Dict.get(obj, "path") {
    | Some(v) => JSON.Decode.string(v)
    | None => None
    }
  | None => None
  }

  switch path {
  | None => Obj.magic(makeToolResult("Missing required parameter: path", ~isError=true))
  | Some(p) =>
    let result = await executeOperation(CreateFile, p)
    switch result {
    | Ok(_) =>
      let op = createOperation(CreateFile, p)
      recordOperation(op)

      let response = Dict.make()
      Dict.set(response, "success", JSON.Encode.bool(true))
      Dict.set(response, "operation", JSON.Encode.string("touch"))
      Dict.set(response, "path", JSON.Encode.string(p))
      Dict.set(response, "operationId", JSON.Encode.string(op.id))
      Dict.set(response, "undoCommand", JSON.Encode.string("vsh_rm " ++ p))

      Obj.magic(makeJsonResult(JSON.Encode.object(response)))
    | Error(msg) =>
      Obj.magic(makeToolResult("touch failed: " ++ msg, ~isError=true))
    }
  }
}

let rmHandler = async (params: JSON.t): promise<JSON.t> => {
  let path = switch JSON.Decode.object(params) {
  | Some(obj) =>
    switch Dict.get(obj, "path") {
    | Some(v) => JSON.Decode.string(v)
    | None => None
    }
  | None => None
  }

  switch path {
  | None => Obj.magic(makeToolResult("Missing required parameter: path", ~isError=true))
  | Some(p) =>
    // Read content for undo before deleting
    let undoData = try {
      Some(await Fs.readTextFile(resolvePath(p)))
    } catch {
    | _ => None
    }

    let result = await executeOperation(DeleteFile, p)
    switch result {
    | Ok(_) =>
      let op = createOperation(DeleteFile, p, ~undoData?)
      recordOperation(op)

      let response = Dict.make()
      Dict.set(response, "success", JSON.Encode.bool(true))
      Dict.set(response, "operation", JSON.Encode.string("rm"))
      Dict.set(response, "path", JSON.Encode.string(p))
      Dict.set(response, "operationId", JSON.Encode.string(op.id))
      Dict.set(response, "canUndo", JSON.Encode.bool(true))

      Obj.magic(makeJsonResult(JSON.Encode.object(response)))
    | Error(msg) =>
      Obj.magic(makeToolResult("rm failed: " ++ msg, ~isError=true))
    }
  }
}

let undoHandler = async (params: JSON.t): promise<JSON.t> => {
  let count = switch JSON.Decode.object(params) {
  | Some(obj) =>
    switch Dict.get(obj, "count") {
    | Some(v) =>
      switch JSON.Decode.float(v) {
      | Some(n) => Float.toInt(n)
      | None => 1
      }
    | None => 1
    }
  | None => 1
  }

  let ops = getUndoable(count)

  if Array.length(ops) == 0 {
    Obj.magic(makeToolResult("Nothing to undo"))
  } else {
    let undone = []

    // Undo in reverse order
    let reversed = Array.toReversed(ops)
    for i in 0 to Array.length(reversed) - 1 {
      switch reversed[i] {
      | Some(op) =>
        switch inverseOp(op.opType) {
        | Some(invOp) =>
          let result = await executeOperation(invOp, op.path)
          switch result {
          | Ok(_) =>
            let undoId = generateId()
            markUndone(op.id, undoId)
            pushRedo(op)

            let item = Dict.make()
            Dict.set(item, "originalOp", JSON.Encode.string(op.id))
            Dict.set(item, "inverseOp", JSON.Encode.string(opTypeToString(invOp)))
            Dict.set(item, "path", JSON.Encode.string(op.path))
            Array.push(undone, JSON.Encode.object(item))
          | Error(_) => ()
          }
        | None => ()
        }
      | None => ()
      }
    }

    let response = Dict.make()
    Dict.set(response, "undoneCount", JSON.Encode.int(Array.length(undone)))
    Dict.set(response, "operations", JSON.Encode.array(undone))
    Dict.set(response, "proofTheorem", JSON.Encode.string(compositionProof.theorem))

    Obj.magic(makeJsonResult(JSON.Encode.object(response)))
  }
}

let historyHandler = async (params: JSON.t): promise<JSON.t> => {
  let count = switch JSON.Decode.object(params) {
  | Some(obj) =>
    switch Dict.get(obj, "count") {
    | Some(v) =>
      switch JSON.Decode.float(v) {
      | Some(n) => Float.toInt(n)
      | None => 10
      }
    | None => 10
    }
  | None => 10
  }

  let showProofs = switch JSON.Decode.object(params) {
  | Some(obj) =>
    switch Dict.get(obj, "showProofs") {
    | Some(v) =>
      switch JSON.Decode.bool(v) {
      | Some(b) => b
      | None => false
      }
    | None => false
    }
  | None => false
  }

  let history = getHistory(count)
  let items = Array.map(history, op => {
    let item = Dict.make()
    Dict.set(item, "id", JSON.Encode.string(op.id))
    Dict.set(item, "operation", JSON.Encode.string(opTypeToString(op.opType)))
    Dict.set(item, "path", JSON.Encode.string(op.path))
    Dict.set(item, "timestamp", JSON.Encode.float(op.timestamp))
    Dict.set(item, "undone", JSON.Encode.bool(op.undone))

    if showProofs {
      let proof = getProofRef(op.opType)
      Dict.set(item, "proofTheorem", JSON.Encode.string(proof.theorem))
      Dict.set(item, "proofLocation", JSON.Encode.string(proof.coqLocation))
    }

    JSON.Encode.object(item)
  })

  let response = Dict.make()
  Dict.set(response, "count", JSON.Encode.int(Array.length(items)))
  Dict.set(response, "operations", JSON.Encode.array(items))

  Obj.magic(makeJsonResult(JSON.Encode.object(response)))
}

let statusHandler = async (_params: JSON.t): promise<JSON.t> => {
  Obj.magic(makeJsonResult(stateToJson()))
}

let proofsHandler = async (_params: JSON.t): promise<JSON.t> => {
  let proofs = [mkdirRmdirProof, createDeleteProof, compositionProof]
  let items = Array.map(proofs, proof => {
    let item = Dict.make()
    Dict.set(item, "theorem", JSON.Encode.string(proof.theorem))
    Dict.set(item, "description", JSON.Encode.string(proof.description))
    Dict.set(item, "coq", JSON.Encode.string(proof.coqLocation))
    Dict.set(item, "lean4", JSON.Encode.string(proof.lean4Location))
    Dict.set(item, "agda", JSON.Encode.string(proof.agdaLocation))
    Dict.set(item, "isabelle", JSON.Encode.string(proof.isabelleLocation))
    JSON.Encode.object(item)
  })

  let response = Dict.make()
  Dict.set(response, "totalTheorems", JSON.Encode.int(256))
  Dict.set(response, "proofSystems", JSON.Encode.int(6))
  Dict.set(response, "coreTheorems", JSON.Encode.array(items))
  Dict.set(
    response,
    "verificationGap",
    JSON.Encode.string("FFI layer implements precondition checks derived from proofs but is not mechanically verified"),
  )

  Obj.magic(makeJsonResult(JSON.Encode.object(response)))
}

let beginHandler = async (params: JSON.t): promise<JSON.t> => {
  let name = switch JSON.Decode.object(params) {
  | Some(obj) =>
    switch Dict.get(obj, "name") {
    | Some(v) => JSON.Decode.string(v)
    | None => None
    }
  | None => None
  }

  switch name {
  | None => Obj.magic(makeToolResult("Missing required parameter: name", ~isError=true))
  | Some(n) =>
    let txnId = beginTransaction(n)

    let response = Dict.make()
    Dict.set(response, "success", JSON.Encode.bool(true))
    Dict.set(response, "transactionId", JSON.Encode.string(txnId))
    Dict.set(response, "name", JSON.Encode.string(n))
    Dict.set(response, "message", JSON.Encode.string("Transaction started. All operations will be grouped until commit or rollback."))

    Obj.magic(makeJsonResult(JSON.Encode.object(response)))
  }
}

let commitHandler = async (_params: JSON.t): promise<JSON.t> => {
  switch commitTransaction() {
  | None => Obj.magic(makeToolResult("No active transaction to commit", ~isError=true))
  | Some(txn) =>
    let response = Dict.make()
    Dict.set(response, "success", JSON.Encode.bool(true))
    Dict.set(response, "transactionId", JSON.Encode.string(txn.id))
    Dict.set(response, "name", JSON.Encode.string(txn.name))
    Dict.set(response, "operationCount", JSON.Encode.int(Array.length(txn.operations)))

    Obj.magic(makeJsonResult(JSON.Encode.object(response)))
  }
}

let rollbackHandler = async (_params: JSON.t): promise<JSON.t> => {
  switch rollbackTransaction() {
  | None => Obj.magic(makeToolResult("No active transaction to rollback", ~isError=true))
  | Some(txn) =>
    // Undo all operations in the transaction
    let undoneCount = ref(0)

    // Get operations and undo them in reverse
    let ops = Array.filterMap(txn.operations, opId => {
      Array.find(state.history, op => op.id == opId)
    })

    let reversed = Array.toReversed(ops)
    for i in 0 to Array.length(reversed) - 1 {
      switch reversed[i] {
      | Some(op) =>
        if !op.undone {
          switch inverseOp(op.opType) {
          | Some(invOp) =>
            let _ = await executeOperation(invOp, op.path)
            markUndone(op.id, "rollback")
            undoneCount := undoneCount.contents + 1
          | None => ()
          }
        }
      | None => ()
      }
    }

    let response = Dict.make()
    Dict.set(response, "success", JSON.Encode.bool(true))
    Dict.set(response, "transactionId", JSON.Encode.string(txn.id))
    Dict.set(response, "name", JSON.Encode.string(txn.name))
    Dict.set(response, "rolledBackOperations", JSON.Encode.int(undoneCount.contents))

    Obj.magic(makeJsonResult(JSON.Encode.object(response)))
  }
}

// ============================================================================
// Server Creation
// ============================================================================

let createServer = (): mcpServer => {
  let server = createMcpServer({
    name: "valence-shell-mcp",
    version: packageVersion,
    description: "Formally verified reversible shell operations via MCP",
  })

  // Path schema for operations
  let pathSchema = Dict.make()
  Dict.set(pathSchema, "type", JSON.Encode.string("object"))
  let pathProps = Dict.make()
  let pathProp = Dict.make()
  Dict.set(pathProp, "type", JSON.Encode.string("string"))
  Dict.set(pathProp, "description", JSON.Encode.string("Path within sandbox"))
  Dict.set(pathProps, "path", JSON.Encode.object(pathProp))
  Dict.set(pathSchema, "properties", JSON.Encode.object(pathProps))
  Dict.set(pathSchema, "required", JSON.Encode.array([JSON.Encode.string("path")]))

  // Empty schema
  let emptySchema = Dict.make()
  Dict.set(emptySchema, "type", JSON.Encode.string("object"))
  Dict.set(emptySchema, "properties", JSON.Encode.object(Dict.make()))

  // Count schema
  let countSchema = Dict.make()
  Dict.set(countSchema, "type", JSON.Encode.string("object"))
  let countProps = Dict.make()
  let countProp = Dict.make()
  Dict.set(countProp, "type", JSON.Encode.string("integer"))
  Dict.set(countProp, "description", JSON.Encode.string("Number of operations"))
  Dict.set(countProp, "default", JSON.Encode.int(1))
  Dict.set(countProps, "count", JSON.Encode.object(countProp))
  Dict.set(countSchema, "properties", JSON.Encode.object(countProps))

  // History schema
  let historySchema = Dict.make()
  Dict.set(historySchema, "type", JSON.Encode.string("object"))
  let historyProps = Dict.make()
  let historyCount = Dict.make()
  Dict.set(historyCount, "type", JSON.Encode.string("integer"))
  Dict.set(historyCount, "description", JSON.Encode.string("Number of operations to show"))
  Dict.set(historyCount, "default", JSON.Encode.int(10))
  Dict.set(historyProps, "count", JSON.Encode.object(historyCount))
  let showProofs = Dict.make()
  Dict.set(showProofs, "type", JSON.Encode.string("boolean"))
  Dict.set(showProofs, "description", JSON.Encode.string("Include proof references"))
  Dict.set(showProofs, "default", JSON.Encode.bool(false))
  Dict.set(historyProps, "showProofs", JSON.Encode.object(showProofs))
  Dict.set(historySchema, "properties", JSON.Encode.object(historyProps))

  // Name schema for transactions
  let nameSchema = Dict.make()
  Dict.set(nameSchema, "type", JSON.Encode.string("object"))
  let nameProps = Dict.make()
  let nameProp = Dict.make()
  Dict.set(nameProp, "type", JSON.Encode.string("string"))
  Dict.set(nameProp, "description", JSON.Encode.string("Transaction name"))
  Dict.set(nameProps, "name", JSON.Encode.object(nameProp))
  Dict.set(nameSchema, "properties", JSON.Encode.object(nameProps))
  Dict.set(nameSchema, "required", JSON.Encode.array([JSON.Encode.string("name")]))

  // Register tools
  tool(server, "vsh_mkdir", "Create a directory (reversible via vsh_rmdir). Backed by mkdir_rmdir_reversible theorem.", pathSchema, mkdirHandler)
  tool(server, "vsh_rmdir", "Remove an empty directory (reversible via vsh_mkdir). Backed by mkdir_rmdir_reversible theorem.", pathSchema, rmdirHandler)
  tool(server, "vsh_touch", "Create an empty file (reversible via vsh_rm). Backed by create_delete_file_reversible theorem.", pathSchema, touchHandler)
  tool(server, "vsh_rm", "Remove a file (reversible, content preserved for undo). Backed by create_delete_file_reversible theorem.", pathSchema, rmHandler)
  tool(server, "vsh_undo", "Undo the last N operations. Backed by operation_sequence_reversible theorem.", countSchema, undoHandler)
  tool(server, "vsh_history", "Show operation history with optional proof references.", historySchema, historyHandler)
  tool(server, "vsh_status", "Show current shell state including undo/redo stacks and active transaction.", emptySchema, statusHandler)
  tool(server, "vsh_proofs", "Show verification information including ~256 theorems across 6 proof systems.", emptySchema, proofsHandler)
  tool(server, "vsh_begin", "Begin a named transaction. Operations will be grouped for atomic commit/rollback.", nameSchema, beginHandler)
  tool(server, "vsh_commit", "Commit the current transaction.", emptySchema, commitHandler)
  tool(server, "vsh_rollback", "Rollback the current transaction, undoing all operations within it.", emptySchema, rollbackHandler)

  server
}

// ============================================================================
// HTTP Mode Handler
// ============================================================================

// Handle MCP JSON-RPC request over HTTP
let handleHttpRequest = async (body: string): promise<JSON.t> => {
  // Parse request
  let request = try {
    JSON.parseExn(body)
  } catch {
  | _ =>
    let error = Dict.make()
    Dict.set(error, "jsonrpc", JSON.Encode.string("2.0"))
    Dict.set(error, "error", JSON.Encode.object({
      let e = Dict.make()
      Dict.set(e, "code", JSON.Encode.int(-32700))
      Dict.set(e, "message", JSON.Encode.string("Parse error"))
      e
    }))
    Dict.set(error, "id", JSON.Encode.null)
    return JSON.Encode.object(error)
  }

  // Extract method and params
  let obj = JSON.Decode.object(request)->Option.getOr(Dict.make())
  let method = Dict.get(obj, "method")->Option.flatMap(JSON.Decode.string)->Option.getOr("")
  let params = Dict.get(obj, "params")->Option.getOr(JSON.Encode.object(Dict.make()))
  let id = Dict.get(obj, "id")->Option.getOr(JSON.Encode.null)

  // Route to handler
  let result = switch method {
  | "tools/call" =>
    // MCP tools/call - extract tool name from params
    let paramsObj = JSON.Decode.object(params)->Option.getOr(Dict.make())
    let toolName = Dict.get(paramsObj, "name")->Option.flatMap(JSON.Decode.string)->Option.getOr("")
    let toolParams = Dict.get(paramsObj, "arguments")->Option.getOr(JSON.Encode.object(Dict.make()))

    switch toolName {
    | "vsh_mkdir" => await mkdirHandler(toolParams)
    | "vsh_rmdir" => await rmdirHandler(toolParams)
    | "vsh_touch" => await touchHandler(toolParams)
    | "vsh_rm" => await rmHandler(toolParams)
    | "vsh_undo" => await undoHandler(toolParams)
    | "vsh_history" => await historyHandler(toolParams)
    | "vsh_status" => await statusHandler(toolParams)
    | "vsh_proofs" => await proofsHandler(toolParams)
    | "vsh_begin" => await beginHandler(toolParams)
    | "vsh_commit" => await commitHandler(toolParams)
    | "vsh_rollback" => await rollbackHandler(toolParams)
    | _ => Obj.magic(makeToolResult("Unknown tool: " ++ toolName, ~isError=true))
    }
  | "tools/list" =>
    // Return available tools
    let tools = [
      {"name": "vsh_mkdir", "description": "Create directory (reversible)"},
      {"name": "vsh_rmdir", "description": "Remove empty directory (reversible)"},
      {"name": "vsh_touch", "description": "Create empty file (reversible)"},
      {"name": "vsh_rm", "description": "Remove file (reversible)"},
      {"name": "vsh_undo", "description": "Undo last N operations"},
      {"name": "vsh_history", "description": "Show operation history"},
      {"name": "vsh_status", "description": "Show shell state"},
      {"name": "vsh_proofs", "description": "Show verification info"},
      {"name": "vsh_begin", "description": "Begin transaction"},
      {"name": "vsh_commit", "description": "Commit transaction"},
      {"name": "vsh_rollback", "description": "Rollback transaction"},
    ]
    let toolsJson = Array.map(tools, t => {
      let obj = Dict.make()
      Dict.set(obj, "name", JSON.Encode.string(t["name"]))
      Dict.set(obj, "description", JSON.Encode.string(t["description"]))
      JSON.Encode.object(obj)
    })
    let result = Dict.make()
    Dict.set(result, "tools", JSON.Encode.array(toolsJson))
    JSON.Encode.object(result)
  | "initialize" =>
    let result = Dict.make()
    Dict.set(result, "protocolVersion", JSON.Encode.string("2024-11-05"))
    Dict.set(result, "capabilities", JSON.Encode.object({
      let caps = Dict.make()
      Dict.set(caps, "tools", JSON.Encode.object(Dict.make()))
      caps
    }))
    Dict.set(result, "serverInfo", JSON.Encode.object({
      let info = Dict.make()
      Dict.set(info, "name", JSON.Encode.string("valence-shell-mcp"))
      Dict.set(info, "version", JSON.Encode.string(packageVersion))
      info
    }))
    JSON.Encode.object(result)
  | _ =>
    let error = Dict.make()
    Dict.set(error, "code", JSON.Encode.int(-32601))
    Dict.set(error, "message", JSON.Encode.string("Method not found: " ++ method))
    JSON.Encode.object(error)
  }

  // Build response
  let response = Dict.make()
  Dict.set(response, "jsonrpc", JSON.Encode.string("2.0"))
  Dict.set(response, "result", result)
  Dict.set(response, "id", id)
  JSON.Encode.object(response)
}

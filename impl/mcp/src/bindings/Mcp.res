// SPDX-License-Identifier: PMPL-1.0-or-later
// MCP SDK bindings for ReScript - Valence Shell

// toolHandler type matches what the MCP SDK expects at the JS runtime boundary.
// toolResult is structurally a JS object that the SDK handles as JSON.t.
// We use a dedicated coercion (toolResultToJson) instead of scattered Obj.magic.
type toolHandler = JSON.t => promise<JSON.t>

// Safe coercion: toolResult is a plain JS record that the MCP SDK treats as JSON.t
// at the FFI boundary. This replaces all Obj.magic calls in Server.res.
let toolResultToJson: toolResult => JSON.t = result => {
  let obj = Dict.make()
  let contentArr = Array.map(result.content, item => {
    let itemObj = Dict.make()
    Dict.set(itemObj, "type", JSON.Encode.string(item.type_))
    Dict.set(itemObj, "text", JSON.Encode.string(item.text))
    JSON.Encode.object(itemObj)
  })
  Dict.set(obj, "content", JSON.Encode.array(contentArr))
  switch result.isError {
  | Some(true) => Dict.set(obj, "isError", JSON.Encode.bool(true))
  | _ => ()
  }
  JSON.Encode.object(obj)
}

type toolSchema = {
  @as("type") type_: string,
  properties: dict<JSON.t>,
  required?: array<string>,
}

type mcpTool = {
  name: string,
  description: string,
  inputSchema: toolSchema,
}

type serverCapabilities = {
  tools: {listChanged: bool},
}

type serverInfo = {
  name: string,
  version: string,
  description?: string,
}

type mcpServerConfig = {
  name: string,
  version: string,
  description?: string,
}

// STDIO Transport binding
type stdioTransport

@module("@modelcontextprotocol/sdk/server/stdio.js") @new
external createStdioTransport: unit => stdioTransport = "StdioServerTransport"

// MCP Server class binding
type mcpServer

@module("@modelcontextprotocol/sdk/server/mcp.js") @new
external createMcpServer: mcpServerConfig => mcpServer = "McpServer"

@send
external tool: (mcpServer, string, string, dict<JSON.t>, toolHandler) => unit = "tool"

@send
external connect: (mcpServer, stdioTransport) => promise<unit> = "connect"

// Tool result types
type contentItem = {
  @as("type") type_: string,
  text: string,
}

type toolResult = {
  content: array<contentItem>,
  isError?: bool,
}

let makeTextContent = (text: string): contentItem => {
  type_: "text",
  text,
}

let makeToolResult = (text: string, ~isError=false): toolResult => {
  content: [makeTextContent(text)],
  isError: ?isError ? Some(true) : None,
}

let makeJsonResult = (data: JSON.t): toolResult => {
  content: [makeTextContent(JSON.stringify(data, ~space=2))],
}

// Proof reference for verification transparency
type proofReference = {
  theorem: string,
  coqLocation: string,
  lean4Location: string,
  agdaLocation: string,
  isabelleLocation: string,
  description: string,
}

let mkdirRmdirProof: proofReference = {
  theorem: "mkdir_rmdir_reversible",
  coqLocation: "proofs/coq/filesystem_model.v:L45-L62",
  lean4Location: "proofs/lean4/FilesystemModel.lean:L38-L52",
  agdaLocation: "proofs/agda/FilesystemModel.agda:L41-L58",
  isabelleLocation: "proofs/isabelle/FilesystemModel.thy:L35-L50",
  description: "rmdir(mkdir(path, fs)) = fs when preconditions hold",
}

let createDeleteProof: proofReference = {
  theorem: "create_delete_file_reversible",
  coqLocation: "proofs/coq/file_operations.v:L32-L48",
  lean4Location: "proofs/lean4/FileOperations.lean:L28-L42",
  agdaLocation: "proofs/agda/FileOperations.agda:L30-L45",
  isabelleLocation: "proofs/isabelle/FileOperations.thy:L25-L40",
  description: "delete_file(create_file(path, fs)) = fs when preconditions hold",
}

let compositionProof: proofReference = {
  theorem: "operation_sequence_reversible",
  coqLocation: "proofs/coq/filesystem_composition.v:L28-L52",
  lean4Location: "proofs/lean4/FilesystemComposition.lean:L24-L45",
  agdaLocation: "proofs/agda/FilesystemComposition.agda:L26-L48",
  isabelleLocation: "proofs/isabelle/FilesystemComposition.thy:L22-L42",
  description: "apply_sequence(reverse(ops), apply_sequence(ops, fs)) = fs",
}

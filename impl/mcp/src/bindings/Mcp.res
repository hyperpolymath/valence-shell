// SPDX-License-Identifier: AGPL-3.0-or-later
// MCP SDK bindings for ReScript - Valence Shell

type toolHandler = JSON.t => promise<JSON.t>

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

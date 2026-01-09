// SPDX-License-Identifier: AGPL-3.0-or-later
// Valence Shell MCP Server - Entry Point
//
// Usage:
//   Local:  deno task start
//   HTTP:   deno task serve
//   Deploy: deno deploy (auto-detects HTTP mode)

open Mcp
open Deno
open Server
open State

// ============================================================================
// Server Mode Detection
// ============================================================================

type serverMode = Stdio | Http

let isServerlessEnvironment = (): bool => {
  Env.get("DENO_DEPLOYMENT_ID")->Option.isSome ||
    Env.get("MCP_HTTP_MODE") == Some("true") ||
    Array.includes(Args.get(), "--http")
}

let detectMode = (): serverMode => {
  if isServerlessEnvironment() {
    Http
  } else {
    Stdio
  }
}

// ============================================================================
// STDIO Mode (for local MCP clients like Claude Desktop)
// ============================================================================

let startStdioMode = async (server: mcpServer): promise<unit> => {
  Console.error("valence-shell-mcp v0.1.0 (STDIO mode)")
  Console.error("Formally verified reversible shell operations")
  Console.error("Feedback: https://github.com/hyperpolymath/valence-shell/issues")

  let transport = createStdioTransport()
  await connect(server, transport)
}

// ============================================================================
// HTTP Mode (for serverless/cloud deployment)
// ============================================================================

let startHttpMode = async (): promise<unit> => {
  let port = switch Env.get("PORT") {
  | Some(p) =>
    switch Int.fromString(p) {
    | Some(n) => n
    | None => 8000
    }
  | None => 8000
  }

  let host = switch Env.get("HOST") {
  | Some(h) => h
  | None => "0.0.0.0"
  }

  Console.error("valence-shell-mcp v0.1.0 (HTTP mode)")
  Console.error("Listening on http://" ++ host ++ ":" ++ Int.toString(port))

  let handler = async (request: Http.request): promise<Http.response> => {
    let url = Http.makeUrl(request.url)

    if url.pathname == "/health" {
      let health = Dict.make()
      Dict.set(health, "status", JSON.Encode.string("ok"))
      Dict.set(health, "version", JSON.Encode.string("0.1.0"))
      Dict.set(health, "proofSystems", JSON.Encode.int(6))
      Dict.set(health, "totalTheorems", JSON.Encode.int(256))
      Http.jsonResponse(JSON.Encode.object(health), {status: 200})
    } else if url.pathname == "/" || url.pathname == "/info" {
      let tools = [
        "vsh_mkdir", "vsh_rmdir", "vsh_touch", "vsh_rm",
        "vsh_undo", "vsh_history", "vsh_status", "vsh_proofs",
        "vsh_begin", "vsh_commit", "vsh_rollback",
      ]

      let info = Dict.make()
      Dict.set(info, "name", JSON.Encode.string("valence-shell-mcp"))
      Dict.set(info, "version", JSON.Encode.string("0.1.0"))
      Dict.set(info, "description", JSON.Encode.string("Formally verified reversible shell operations via MCP"))
      Dict.set(info, "protocol", JSON.Encode.string("MCP"))
      Dict.set(info, "endpoint", JSON.Encode.string("/mcp"))
      Dict.set(info, "tools", JSON.Encode.array(Array.map(tools, JSON.Encode.string)))
      Dict.set(info, "proofSystems", JSON.Encode.array([
        JSON.Encode.string("Coq"),
        JSON.Encode.string("Lean 4"),
        JSON.Encode.string("Agda"),
        JSON.Encode.string("Isabelle/HOL"),
        JSON.Encode.string("Mizar"),
        JSON.Encode.string("Z3"),
      ]))
      Dict.set(info, "documentation", JSON.Encode.string("https://github.com/hyperpolymath/valence-shell"))
      Http.jsonResponse(JSON.Encode.object(info), {status: 200})
    } else if url.pathname == "/mcp" {
      // MCP endpoint - POST required
      if request.method != "POST" {
        let error = Dict.make()
        Dict.set(error, "error", JSON.Encode.string("Use POST for MCP requests"))
        Http.jsonResponse(JSON.Encode.object(error), {status: 405})
      } else {
        // Handle JSON-RPC request
        let body = await Http.text(request)
        let response = await handleHttpRequest(body)
        Http.jsonResponse(response, {status: 200})
      }
    } else {
      Http.textResponse("Not Found", {status: 404})
    }
  }

  Http.serve({port, hostname: host}, handler)
}

// ============================================================================
// Initialization
// ============================================================================

let initSandbox = async (): promise<unit> => {
  // Create sandbox directory if needed
  let sandboxRoot = switch Env.get("VSH_SANDBOX") {
  | Some(root) => root
  | None => "/tmp/vsh-sandbox"
  }

  setRoot(sandboxRoot)

  try {
    await Fs.mkdir(sandboxRoot, {"recursive": true})
    Console.error("Sandbox root: " ++ sandboxRoot)
  } catch {
  | _ => Console.error("Using existing sandbox: " ++ sandboxRoot)
  }
}

// ============================================================================
// Entry Point
// ============================================================================

let main = async (): promise<unit> => {
  await initSandbox()

  let mode = detectMode()

  switch mode {
  | Stdio =>
    let server = createServer()
    await startStdioMode(server)
  | Http =>
    await startHttpMode()
  }
}

let _ = main()

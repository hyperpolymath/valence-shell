// SPDX-License-Identifier: PLMP-1.0-or-later
//! Daemon Client - JSON-RPC over Unix Socket
//!
//! Communicates with BEAM daemon for:
//! - Reversible operations (RMR)
//! - Secure deletion (RMO)
//! - Transaction management
//! - Audit trail

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::UnixStream;

const SOCKET_PATH: &str = "/tmp/vsh-daemon.sock";

/// JSON-RPC request
#[derive(Serialize)]
struct JsonRpcRequest {
    jsonrpc: String,
    method: String,
    params: serde_json::Value,
    id: u64,
}

/// JSON-RPC response
#[derive(Deserialize, Debug)]
struct JsonRpcResponse {
    jsonrpc: String,
    id: u64,
    #[serde(default)]
    result: Option<serde_json::Value>,
    #[serde(default)]
    error: Option<JsonRpcError>,
}

#[derive(Deserialize, Debug)]
struct JsonRpcError {
    code: i32,
    message: String,
}

/// Operation result from daemon
#[derive(Deserialize, Debug)]
pub struct OperationResult {
    pub success: bool,
    pub operation: String,
    #[serde(default)]
    pub path: String,
    #[serde(rename = "operationId")]
    pub operation_id: String,
    #[serde(rename = "undoCommand")]
    pub undo_command: Option<String>,
    #[serde(rename = "canUndo")]
    pub can_undo: Option<bool>,
    #[serde(default)]
    pub proof: Option<ProofReference>,
}

#[derive(Deserialize, Debug)]
pub struct ProofReference {
    pub theorem: String,
    #[serde(default)]
    pub location: String,
}

/// Daemon client
pub struct DaemonClient {
    stream: UnixStream,
    next_id: u64,
}

impl DaemonClient {
    /// Connect to daemon
    pub fn connect() -> Result<Self> {
        let stream = UnixStream::connect(SOCKET_PATH)
            .context("Failed to connect to daemon - is it running?")?;

        Ok(Self { stream, next_id: 1 })
    }

    /// Check if daemon is running
    pub fn is_daemon_running() -> bool {
        UnixStream::connect(SOCKET_PATH).is_ok()
    }

    /// Send request and get response
    fn call(&mut self, method: &str, params: serde_json::Value) -> Result<serde_json::Value> {
        let request = JsonRpcRequest {
            jsonrpc: "2.0".to_string(),
            method: method.to_string(),
            params,
            id: self.next_id,
        };
        self.next_id += 1;

        // Send request
        let request_json = serde_json::to_string(&request)?;
        writeln!(self.stream, "{}", request_json)?;

        // Read response
        let mut reader = BufReader::new(&self.stream);
        let mut response_line = String::new();
        reader.read_line(&mut response_line)?;

        let response: JsonRpcResponse = serde_json::from_str(&response_line)?;

        if let Some(error) = response.error {
            anyhow::bail!("Daemon error: {} (code: {})", error.message, error.code);
        }

        response
            .result
            .ok_or_else(|| anyhow::anyhow!("No result in response"))
    }

    // Filesystem Operations

    pub fn mkdir(&mut self, path: &str) -> Result<OperationResult> {
        let params = serde_json::json!({ "path": path });
        let result = self.call("mkdir", params)?;
        Ok(serde_json::from_value(result)?)
    }

    pub fn rmdir(&mut self, path: &str) -> Result<OperationResult> {
        let params = serde_json::json!({ "path": path });
        let result = self.call("rmdir", params)?;
        Ok(serde_json::from_value(result)?)
    }

    pub fn touch(&mut self, path: &str) -> Result<OperationResult> {
        let params = serde_json::json!({ "path": path });
        let result = self.call("touch", params)?;
        Ok(serde_json::from_value(result)?)
    }

    pub fn rm(&mut self, path: &str) -> Result<OperationResult> {
        let params = serde_json::json!({ "path": path });
        let result = self.call("rm", params)?;
        Ok(serde_json::from_value(result)?)
    }

    pub fn copy(&mut self, src: &str, dst: &str) -> Result<OperationResult> {
        let params = serde_json::json!({ "src": src, "dst": dst });
        let result = self.call("copy", params)?;
        Ok(serde_json::from_value(result)?)
    }

    pub fn move_file(&mut self, src: &str, dst: &str) -> Result<OperationResult> {
        let params = serde_json::json!({ "src": src, "dst": dst });
        let result = self.call("move", params)?;
        Ok(serde_json::from_value(result)?)
    }

    // Reversibility Operations

    pub fn undo(&mut self, count: Option<u32>) -> Result<serde_json::Value> {
        let params = if let Some(c) = count {
            serde_json::json!({ "count": c })
        } else {
            serde_json::json!({})
        };
        self.call("undo", params)
    }

    pub fn redo(&mut self, count: Option<u32>) -> Result<serde_json::Value> {
        let params = if let Some(c) = count {
            serde_json::json!({ "count": c })
        } else {
            serde_json::json!({})
        };
        self.call("redo", params)
    }

    pub fn history(&mut self, count: Option<u32>) -> Result<serde_json::Value> {
        let params = if let Some(c) = count {
            serde_json::json!({ "count": c })
        } else {
            serde_json::json!({})
        };
        self.call("history", params)
    }

    pub fn status(&mut self) -> Result<serde_json::Value> {
        self.call("status", serde_json::json!({}))
    }

    // Transaction Operations

    pub fn begin_transaction(&mut self, name: &str) -> Result<serde_json::Value> {
        let params = serde_json::json!({ "name": name });
        self.call("begin", params)
    }

    pub fn commit_transaction(&mut self) -> Result<serde_json::Value> {
        self.call("commit", serde_json::json!({}))
    }

    pub fn rollback_transaction(&mut self) -> Result<serde_json::Value> {
        self.call("rollback", serde_json::json!({}))
    }

    // Verification

    pub fn get_proofs(&mut self) -> Result<serde_json::Value> {
        self.call("proofs", serde_json::json!({}))
    }
}

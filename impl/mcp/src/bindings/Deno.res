// SPDX-License-Identifier: AGPL-3.0-or-later
// Deno runtime bindings for ReScript

module Env = {
  @val @scope(("Deno", "env"))
  external get: string => option<string> = "get"

  @val @scope(("Deno", "env"))
  external set: (string, string) => unit = "set"
}

module Args = {
  @val @scope("Deno")
  external get: unit => array<string> = "args"
}

module Fs = {
  type fileInfo = {
    isFile: bool,
    isDirectory: bool,
    isSymlink: bool,
    size: float,
  }

  @val @scope("Deno")
  external readTextFile: string => promise<string> = "readTextFile"

  @val @scope("Deno")
  external writeTextFile: (string, string) => promise<unit> = "writeTextFile"

  @val @scope("Deno")
  external mkdir: (string, {"recursive": bool}) => promise<unit> = "mkdir"

  @val @scope("Deno")
  external remove: (string, {"recursive": bool}) => promise<unit> = "remove"

  @val @scope("Deno")
  external stat: string => promise<fileInfo> = "stat"

  @val @scope("Deno")
  external lstat: string => promise<fileInfo> = "lstat"

  type dirEntry = {
    name: string,
    isFile: bool,
    isDirectory: bool,
    isSymlink: bool,
  }

  @val @scope("Deno")
  external readDir: string => Js.Array2.array_like<dirEntry> = "readDirSync"
}

module Command = {
  type commandOutput = {
    code: int,
    stdout: Uint8Array.t,
    stderr: Uint8Array.t,
  }

  type commandOptions = {
    args?: array<string>,
    cwd?: string,
    env?: dict<string>,
    stdin?: string,
    stdout?: string,
    stderr?: string,
  }

  @new @scope("Deno")
  external make: (string, commandOptions) => 'command = "Command"

  @send
  external output: 'command => promise<commandOutput> = "output"

  @send
  external spawn: 'command => 'child = "spawn"
}

// Text encoding/decoding
module TextEncoder = {
  type t

  @new
  external make: unit => t = "TextEncoder"

  @send
  external encode: (t, string) => Uint8Array.t = "encode"
}

module TextDecoder = {
  type t

  @new
  external make: unit => t = "TextDecoder"

  @send
  external decode: (t, Uint8Array.t) => string = "decode"
}

// Console binding
module Console = {
  @val @scope("console")
  external log: 'a => unit = "log"

  @val @scope("console")
  external error: 'a => unit = "error"

  @val @scope("console")
  external warn: 'a => unit = "warn"
}

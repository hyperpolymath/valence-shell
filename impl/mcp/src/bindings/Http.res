// SPDX-License-Identifier: PLMP-1.0-or-later
// HTTP bindings for Deno

type request = {
  method: string,
  url: string,
  headers: Js.Dict.t<string>,
}

type responseInit = {
  status?: int,
  headers?: Js.Dict.t<string>,
}

type response

@new
external makeResponse: (Nullable.t<string>, responseInit) => response = "Response"

type urlRecord = {
  pathname: string,
  searchParams: Js.Dict.t<string>,
  href: string,
  origin: string,
  host: string,
}

@new
external makeUrl: string => urlRecord = "URL"

type serveOptions = {
  port: int,
  hostname: string,
}

type serveHandler = request => promise<response>

@val @scope("Deno")
external serve: (serveOptions, serveHandler) => unit = "serve"

let jsonResponse = (data: JSON.t, init: responseInit): response => {
  let headers = Js.Dict.empty()
  Js.Dict.set(headers, "Content-Type", "application/json")
  let init' = {
    status: ?init.status,
    headers: Some(headers),
  }
  makeResponse(Nullable.make(JSON.stringify(data)), init')
}

let textResponse = (text: string, init: responseInit): response => {
  let headers = Js.Dict.empty()
  Js.Dict.set(headers, "Content-Type", "text/plain")
  let init' = {
    status: ?init.status,
    headers: Some(headers),
  }
  makeResponse(Nullable.make(text), init')
}

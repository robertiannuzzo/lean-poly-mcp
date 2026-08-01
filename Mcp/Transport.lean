import Lean.Data.JsonRpc
import Mcp.Interface

/-!
# Transport

JSON-RPC 2.0 over stdio, newline-delimited — the framing MCP's stdio transport uses,
and the one `v1-idris/gui/server_gui.py` already speaks.

Note this is *not* LSP framing: `Lean.Data.Lsp.Communication` prefixes messages with
`Content-Length` headers, which MCP does not. So the message *type* and its JSON
instances come from `Lean.JsonRpc`, but the framing is ours.

The only interesting line in this file is `respond`, which answers requests by
projecting `Mcp.server` — the lens — through `sectionEquiv`. The running server and
the categorical object are one term.
-/

namespace Mcp

open Lean Lean.JsonRpc
open Poly

def logErr (s : String) : IO Unit := do
  let err ← IO.getStderr
  err.putStrLn s
  err.flush

def writeMessage (out : IO.FS.Stream) (m : Message) : IO Unit := do
  out.putStr ((toJson m).compress ++ "\n")
  out.flush

/-- Answer a decoded request. The dispatch is `(sectionEquiv MCP).toFun server`, which
`dispatch_eq_handle` proves is `handle` — written this way deliberately, so the live
path goes through the lens rather than around it. -/
def respond (id : RequestID) (m : Method) : Message :=
  .response id (encodeResult m ((sectionEquiv MCP).toFun server m))

def handleMessage (out : IO.FS.Stream) : Message → IO Unit
  | .request id method params? => do
    match decodeRequest method (params?.map toJson) with
    | .unknownMethod =>
      writeMessage out (.responseError id .methodNotFound s!"unknown method: {method}" none)
    | .badParams =>
      writeMessage out (.responseError id .invalidParams
        s!"{method}: missing or malformed params" none)
    | .ok m => writeMessage out (respond id m)
  | .notification method _ => logErr s!"notification: {method}"
  | .response _ _ => logErr "unexpected response received by server"
  | .responseError _ _ msg _ => logErr s!"unexpected error response received by server: {msg}"

def handleLine (out : IO.FS.Stream) (line : String) : IO Unit := do
  match Json.parse line with
  | .error e => logErr s!"could not parse line as JSON: {e}"
  | .ok j =>
    match fromJson? (α := Message) j with
    | .error e => logErr s!"could not parse message: {e}"
    | .ok msg => handleMessage out msg

/-- Read newline-delimited messages until stdin closes. -/
partial def loop (inp out : IO.FS.Stream) : IO Unit := do
  let line ← inp.getLine
  -- `getLine` returns "" only at EOF; a blank line comes back as "\n".
  if line.isEmpty then
    return
  if line.all Char.isWhitespace then
    loop inp out
  else
    handleLine out line
    loop inp out

end Mcp

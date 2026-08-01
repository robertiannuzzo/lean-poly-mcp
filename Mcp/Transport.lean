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

-- Both `Lean` and `Lean.JsonRpc` export a `Message`, so `JsonRpc.Message` stays
-- qualified below rather than opening the namespace wholesale.
open Lean
open Poly

def logErr (s : String) : IO Unit := do
  let err ← IO.getStderr
  err.putStrLn s
  err.flush

def writeMessage (out : IO.FS.Stream) (m : JsonRpc.Message) : IO Unit := do
  out.putStr ((toJson m).compress ++ "\n")
  out.flush

/-- Answer a decoded request by running the server — `Mcp.handle`, the effectful
section of the coproduct. On the pure summand this is still literally the Phase 2
lens: `handle_inl` proves `handle env (.inl m) = pure (pureHandle m)` by `rfl`, and
`pureHandle` is what `pureServer` projects to. The live path still goes through the
categorical object rather than around it; it is now a Kleisli section rather than a
`Lens MCP y`, for the reason spelled out in `Poly/Kleisli.lean`. -/
def respond (env : Lean.Environment) (id : JsonRpc.RequestID) (m : Method) : IO JsonRpc.Message := do
  let result ← handle env m
  return .response id (encodeResult m result)

def handleMessage (env : Lean.Environment) (out : IO.FS.Stream) : JsonRpc.Message → IO Unit
  | .request id method params? => do
    match decodeRequest method (params?.map toJson) with
    | .unknownMethod =>
      writeMessage out (.responseError id .methodNotFound s!"unknown method: {method}" none)
    | .badParams =>
      writeMessage out (.responseError id .invalidParams
        s!"{method}: missing or malformed params" none)
    | .ok m => writeMessage out (← respond env id m)
  | .notification method _ => logErr s!"notification: {method}"
  | .response _ _ => logErr "unexpected response received by server"
  | .responseError _ _ msg _ => logErr s!"unexpected error response received by server: {msg}"

def handleLine (env : Lean.Environment) (out : IO.FS.Stream) (line : String) : IO Unit := do
  match Json.parse line with
  | .error e => logErr s!"could not parse line as JSON: {e}"
  | .ok j =>
    match fromJson? (α := JsonRpc.Message) j with
    | .error e => logErr s!"could not parse message: {e}"
    | .ok msg => handleMessage env out msg

/-- Read newline-delimited messages until stdin closes. -/
partial def loop (env : Lean.Environment) (inp out : IO.FS.Stream) : IO Unit := do
  let line ← inp.getLine
  -- `getLine` returns "" only at EOF; a blank line comes back as "\n".
  if line.isEmpty then
    return
  if line.all Char.isWhitespace then
    loop env inp out
  else
    handleLine env out line
    loop env inp out

end Mcp

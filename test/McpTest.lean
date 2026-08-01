import Mcp.Transport

/-!
# MCP interface tests

Checks that decoding, dispatch and encoding line up, and records what the compiler
says when a handler returns the wrong shape for its request.
-/

open Lean (Json toJson)
open Poly
open Mcp

/-! ## The server is the lens

`dispatch_eq_handle` is proved by `rfl` in `Mcp/Interface.lean`; this restates it as a
test so a future refactor that decouples them fails here.
-/

example : (sectionEquiv PureMCP).toFun pureServer = pureHandle := pureDispatch_eq_handle

#guard ((sectionEquiv PureMCP).toFun pureServer .listTools).length = 1

/-! ## Dispatch -/

#guard (pureHandle (.initialize "2025-06-18")).serverInfo.name = "lean-poly-mcp"
#guard (pureHandle (.initialize "1999-01-01")).protocolVersion = "1999-01-01"
#guard (pureHandle .listTools).map (·.name) = ["hello"]

#guard (pureHandle (.callTool "hello" none)
        = ⟨[.text "Hello, world! (from the Lean 4 MCP server)"], false⟩)

#guard (pureHandle (.callTool "hello" (some (Json.mkObj [("name", Json.str "Robert")])))
        = ⟨[.text "Hello, Robert! (from the Lean 4 MCP server)"], false⟩)

/-! An unknown *tool* is a successful call reporting an error, not a protocol error —
the request was well-formed. Contrast with an unknown *method* below. -/
#guard (pureHandle (.callTool "nope" none) = ⟨[.text "unknown tool: nope"], true⟩)

/-! ## Decoding

The three outcomes are distinguished because they map to different JSON-RPC codes:
a missing method is `-32601`, malformed params `-32602`.
-/

private def decodesOk (method : String) (params : Option Json) : Bool :=
  match decodeRequest method params with | .ok _ => true | _ => false

private def decodesBadParams (method : String) (params : Option Json) : Bool :=
  match decodeRequest method params with | .badParams => true | _ => false

private def decodesUnknown (method : String) (params : Option Json) : Bool :=
  match decodeRequest method params with | .unknownMethod => true | _ => false

/-! The oracle summand decodes too — `source` is the one required field. -/
#guard decodesOk "check" (some (Json.mkObj [("source", Json.str "theorem cand : True := trivial")]))
#guard decodesBadParams "check" (some (Json.mkObj []))

#guard decodesOk "tools/list" none
#guard decodesOk "initialize" none                      -- protocolVersion defaults
#guard decodesOk "tools/call" (some (Json.mkObj [("name", Json.str "hello")]))
#guard decodesBadParams "tools/call" none               -- no tool name
#guard decodesBadParams "tools/call" (some (Json.mkObj []))
#guard decodesUnknown "bogus/method" none
#guard decodesUnknown "tools/call/extra" none

/-! ## Encoding

`tools/list` is the one place the MCP envelope differs from the natural Lean type,
so it is the one worth pinning.
-/

#guard (encodeResult (.inl .listTools) (pureHandle .listTools)).compress.startsWith "{\"tools\":["

#guard ((encodeResult (.inl (.callTool "hello" none)) (pureHandle (.callTool "hello" none))).compress
        = "{\"content\":[{\"text\":\"Hello, world! (from the Lean 4 MCP server)\",\"type\":\"text\"}],\"isError\":false}")

/-! ## Negative test

A handler that swaps two branches — answering `tools/list` with a call result and
`tools/call` with the tool list — must not compile:

```lean
def badHandle : (m : PureMethod) → PureResultOf m
  | .initialize pv => ⟨pv, ⟨"lean-poly-mcp", "0.1.0"⟩⟩
  | .listTools => callHello none
  | .callTool _ _ => tools
```

Verified against v4.33.0-rc1. Both branches are rejected independently, and the
expected type is reported in terms of the direction family, which is exactly the
dependency doing the work:

```
error: Type mismatch
  callHello none
has type
  CallToolResult
but is expected to have type
  PureResultOf PureMethod.listTools

error: Type mismatch
  tools
has type
  List Tool
but is expected to have type
  PureResultOf (PureMethod.callTool name✝ args✝)
```
-/

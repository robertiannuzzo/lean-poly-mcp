import Lean.Data.Json

/-!
# Wire types

The result records and their JSON encodings. `Mcp/Interface.lean` is the typed layer
above: it decides *which* of these a given request produces, via the direction family
of the interface polynomial.

Ported from `v1-idris/src/MCP/Types.idr`, but the encoders are mostly `deriving
ToJson` here, since the MCP field names already match the Lean field names.
-/

namespace Mcp

open Lean (Json ToJson toJson)

/-- The MCP revision this server implements. -/
def protocolVersion : String := "2025-06-18"

structure Implementation where
  name : String
  version : String
  deriving Repr, DecidableEq, ToJson

/-- `capabilities` is not a field of the Lean record — it is fixed by what this server
actually implements, so it is supplied by the encoder rather than stored. -/
structure InitializeResult where
  protocolVersion : String
  serverInfo : Implementation
  deriving Repr, DecidableEq

instance : ToJson InitializeResult where
  toJson r := Json.mkObj
    [ ("protocolVersion", Json.str r.protocolVersion)
    , ("capabilities", Json.mkObj [("tools", Json.mkObj [])])
    , ("serverInfo", toJson r.serverInfo) ]

/-- A tool's advertised shape.

MCP turns out to name the two halves of a polynomial directly: `inputSchema` is the
**position** — what a request to this tool carries — and `outputSchema` is the
**direction**, the response that request admits. So `tools/list` advertises
`Σ_t inputSchema_t → outputSchema_t` without any extension to the protocol, and a client
can read the interface's structure off the wire.

`outputSchema` is optional in MCP, so it is omitted rather than emitted as `null` when
absent — a hand-written encoder, because `deriving ToJson` would emit the null. -/
structure Tool where
  name : String
  description : String
  inputSchema : Json
  outputSchema : Option Json := none

instance : ToJson Tool where
  toJson t :=
    let base : List (String × Json) :=
      [ ("name", Json.str t.name)
      , ("description", Json.str t.description)
      , ("inputSchema", t.inputSchema) ]
    Json.mkObj (match t.outputSchema with
      | none => base
      | some o => base ++ [("outputSchema", o)])

/-- Tool-call output. Only text content is needed so far. -/
inductive Content where
  | text (text : String)
  deriving Repr, DecidableEq

instance : ToJson Content where
  toJson
    | .text s => Json.mkObj [("type", Json.str "text"), ("text", Json.str s)]

structure CallToolResult where
  content : List Content
  isError : Bool
  deriving Repr, DecidableEq, ToJson

end Mcp

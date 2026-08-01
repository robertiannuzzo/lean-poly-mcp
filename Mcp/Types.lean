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

/-- A tool's advertised shape. `inputSchema` is an opaque JSON Schema object. -/
structure Tool where
  name : String
  description : String
  inputSchema : Json
  deriving ToJson

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

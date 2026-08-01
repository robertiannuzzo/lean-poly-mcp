import Poly.Basic
import Mcp.Types

/-!
# The MCP interface as a polynomial functor

`Method` is the position type, `ResultOf` the direction family, and the server is a
**section** — a `Lens MCP y`, by `Poly.sectionEquiv`.

The thing to notice, and the reason this file exists in this shape: `handle` below is
not a stylised model of the server that happens to sit alongside it. It *is* the
server. `Mcp/Transport.lean` answers live requests by projecting this very lens
through `sectionEquiv`, so there is no second, idealised copy to drift out of sync.
That was the structural flaw in v1, where
`v1-idris/vendor/container-compendium/mcp-demo/McpReal.idr` was the elegant artifact
and `v1-idris/src/Server.idr` was the one that ran.
-/

namespace Mcp

open Lean (Json ToJson toJson)
open Poly

/-- The requests this server accepts — the positions of the interface polynomial.
Each constructor carries exactly what a handler needs to determine the response. -/
inductive Method where
  | initialize (protocolVersion : String)
  | listTools
  | callTool (name : String) (args : Option Json)

/-- The response type, indexed by the request. This dependency is what makes an
ill-typed request/response pairing unrepresentable. -/
abbrev ResultOf : Method → Type
  | .initialize _ => InitializeResult
  | .listTools => List Tool
  | .callTool _ _ => CallToolResult

/-- The interface: positions are requests, directions are responses to *that*
request. -/
abbrev MCP : Poly := ⟨Method, ResultOf⟩

/-! ## The tools -/

def helloTool : Tool where
  name := "hello"
  description := "Say hello. Optional 'name' argument."
  inputSchema := Json.mkObj
    [ ("type", Json.str "object")
    , ("properties", Json.mkObj
        [ ("name", Json.mkObj
            [ ("type", Json.str "string")
            , ("description", Json.str "Name to greet") ]) ]) ]

/-- Every tool this server exposes. In `Poly` terms the registry is a coproduct; here
it is still a list, because with one tool the coproduct structure would be decoration
rather than load-bearing. It becomes real when the oracle tools land in Phase 3. -/
def tools : List Tool := [helloTool]

def callHello (args : Option Json) : CallToolResult :=
  let name := match args.bind (·.getObjValAs? String "name" |>.toOption) with
    | some n => n
    | none => "world"
  ⟨[.text s!"Hello, {name}! (from the Lean 4 MCP server)"], false⟩

/-! ## The server -/

/-- The handler: an exhaustive dependent function from a request to a value of *that
request's* response type. Missing a case, or returning the wrong shape for one, is a
compile error. See `test/McpTest.lean` for the verbatim rejection. -/
def handle : (m : Method) → ResultOf m
  | .initialize pv => ⟨pv, ⟨"lean-poly-mcp", "0.1.0"⟩⟩
  | .listTools => tools
  | .callTool "hello" args => callHello args
  | .callTool nm _ => ⟨[.text s!"unknown tool: {nm}"], true⟩

/-- **The server, as a lens.** This is the object the transport actually runs. -/
def server : Lens MCP y := (sectionEquiv MCP).invFun handle

/-- Projecting the lens back to a dispatch function is definitionally the handler —
`sectionEquiv`'s round-trip is `rfl`, so routing live traffic through the lens costs
nothing at runtime and keeps one source of truth. -/
theorem dispatch_eq_handle : (sectionEquiv MCP).toFun server = handle := rfl

/-!
### A note on what changes in Phase 3

`check` and `prove` must run the elaborator, so their handlers are `IO`. A dependent
function `(m : Method) → IO (ResultOf m)` is *not* a `Lens MCP y` — it is a section in
the Kleisli category of `IO`. The pure statement above will then hold only of the pure
fragment, via the embedding `Section p → (i : p.Pos) → IO (p.Dir i)` given by `pure ∘ ·`.
Flagging it here rather than discovering it later; v1 hit exactly this and noted it at
`v1-idris/src/MCP/Container.idr`.
-/

/-! ## Decoding -/

/-- What decoding can produce: a well-formed request, or one of two distinct ways of
failing to be one. Kept separate from `Method` so "no such method" and "method known,
params malformed" get different JSON-RPC error codes. -/
inductive Decoded where
  | ok (m : Method)
  | unknownMethod
  | badParams

def decodeRequest (method : String) (params : Option Json) : Decoded :=
  match method with
  | "initialize" =>
    let pv := params.bind (·.getObjValAs? String "protocolVersion" |>.toOption)
    .ok (.initialize (pv.getD protocolVersion))
  | "tools/list" => .ok .listTools
  | "tools/call" =>
    match params.bind (·.getObjValAs? String "name" |>.toOption) with
    | some nm => .ok (.callTool nm (params.bind (·.getObjVal? "arguments" |>.toOption)))
    | none => .badParams
  | _ => .unknownMethod

/-- Wire encoding, also exhaustive over `Method`. `tools/list` is the one case where
the MCP envelope differs from the natural Lean type, so the wrapping happens here
rather than distorting `ResultOf`. -/
def encodeResult : (m : Method) → ResultOf m → Json
  | .initialize _, r => toJson r
  | .listTools, r => Json.mkObj [("tools", toJson r)]
  | .callTool _ _, r => toJson r

end Mcp

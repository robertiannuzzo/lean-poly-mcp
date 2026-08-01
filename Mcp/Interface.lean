import Poly.Basic
import Poly.Kleisli
import Mcp.Types
import Oracle.Kernel

/-!
# The MCP interface as a polynomial functor

Positions are requests, directions are the responses to *that* request, and the server
is a section.

Phase 3 changes the shape of that claim, in a way worth being precise about. The
interface is now a **coproduct**

  `MCP = PureMCP ⊕' OracleMCP`

and the two summands are not the same kind of thing. `PureMCP` — initialize, tools/list,
tools/call — is served by a genuine `Lens PureMCP y`: a pure section, exactly as in
Phase 2, and `pureDispatch_eq_handle` still holds by `rfl`. `OracleMCP` cannot be:
verifying a proof runs the elaborator, so its handler is effectful, and the whole
server is a section only in the Kleisli category of `IO` (see `Poly/Kleisli.lean`).

So the coproduct is doing real work here rather than being a nice way to describe a
list. It is what lets the pure claim survive intact on the summand where it is true,
instead of being weakened everywhere to accommodate the summand where it is not.
-/

namespace Mcp

open Lean (Json ToJson toJson)
open Poly

/-! ## The pure fragment -/

/-- Requests answerable without touching the outside world. -/
inductive PureMethod where
  | initialize (protocolVersion : String)
  | listTools
  | callTool (name : String) (args : Option Json)

abbrev PureResultOf : PureMethod → Type
  | .initialize _ => InitializeResult
  | .listTools => List Tool
  | .callTool _ _ => CallToolResult

abbrev PureMCP : Poly := ⟨PureMethod, PureResultOf⟩

/-! ## The oracle fragment -/

/-- A verification request. Mirrors `Oracle.Request` minus the declaration name, which
this server fixes at `cand` so the wire format cannot smuggle in a different target. -/
structure CheckRequest where
  preamble : String := ""
  source : String
  statement : Option String := none

/-- Directions here are verdicts. Note every request has the *same* response type,
so this summand is a monomial — the dependency is trivial for `check` alone, and the
interesting dependency lives across the coproduct. -/
abbrev OracleMCP : Poly := ⟨CheckRequest, fun _ => Oracle.Outcome⟩

/-! ## The whole interface -/

/-- **The interface is a coproduct.** Adding a family of requests is `⊕'`, not an
edit to an inductive type. -/
abbrev MCP : Poly := PureMCP ⊕' OracleMCP

/-- A request: a position of `MCP`, which is by construction a sum. -/
abbrev Method := MCP.Pos

/-- The response type for a request — `MCP.Dir`, spelled out for readability. -/
abbrev ResultOf : Method → Type := MCP.Dir

example : ResultOf (.inl .listTools) = List Tool := rfl
example (r : CheckRequest) : ResultOf (.inr r) = Oracle.Outcome := rfl

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

def tools : List Tool := [helloTool]

def callHello (args : Option Json) : CallToolResult :=
  let name := match args.bind (·.getObjValAs? String "name" |>.toOption) with
    | some n => n
    | none => "world"
  ⟨[.text s!"Hello, {name}! (from the Lean 4 MCP server)"], false⟩

/-! ## The pure server — unchanged from Phase 2 -/

/-- Exhaustive dependent function from a request to a value of *that request's*
response type. See `test/McpTest.lean` for the verbatim rejection of a wrong shape. -/
def pureHandle : (m : PureMethod) → PureResultOf m
  | .initialize pv => ⟨pv, ⟨"lean-poly-mcp", "0.1.0"⟩⟩
  | .listTools => tools
  | .callTool "hello" args => callHello args
  | .callTool nm _ => ⟨[.text s!"unknown tool: {nm}"], true⟩

/-- **The pure server, as a lens.** Still exactly a section of its summand. -/
def pureServer : Lens PureMCP y := (sectionEquiv PureMCP).invFun pureHandle

/-- The Phase 2 statement, surviving intact on the summand where it is true. -/
theorem pureDispatch_eq_handle :
    (sectionEquiv PureMCP).toFun pureServer = pureHandle := rfl

/-! ## The whole server -/

/-- Verify one candidate. The declaration name is fixed at `cand` by this server, not
supplied by the caller. -/
def runCheck (env : Lean.Environment) (r : CheckRequest) : IO Oracle.Outcome :=
  Oracle.verify env
    { preamble := r.preamble, source := r.source, expected? := r.statement }

/-- **The server**, as an effectful section of the coproduct: the copairing of the pure
section (embedded by `Section.toIO`) with the oracle's effectful one. -/
def handle (env : Lean.Environment) : IOSection MCP
  | .inl m => Section.toIO ((sectionEquiv PureMCP).toFun pureServer) m
  | .inr r => runCheck env r

/-- On the pure summand the server is still literally the pure handler, with `pure`
wrapped around it — nothing has been weakened, only extended. -/
theorem handle_inl (env : Lean.Environment) (m : PureMethod) :
    handle env (.inl m) = pure (pureHandle m) := rfl

/-! ## Decoding -/

inductive Decoded where
  | ok (m : Method)
  | unknownMethod
  | badParams

def decodeRequest (method : String) (params : Option Json) : Decoded :=
  match method with
  | "initialize" =>
    let pv := params.bind (·.getObjValAs? String "protocolVersion" |>.toOption)
    .ok (.inl (.initialize (pv.getD protocolVersion)))
  | "tools/list" => .ok (.inl .listTools)
  | "tools/call" =>
    match params.bind (·.getObjValAs? String "name" |>.toOption) with
    | some nm => .ok (.inl (.callTool nm (params.bind (·.getObjVal? "arguments" |>.toOption))))
    | none => .badParams
  | "check" =>
    match params.bind (·.getObjValAs? String "source" |>.toOption) with
    | some src =>
      .ok (.inr
        { source := src
          preamble := (params.bind (·.getObjValAs? String "preamble" |>.toOption)).getD ""
          statement := params.bind (·.getObjValAs? String "statement" |>.toOption) })
    | none => .badParams
  | _ => .unknownMethod

/-! ## Encoding -/

/-- Verdicts carry evidence, never a bare boolean. In particular `checked` always
reports the axiom set it was accepted with, so a caller can audit the audit. -/
def outcomeToJson : Oracle.Outcome → Json
  | .checked axioms => Json.mkObj
      [ ("outcome", Json.str "checked")
      , ("axioms", toJson (axioms.map toString)) ]
  | .elabFailed d => Json.mkObj
      [ ("outcome", Json.str "elab_failed"), ("diagnostic", Json.str d) ]
  | .missingDecl n => Json.mkObj
      [ ("outcome", Json.str "missing_decl"), ("expected", Json.str (toString n)) ]
  | .unsoundAxioms axioms => Json.mkObj
      [ ("outcome", Json.str "unsound_axioms")
      , ("axioms", toJson (axioms.map toString)) ]
  | .statementMismatch d => Json.mkObj
      [ ("outcome", Json.str "statement_mismatch"), ("diagnostic", Json.str d) ]
  | .badStatement d => Json.mkObj
      [ ("outcome", Json.str "bad_statement"), ("diagnostic", Json.str d) ]

/-- Exhaustive over `Method`. The `check` case echoes the request back alongside the
verdict — it can, because the *position* carries the request and the encoder receives
both position and direction. -/
def encodeResult : (m : Method) → ResultOf m → Json
  | .inl (.initialize _), r => toJson r
  | .inl .listTools, r => Json.mkObj [("tools", toJson r)]
  | .inl (.callTool _ _), r => toJson r
  | .inr req, o =>
    match outcomeToJson o with
    | .obj fields => .obj (fields.insert "source" (Json.str req.source))
    | j => j

end Mcp

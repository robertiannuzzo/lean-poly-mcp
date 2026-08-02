import Poly.Basic
import Poly.Kleisli
import Mcp.Types
import Oracle.Kernel

/-!
# The MCP interface as a polynomial functor

Positions are requests, directions are the responses to *that* request.

The interface is a coproduct of two very different summands:

  `MCP = PureMCP ⊕' ToolMCP`

`PureMCP` (initialize, tools/list) is served by a genuine `Lens PureMCP y` — a pure
section, and `pureDispatch_eq_handle` still holds by `rfl`. `ToolMCP` cannot be:
verifying a proof runs the elaborator, so its handler is effectful and the whole server
is a section only in the Kleisli category of `IO` (see `Poly/Kleisli.lean`). The
coproduct is what lets the pure claim survive intact on the summand where it is true
instead of being weakened everywhere.

`ToolMCP` is itself an **indexed** coproduct, `Poly.sigma toolPoly` — one summand per
tool. Adding a tool is one constructor of `ToolId` and one case of `toolPoly`; nothing
else in this file changes shape. That is the registry-as-coproduct claim discharged in
code rather than asserted in prose.

## Why tools and not custom methods

v1 exposed `check` as a top-level JSON-RPC method. That works with a hand-written client
and with nothing else: a standards-compliant MCP client discovers `tools/list` and calls
`tools/call`, and never learns a custom method exists. Routing the oracle through the
tool registry makes the server usable by *any* MCP client, and costs nothing — the
dependent structure is preserved internally and flattened only at the wire boundary, in
`encodeResult`.
-/

namespace Mcp

open Lean (Json ToJson toJson)
open Poly

/-! ## The pure fragment -/

/-- Requests answerable without touching the outside world. Note `tools/call` is *not*
here — it dispatches into the registry below. -/
inductive PureMethod where
  | initialize (protocolVersion : String)
  | listTools

abbrev PureResultOf : PureMethod → Type
  | .initialize _ => InitializeResult
  | .listTools => List Tool

abbrev PureMCP : Poly := ⟨PureMethod, PureResultOf⟩

/-! ## The tool registry -/

/-- A verification request. `declName` is fixed at `cand` by this server rather than
supplied by the caller, so the wire format cannot redirect the audit at a different
declaration. -/
structure CheckRequest where
  preamble : String := ""
  source : String
  statement : Option String := none
  deriving Repr

inductive ToolId where
  | hello
  | check
  deriving DecidableEq, Repr

/-- **Each tool is itself a polynomial**: its arguments are the positions, its natural
result type is the direction.

Note the direction of `check` is `Oracle.Outcome`, not a stringly-typed
`CallToolResult` — the typed layer is preserved all the way to the handler, and the MCP
envelope is applied once, at the edge, in `encodeResult`. Losing that distinction is how
a tool surface degenerates into passing JSON around. -/
@[reducible] def toolPoly : ToolId → Poly
  | .hello => ⟨Option String, fun _ => String⟩
  | .check => ⟨CheckRequest, fun _ => Oracle.Outcome⟩

/-- The registry: `Σ_{t : ToolId} toolPoly t`. -/
abbrev ToolMCP : Poly := Poly.sigma toolPoly

/-! ## The whole interface -/

abbrev MCP : Poly := PureMCP ⊕' ToolMCP

/-- A request: a position of `MCP`. -/
abbrev Method := MCP.Pos

/-- The response type for a request. -/
abbrev ResultOf : Method → Type := MCP.Dir

/-- The direction at a tool position is that tool's own result type — by `rfl`. This is
the registry claim in its most direct form. -/
example (r : CheckRequest) : ResultOf (.inr ⟨.check, r⟩) = Oracle.Outcome := rfl
example (n : Option String) : ResultOf (.inr ⟨.hello, n⟩) = String := rfl
example : ResultOf (.inl .listTools) = List Tool := rfl

/-! ## Tool metadata

Names, schemas and the lookup table all derive from one enumeration, so the advertised
registry and the dispatchable registry cannot drift apart. -/

def allTools : List ToolId := [.hello, .check]

def toolName : ToolId → String
  | .hello => "hello"
  | .check => "check"

def toolInfo : ToolId → Tool
  | .hello =>
    { name := toolName .hello
      description := "Say hello. Optional 'name' argument."
      inputSchema := Json.mkObj
        [ ("type", Json.str "object")
        , ("properties", Json.mkObj
            [ ("name", Json.mkObj
                [ ("type", Json.str "string")
                , ("description", Json.str "Name to greet") ]) ]) ] }
  | .check =>
    { name := toolName .check
      description :=
        "Verify a Lean declaration against the kernel: elaborate it, audit the axioms it \
         depends on, and (if 'statement' is given) check it proves that statement. \
         Returns structured evidence, never a bare boolean."
      inputSchema := Json.mkObj
        [ ("type", Json.str "object")
        , ("properties", Json.mkObj
            [ ("source", Json.mkObj
                [ ("type", Json.str "string")
                , ("description", Json.str "Lean source defining a declaration named 'cand'.") ])
            , ("statement", Json.mkObj
                [ ("type", Json.str "string")
                , ("description", Json.str "Optional. The statement 'cand' must prove.") ])
            , ("preamble", Json.mkObj
                [ ("type", Json.str "string")
                , ("description", Json.str "Optional. Lines prepended to both the candidate and the statement probes, typically `open` commands.") ]) ])
        , ("required", toJson [ "source" ]) ] }

def tools : List Tool := allTools.map toolInfo

def toolOfName (s : String) : Option ToolId :=
  allTools.find? (fun t => toolName t == s)

/-! ## The pure server -/

def pureHandle : (m : PureMethod) → PureResultOf m
  | .initialize pv => ⟨pv, ⟨"lean-poly-mcp", "0.1.0"⟩⟩
  | .listTools => tools

/-- **The pure server, as a lens.** Still exactly a section of its summand. -/
def pureServer : Lens PureMCP y := (sectionEquiv PureMCP).invFun pureHandle

/-- The Phase 2 statement, surviving intact on the summand where it is true. -/
theorem pureDispatch_eq_handle :
    (sectionEquiv PureMCP).toFun pureServer = pureHandle := rfl

/-! ## The whole server -/

/-- Dispatch a tool call. Exhaustive over the registry, and each branch must produce a
value of *that tool's* direction type. -/
def handleTool (env : Lean.Environment) : (i : ToolMCP.Pos) → IO (ToolMCP.Dir i)
  | ⟨.hello, name⟩ =>
    pure s!"Hello, {name.getD "world"}! (from the Lean 4 MCP server)"
  | ⟨.check, r⟩ =>
    Oracle.verify env
      { preamble := r.preamble, source := r.source, expected? := r.statement }

/-- **The server**, as an effectful section of the coproduct: the pure section embedded
by `Section.toIO`, copaired with the registry's effectful one. -/
def handle (env : Lean.Environment) : IOSection MCP
  | .inl m => Section.toIO ((sectionEquiv PureMCP).toFun pureServer) m
  | .inr t => handleTool env t

/-- On the pure summand the server is still literally the pure handler with `pure`
wrapped around it — nothing has been weakened, only extended. -/
theorem handle_inl (env : Lean.Environment) (m : PureMethod) :
    handle env (.inl m) = pure (pureHandle m) := rfl

/-! ## Decoding -/

/-- What decoding can produce. `unknownTool` is deliberately *not* a position of the
registry: the polynomial should contain exactly the tools that exist, and MCP says an
unknown tool name is a **successful** `tools/call` reporting `isError`, not a protocol
error. Keeping it here puts that case with the other transport-level outcomes instead of
polluting the registry with a summand that can only fail. -/
inductive Decoded where
  | ok (m : Method)
  | unknownMethod
  | badParams
  | unknownTool (name : String)

/-- Parse a tool's arguments into a position of *that tool's* polynomial — itself a
dependent function over the registry. -/
def parseArgs : (t : ToolId) → Option Json → Option (toolPoly t).Pos
  | .hello, args => some (args.bind (·.getObjValAs? String "name" |>.toOption))
  | .check, args => do
    let src ← args.bind (·.getObjValAs? String "source" |>.toOption)
    some { source := src
           preamble := (args.bind (·.getObjValAs? String "preamble" |>.toOption)).getD ""
           statement := args.bind (·.getObjValAs? String "statement" |>.toOption) }

def decodeRequest (method : String) (params : Option Json) : Decoded :=
  match method with
  | "initialize" =>
    let pv := params.bind (·.getObjValAs? String "protocolVersion" |>.toOption)
    .ok (.inl (.initialize (pv.getD protocolVersion)))
  | "tools/list" => .ok (.inl .listTools)
  | "tools/call" =>
    match params.bind (·.getObjValAs? String "name" |>.toOption) with
    | none => .badParams
    | some nm =>
      match toolOfName nm with
      | none => .unknownTool nm
      | some t =>
        match parseArgs t (params.bind (·.getObjVal? "arguments" |>.toOption)) with
        | none => .badParams
        | some pos => .ok (.inr ⟨t, pos⟩)
  | _ => .unknownMethod

/-! ## Encoding

The wire boundary, and the only place the dependent structure is flattened. -/

/-- Verdicts carry evidence, never a bare boolean — in particular `checked` always
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

/-- One-line human summary, so a client that only renders `content` still sees the
verdict rather than an opaque blob. -/
def outcomeSummary : Oracle.Outcome → String
  | .checked axioms =>
    if axioms.isEmpty then "checked — depends on no axioms"
    else s!"checked — axioms: {axioms.toList.map toString}"
  | .elabFailed _ => "elaboration failed"
  | .missingDecl n => s!"did not define `{n}`"
  | .unsoundAxioms axioms => s!"REJECTED — axioms outside the whitelist: {axioms.toList.map toString}"
  | .statementMismatch _ => "REJECTED — proves a different statement than the one requested"
  | .badStatement _ => "the requested statement is itself ill-formed here"

/-- MCP's `tools/call` envelope. `structuredContent` carries the machine-readable
verdict; `content` carries the same thing as text for clients that do not read it. -/
def callToolJson (text : String) (isError : Bool) (structured : Option Json) : Json :=
  let base : List (String × Json) :=
    [ ("content", Json.arr #[Json.mkObj [("type", Json.str "text"), ("text", Json.str text)]])
    , ("isError", Json.bool isError) ]
  Json.mkObj (match structured with
    | none => base
    | some s => base ++ [("structuredContent", s)])

/-- Exhaustive over `Method`.

Note `check` returning `unsound_axioms` sets `isError := false`: the tool *ran*, and
answered. MCP's `isError` means the invocation failed, not that the verdict was
unwelcome — conflating the two would tell an agent to retry the call rather than to
believe the rejection. -/
def encodeResult : (m : Method) → ResultOf m → Json
  | .inl (.initialize _), r => toJson r
  | .inl .listTools, r => Json.mkObj [("tools", toJson r)]
  | .inr ⟨.hello, _⟩, greeting => callToolJson greeting false none
  | .inr ⟨.check, _⟩, outcome =>
    callToolJson (outcomeSummary outcome) false (some (outcomeToJson outcome))

/-- The response for a tool name that is not in the registry: a successful call
reporting an error, per MCP. -/
def unknownToolJson (name : String) : Json :=
  callToolJson s!"unknown tool: {name}" true none

end Mcp

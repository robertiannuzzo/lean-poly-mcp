import Mcp.Transport

/-!
# MCP interface tests

Covers the registry-as-coproduct structure, decoding, and the wire envelope, and records
what the compiler says when a tool handler returns the wrong shape.
-/

open Lean (Json toJson)
open Poly
open Mcp

/-! ## The registry is a coproduct

The direction at a tool position is that tool's own result type, definitionally. If a
refactor flattened the registry into "every tool returns `CallToolResult`", these stop
being `rfl` and this file fails.
-/

example (r : CheckRequest) : ResultOf (.inr ⟨.check, r⟩) = Oracle.Outcome := rfl
example (n : Option String) : ResultOf (.inr ⟨.hello, n⟩) = String := rfl
example (r : SearchRequest) : ResultOf (.inr ⟨.search, r⟩) = Tactics.Outcome := rfl
example : ResultOf (.inl .listTools) = List Tool := rfl

/-! ## The pure server is still the lens -/

example : (sectionEquiv PureMCP).toFun pureServer = pureHandle := pureDispatch_eq_handle

#guard ((sectionEquiv PureMCP).toFun pureServer .listTools).length = 3

/-! ## Pure dispatch -/

#guard (pureHandle (.initialize "2025-06-18")).serverInfo.name = "lean-poly-mcp"
#guard (pureHandle (.initialize "1999-01-01")).protocolVersion = "1999-01-01"
#guard (pureHandle .listTools).map (·.name) = ["hello", "check", "search"]

/-! ## Metadata derives from one enumeration

Names, schemas and lookup all come from `allTools`, so the advertised registry and the
dispatchable registry cannot drift apart. -/

#guard allTools.map toolName = ["hello", "check", "search"]
#guard (tools.map (·.name)) = allTools.map toolName
#guard toolOfName "check" = some .check
#guard toolOfName "hello" = some .hello
#guard toolOfName "search" = some .search
#guard toolOfName "nope" = none

/-! ## Argument parsing is dependent

`parseArgs t` lands in `(toolPoly t).Pos` — a different type per tool. -/

private def helloArgs : Option Json := some (Json.mkObj [("name", Json.str "Robert")])
private def checkArgs : Option Json :=
  some (Json.mkObj [("source", Json.str "theorem cand : True := trivial")])

#guard parseArgs .hello helloArgs = some (some "Robert")
#guard parseArgs .hello none = some none          -- optional; defaults later
#guard (parseArgs .check checkArgs).isSome
#guard (parseArgs .check none).isNone             -- `source` is required
#guard (parseArgs .check (some (Json.mkObj []))).isNone

/-! ## Decoding

Four outcomes, because they map to four different wire behaviours: a missing method is
`-32601`, malformed params `-32602`, an unknown *tool* is a successful call reporting
`isError`, and a good request dispatches. -/

private def decodesOk (m : String) (p : Option Json) : Bool :=
  match decodeRequest m p with | .ok _ => true | _ => false
private def decodesBadParams (m : String) (p : Option Json) : Bool :=
  match decodeRequest m p with | .badParams => true | _ => false
private def decodesUnknownMethod (m : String) (p : Option Json) : Bool :=
  match decodeRequest m p with | .unknownMethod => true | _ => false
private def decodesUnknownTool (m : String) (p : Option Json) : Bool :=
  match decodeRequest m p with | .unknownTool _ => true | _ => false

private def callParams (name : String) (args : Option Json) : Option Json :=
  some (Json.mkObj (
    [("name", Json.str name)] ++ (match args with | none => [] | some a => [("arguments", a)])))

#guard decodesOk "tools/list" none
#guard decodesOk "initialize" none                                  -- protocolVersion defaults
#guard decodesOk "tools/call" (callParams "hello" none)
#guard decodesOk "tools/call" (callParams "check" checkArgs)

#guard decodesBadParams "tools/call" none                           -- no tool name
#guard decodesBadParams "tools/call" (callParams "check" none)      -- `check` needs source

#guard decodesUnknownTool "tools/call" (callParams "nope" none)
#guard decodesUnknownMethod "bogus/method" none

/-! An unknown *tool* must not be a protocol error, and an unknown *method* must not be a
tool result. Getting these backwards is a spec violation in both directions. -/
#guard !decodesUnknownMethod "tools/call" (callParams "nope" none)
#guard !decodesUnknownTool "bogus/method" none

/-! ## v1's custom method is gone

`check` is a tool now, not a top-level method — that is the whole point of this phase.
A client that still calls it as a method gets `-32601`, which is the correct answer. -/
#guard decodesUnknownMethod "check" checkArgs

/-! ## Encoding -/

#guard (encodeResult (.inl .listTools) (pureHandle .listTools)).compress.startsWith "{\"tools\":["

#guard ((encodeResult (.inr ⟨.hello, some "Robert"⟩) "Hello, Robert!").compress
        = "{\"content\":[{\"text\":\"Hello, Robert!\",\"type\":\"text\"}],\"isError\":false}")

/-! A verdict the caller will not like is still a *successful* call — `isError` means the
invocation failed, not that the answer was unwelcome. Conflating them tells an agent to
retry rather than to believe the rejection. -/
private def rejected : Json :=
  encodeResult (.inr ⟨.check, { source := "" }⟩) (.unsoundAxioms #[`sorryAx])

#guard (rejected.getObjValAs? Bool "isError").toOption = some false
#guard ((rejected.getObjVal? "structuredContent").toOption.bind
          (·.getObjValAs? String "outcome" |>.toOption)) = some "unsound_axioms"

/-! An unknown tool, by contrast, *is* an error result. -/
#guard ((unknownToolJson "nope").getObjValAs? Bool "isError").toOption = some true

/-! ## Negative test

A handler branch that returns the wrong tool's result type must not compile:

```lean
def badHandleTool (env : Lean.Environment) : (i : ToolMCP.Pos) → IO (ToolMCP.Dir i)
  | ⟨.hello, _⟩ => pure (Oracle.Outcome.checked #[])
  | ⟨.check, r⟩ => pure "not an outcome"
```

Verified against v4.28.0. The compiler reports the expected type in terms of the
registry's direction family — the dependency doing the work, made visible:

```
error: Application type mismatch: The argument
  Oracle.Outcome.checked #[]
has type
  Oracle.Outcome
but is expected to have type
  ToolMCP.Dir ⟨ToolId.hello, snd✝⟩

error: Application type mismatch: The argument
  "not an outcome"
has type
  String
but is expected to have type
  ToolMCP.Dir ⟨ToolId.check, snd✝⟩
```
-/

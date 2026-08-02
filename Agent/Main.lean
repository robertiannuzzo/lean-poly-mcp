import Agent.Runner

/-!
Run the agent on a goal and print the session as JSON — the front end's data source.

    agent-run <preamble> <goal> [imports...]

This is a separate executable rather than another MCP tool for a structural reason:
`Agent.prover` is defined *against* `Mcp.MCP`, so a tool that ran the agent would make
`Mcp.Interface` depend on `Agent`, which depends on `Mcp.Interface`. Rather than break
the cycle with an indirection that exists only to satisfy the compiler, the agent stays a
client of the interface — which is what it is.

The emitted trace is a path through the interaction tree: one entry per state visited,
each naming the request that state issued and the phase it moved to.
-/

open Lean Agent

/-- Which request a state issues, as a label the front end can render. -/
def requestLabel (s : State) : String :=
  match s.phase with
  | .search => "tools/call search"
  | .verify _ => "tools/call check"
  | _ => "tools/list (terminal — answer ignored)"

def phaseTag : Phase → String
  | .search => "search"
  | .verify _ => "verify"
  | .solved .. => "solved"
  | .rejected _ => "rejected"
  | .needsProver _ => "needsProver"

def stateToJson (s : State) : Json :=
  Json.mkObj
    [ ("phase", Json.str (phaseTag s.phase))
    , ("label", Json.str (renderPhase s.phase))
    , ("request", Json.str (requestLabel s))
    , ("terminal", Json.bool s.isTerminal) ]

def main (args : List String) : IO UInt32 := do
  match args with
  | preamble :: goal :: imports =>
    let mods := if imports.isEmpty then [`Mathlib] else imports.map (·.toName)
    let env ← Oracle.mkBaseEnv mods.toArray
    let trace ← Agent.run env 8 (start goal preamble)
    let out := Json.mkObj
      [ ("goal", Json.str goal)
      , ("preamble", Json.str preamble)
      , ("states", Json.arr ((trace.map stateToJson).toArray))
      , ("log", Json.arr (((trace.getLast!).log.map Json.str).toArray)) ]
    IO.println out.compress
    return 0
  | _ =>
    IO.eprintln "usage: agent-run <preamble> <goal> [imports...]"
    return 1

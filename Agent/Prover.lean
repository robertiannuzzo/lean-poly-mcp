import Mcp.Interface

/-!
# The agent, as a lens

An agent is a `Lens (S y^S) MCP`: `onPos` picks the next request from the current state,
`onDir` folds the response back in. It is an ordinary value of the kernel's lens type —
not a description of one — and `Agent/Runner.lean` executes exactly this value against
the server.

## The escalation ladder, as a state machine

```
search  ──solved──▶  solved
   │
   └──unsolved──▶  needsProver        (Phase 5 submits to Aristotle here)

verify  ──checked──▶  solved
   │
   └──rejected──▶  rejected
```

`verify` is the entry point for a candidate that came from *outside* — an Aristotle
result, or a human paste. It exists now, before Aristotle does, because the point of the
architecture is that a returned proof goes through the same oracle as everything else.

## Termination is a fixed point, not a state

A lens `S y^S → p` has no notion of stopping: `onPos` must produce a request for *every*
state, including finished ones. So the terminal states emit a harmless `tools/list` and
ignore the answer, making them fixed points of the transition.

That is a real property of the formalism rather than a workaround, and worth saying
plainly: a Moore machine runs forever, and "halting" is modelled by a state that no
longer changes. `Runner.run` reads that fixed point to decide when to stop pumping — the
stopping rule lives in the runner, not in the lens.
-/

namespace Agent

open Lean Poly Mcp

/-- Where the agent is in the ladder. -/
inductive Phase where
  /-- Try the free tiers. -/
  | search
  /-- Verify a candidate that came from outside. -/
  | verify (source : String)
  /-- Done: solved, with how and on what axioms. -/
  | solved (via : String) (axioms : Array Name)
  /-- Done: a supplied candidate did not survive the oracle. -/
  | rejected (reason : String)
  /-- Done for now: the free tiers are exhausted. Phase 5 escalates from here. -/
  | needsProver (tried : List String)
  deriving Repr, Inhabited

def Phase.isTerminal : Phase → Bool
  | .solved .. | .rejected _ | .needsProver _ => true
  | _ => false

/-- The agent's state. `log` accumulates a human-readable trace; the front end draws the
sequence of states, which is a path through the interaction tree. -/
structure State where
  goal : String
  preamble : String := ""
  phase : Phase := .search
  log : List String := []
  deriving Repr, Inhabited

def State.isTerminal (s : State) : Bool := s.phase.isTerminal

/-- Start from a goal and let the ladder run. -/
def start (goal : String) (preamble : String := "") : State :=
  { goal := goal, preamble := preamble }

/-- Start from a candidate someone else produced — the shape an Aristotle result arrives
in. -/
def startFromCandidate (goal source : String) (preamble : String := "") : State :=
  { goal := goal, preamble := preamble, phase := .verify source }

/-! ## The lens -/

/-- Which request this state issues. Total, as it must be — see the note on termination
above. -/
def onPos : State → MCP.Pos
  | { phase := .search, goal, preamble, .. } =>
    .inr ⟨.search, { preamble := preamble, goal := goal, maxTier := 1 }⟩
  | { phase := .verify src, goal, preamble, .. } =>
    .inr ⟨.check, { preamble := preamble, source := src, statement := some goal }⟩
  -- Terminal: ask something harmless and ignore the answer.
  | _ => .inl .listTools

/-- How a response updates the state. The type of the response is determined by
`onPos s`, so each branch here can only see the answer its own request admits — a wrong
pairing does not typecheck. -/
def onDir : (s : State) → MCP.Dir (onPos s) → State
  | s@{ phase := .search, .. }, outcome =>
    match outcome with
    | .solved tier tac axioms =>
      { s with phase := .solved s!"tier {tier} `{tac}`" axioms
               log := s.log ++ [s!"free ladder solved it at tier {tier} with `{tac}`"] }
    | .unsolved tried =>
      { s with phase := .needsProver tried
               log := s.log ++ [s!"free ladder exhausted after {tried.length} tactics"] }
  | s@{ phase := .verify _, .. }, outcome =>
    match outcome with
    | .checked axioms =>
      { s with phase := .solved "supplied candidate" axioms
               log := s.log ++ ["supplied candidate verified"] }
    | .unsoundAxioms axs =>
      { s with phase := .rejected s!"axioms outside the whitelist: {axs.toList.map toString}"
               log := s.log ++ ["supplied candidate REJECTED: unsound axioms"] }
    | .statementMismatch _ =>
      { s with phase := .rejected "proves a different statement than the goal"
               log := s.log ++ ["supplied candidate REJECTED: statement mismatch"] }
    | .elabFailed _ =>
      { s with phase := .rejected "does not elaborate"
               log := s.log ++ ["supplied candidate REJECTED: does not elaborate"] }
    | .missingDecl n =>
      { s with phase := .rejected s!"did not define `{n}`"
               log := s.log ++ ["supplied candidate REJECTED: wrong declaration"] }
    | .badStatement _ =>
      { s with phase := .rejected "the goal itself is ill-formed here"
               log := s.log ++ ["goal ill-formed — harness problem, not a proof problem"] }
  -- Terminal states are fixed points.
  | s, _ => s

/-- **The agent.** A value of the kernel's lens type — the same `Lens` the Phase 1
theorems are about. -/
def prover : Poly.Agent State MCP := ⟨onPos, onDir⟩

end Agent

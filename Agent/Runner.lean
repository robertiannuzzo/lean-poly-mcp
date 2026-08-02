import Agent.Prover
import Poly.Kleisli

/-!
# Running the agent

`Poly.stepIO` composes the agent with the server. This file only adds the stopping rule
and the fuel — the loop itself is lens composition, not hand-written control flow.

The distinction matters for the claim in `docs/lean-upgrade-plan.md` §1. The runtime
executes `Agent.prover`, the same value the Phase 1 theorems are about; it is not a
re-implementation of the agent that happens to agree with one. That was v1's structural
flaw, where the dependent-lens model and the program that ran were two different
artifacts.

What is *not* claimed: that this constitutes a mechanized bridge between the Lean
semantics and the compiled binary's IO behaviour. There is no such bridge. The value
executes; that is design discipline, not a theorem.
-/

namespace Agent

open Lean Poly

/-- Run until the agent reaches a fixed point, or until fuel runs out, returning every
state visited — a path through the interaction tree.

`fuel` is a hard cap on round-trips, not a heuristic: an agent that never reaches a
terminal phase must still stop. -/
def run (env : Environment) : Nat → State → IO (List State)
  | 0, s => pure [s]
  | n + 1, s =>
    if s.isTerminal then pure [s]
    else do
      let s' ← Poly.stepIO prover (Mcp.handle env) s
      return s :: (← run env n s')

/-- The final state of a run. -/
def runToEnd (env : Environment) (fuel : Nat) (s : State) : IO State := do
  let trace ← run env fuel s
  return trace.getLast!

/-- One line per state, for the trace view. -/
def renderPhase : Phase → String
  | .search => "search — trying the free ladder"
  | .verify _ => "verify — checking a supplied candidate"
  | .solved via axioms =>
    let ax := if axioms.isEmpty then "no axioms" else s!"{axioms.toList.map toString}"
    s!"SOLVED via {via} ({ax})"
  | .rejected why => s!"REJECTED — {why}"
  | .needsProver tried => s!"NEEDS PROVER — free ladder exhausted after {tried.length} tactics"

end Agent

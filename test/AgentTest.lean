import Agent.Runner
import Formalize.Benchmark

/-!
# Agent runs

Drives `Agent.prover` — the lens — against the live server, and prints each session as
the path through the interaction tree that it is.

The four cases cover both entry points and both ways each can end: the ladder solving a
goal, the ladder exhausting itself, an outside candidate surviving the oracle, and an
outside candidate being rejected by it.
-/

open Lean Agent

/-! ## The agent is the kernel's lens, not a lookalike

If someone later replaces `prover` with a hand-rolled loop, this stops typechecking. -/

example : Poly.Lens (Poly.monomial Agent.State) Mcp.MCP := Agent.prover

/-! And a run is lens composition: `stepIO` against a *pure* server reduces to
`Poly.step`, the Phase 1 statement, definitionally. -/

example {S : Type} {p : Poly} (a : Poly.Agent S p) (srv : Poly.Lens p Poly.y) (s : S) :
    Poly.stepIO a (Poly.Lens.toIOSection srv) s = pure (Poly.step a srv s) :=
  Poly.stepIO_pure a srv s

structure Case where
  name : String
  state : State

def cat : String := "open CategoryTheory"

def cases : List Case :=
  [ { name := "ladder solves it"
      state := start "∀ {C : Type} [Category C] {X Y : C} (f : X ⟶ Y), 𝟙 X ≫ f = f" cat }
  , { name := "ladder exhausts — this is where Phase 5 escalates"
      state := start "∀ {C : Type} [Category C] {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X), f ≫ g = 𝟙 X → g ≫ f = 𝟙 Y" cat }
  , { name := "supplied candidate survives the oracle"
      state := startFromCandidate
        "∀ {C : Type} [Category C] {X Y : C} (f : X ⟶ Y), 𝟙 X ≫ f = f"
        "theorem cand : ∀ {C : Type} [Category C] {X Y : C} (f : X ⟶ Y), 𝟙 X ≫ f = f := by simp" cat }
  , { name := "supplied candidate is rejected — sorry'd"
      state := startFromCandidate
        "∀ {C : Type} [Category C] {X Y : C} (f : X ⟶ Y), 𝟙 X ≫ f = f"
        "theorem cand : ∀ {C : Type} [Category C] {X Y : C} (f : X ⟶ Y), 𝟙 X ≫ f = f := by sorry" cat }
  ]

def main : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let env ← Oracle.mkBaseEnv #[`Mathlib]
  let t1 ← IO.monoMsNow
  IO.println s!"  [{t1 - t0} ms] import Mathlib (once)\n"

  let mut failed := 0
  for c in cases do
    let s0 ← IO.monoMsNow
    let trace ← Agent.run env 8 c.state
    let s1 ← IO.monoMsNow
    IO.println s!"  ── {c.name}  [{s1 - s0} ms, {trace.length} states]"
    for st in trace do
      IO.println s!"       {Agent.renderPhase st.phase}"
    for line in (trace.getLast!).log do
      IO.println s!"       · {line}"
    -- Every run must reach a fixed point within fuel; a non-terminating agent is a bug.
    if !(trace.getLast!).isTerminal then
      IO.println "       FAIL: ran out of fuel without reaching a terminal phase"
      failed := failed + 1
    IO.println ""

  if failed == 0 then
    IO.println s!"  {cases.length} agent runs reached a fixed point"
    return 0
  else
    IO.println s!"  {failed} of {cases.length} agent runs FAILED"
    return 1

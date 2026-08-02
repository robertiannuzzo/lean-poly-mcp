import Tactics.Search
import Formalize.Benchmark

/-!
# Benchmark: how far do the free tiers get?

Run with `./scripts/check.sh --full`.

This is a **measurement**, not a pass/fail suite, and it is deliberately not written to
be all-green: the statements the free ladder cannot reach are exactly the ones that
justify paying for tier 2, and knowing which they are is the point.

The one hard invariant is a floor on tier 0. Those are the category laws; if `aesop_cat`
and friends stop discharging them, something has broken in the environment rather than in
the corpus, and that should fail loudly.
-/

open Lean Formalize Tactics

def describe : Tactics.Outcome → String
  | .solved tier tac axioms =>
    let ax := if axioms.isEmpty then "no axioms" else s!"{axioms.toList.map toString}"
    s!"tier {tier} · {tac}  ({ax})"
  | .unsolved tried => s!"UNSOLVED  (tried {tried.length}: {tried})"

def isSolved : Tactics.Outcome → Bool
  | .solved .. => true
  | .unsolved _ => false

def main : IO UInt32 := do
  -- Two environments, not one. Mathlib already defines a `Poly` (in
  -- `Mathlib.NumberTheory.Dioph`), so importing both collides on the name. That is a
  -- convenience here rather than a problem: tier 2 needs no Mathlib whatsoever, so it
  -- runs against a bare kernel environment — which is also evidence that `Poly/` really
  -- is Mathlib-free rather than merely claiming to be.
  let t0 ← IO.monoMsNow
  let envMathlib ← Oracle.mkBaseEnv #[`Mathlib]
  let t1 ← IO.monoMsNow
  IO.println s!"  [{t1 - t0} ms] import Mathlib (for tiers 0-1)"
  let t2 ← IO.monoMsNow
  let envPoly ← Oracle.mkBaseEnv #[`Poly.Basic]
  let t3 ← IO.monoMsNow
  IO.println s!"  [{t3 - t2} ms] import Poly.Basic alone (for tier 2 — no Mathlib)\n"

  let mut solvedPerTier : Array Nat := #[0, 0, 0]
  let mut totalPerTier : Array Nat := #[0, 0, 0]

  for p in Formalize.all do
    let s0 ← IO.monoMsNow
    let env := if p.tier == 2 then envPoly else envMathlib
    let outcome ← Tactics.search env p.preamble p.statement
    let s1 ← IO.monoMsNow
    let mark := if isSolved outcome then "ok  " else "MISS"
    IO.println s!"  {mark} [{s1 - s0} ms] {p.name}"
    IO.println s!"            {describe outcome}"
    totalPerTier := totalPerTier.modify p.tier (· + 1)
    if isSolved outcome then
      solvedPerTier := solvedPerTier.modify p.tier (· + 1)

  IO.println "\n  ── how far the free ladder gets ──"
  for t in [0, 1, 2] do
    IO.println s!"  tier {t}: {solvedPerTier[t]!}/{totalPerTier[t]!} solved with no network"

  -- Floor: the category laws must stay discharged.
  if solvedPerTier[0]! < totalPerTier[0]! then
    IO.println s!"\n  FAIL: tier 0 regressed — the laws should always be discharged locally"
    return 1
  IO.println "\n  tier 0 floor holds; tiers 1-2 are a measurement, not a target"
  return 0

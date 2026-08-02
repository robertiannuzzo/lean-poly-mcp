import Oracle.Kernel

/-!
# The free tiers of the escalation ladder

Tiers 0 and 1 of the agent's ladder (`docs/lean-upgrade-plan.md` §2): tactics that cost
nothing but local CPU. Tier 2 is Aristotle, which costs money and hours; the point of
this file is to reach it as rarely as possible.

Nothing here is trusted. Each candidate is a full `theorem cand : <goal> := by <tactic>`
handed to `Oracle.verify`, so a "solved" result has already been elaborated and
axiom-audited by the same gate everything else goes through. A tactic that closed the
goal by `sorry` or `native_decide` would be rejected here exactly as it would be if
Aristotle had produced it — the ladder gets no special trust for being local.
-/

namespace Tactics

open Lean

/-- A rung: a tactic script and the tier it belongs to. -/
structure Rung where
  tier : Nat
  tactic : String
  deriving Repr

/-- The ladder, cheapest first.

Tier 0 is the reflexive/decision end — these either fire immediately or fail
immediately. Tier 1 adds search, which is slower and occasionally much slower.
`aesop_cat` is Mathlib's category-theory discharge tactic and is the single most
productive rung on this corpus; it is at tier 0 because when it works it is fast. -/
def ladder : List Rung :=
  [ ⟨0, "rfl"⟩
  , ⟨0, "trivial"⟩
  , ⟨0, "simp"⟩
  , ⟨0, "aesop_cat"⟩
  , ⟨0, "decide"⟩
  , ⟨0, "omega"⟩
  , ⟨1, "simp_all"⟩
  , ⟨1, "aesop"⟩
  , ⟨1, "exact?"⟩ ]

/-- What a search concluded. `unsolved` reports what was tried, so a caller escalating to
the paid tier can say what it already ruled out. -/
inductive Outcome where
  | solved (tier : Nat) (tactic : String) (axioms : Array Name)
  | unsolved (tried : List String)
  deriving Repr

/-- Try the ladder against a goal, cheapest rung first, stopping at the first candidate
the oracle accepts.

`maxTier` bounds how much local effort to spend before escalating. Note the goal is
*generated into* the candidate, so no separate statement-match probe is needed: the
theorem we elaborate is by construction the statement we were asked about. -/
def search (env : Environment) (preamble : String) (goal : String)
    (maxTier : Nat := 1) : IO Outcome := do
  let mut tried : List String := []
  for r in ladder do
    if r.tier > maxTier then continue
    tried := tried ++ [r.tactic]
    let src := s!"theorem cand : {goal} := by {r.tactic}"
    match ← Oracle.verify env { preamble := preamble, source := src } with
    | .checked axioms => return .solved r.tier r.tactic axioms
    | _ => pure ()
  return .unsolved tried

end Tactics

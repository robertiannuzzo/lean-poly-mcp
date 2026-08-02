import Oracle.Kernel

/-!
# Oracle tests

Run with:

    lake env lean --run test/OracleTest.lean

Each case is a candidate the oracle must classify correctly. The interesting ones are
the attacks: a `sorry`-ed proof, a `native_decide` proof, a user-declared axiom, and a
correct proof of the *wrong theorem*. None of these are rejected by naming them here —
they are rejected by the audit, which is the difference from v1's blacklist.
-/

open Oracle Lean

structure Case where
  name : String
  source : String
  preamble : String := ""
  decl : Name := `cand
  expected : Option String := none
  /-- Prefix that `describe` must produce. Checked, not eyeballed. -/
  expect : String

def describe : Outcome → String
  | .checked axs =>
    if axs.isEmpty then "checked (no axioms)"
    else s!"checked (axioms: {axs.toList})"
  | .elabFailed d => s!"elabFailed: {(d.splitOn "\n").headD "" }"
  | .missingDecl n => s!"missingDecl: {n}"
  | .unsoundAxioms axs => s!"unsoundAxioms: {axs.toList}"
  | .statementMismatch d => s!"statementMismatch: {(d.splitOn "\n").headD ""}"
  | .badStatement d => s!"badStatement: {(d.splitOn "\n").headD ""}"

def cases : List Case :=
  [ { name := "honest proof"
      source := "theorem cand : ∀ n : Nat, n + 0 = n := fun _ => rfl"
      expect := "checked (no axioms)" }

  , { name := "honest proof, statement matches"
      source := "theorem cand : ∀ n : Nat, n + 0 = n := fun _ => rfl"
      expected := some "∀ n : Nat, n + 0 = n"
      expect := "checked (no axioms)" }

  , { name := "ATTACK: sorry"
      source := "theorem cand : ∀ n : Nat, n = n + 1 := by sorry"
      expect := "unsoundAxioms: [sorryAx]" }

  , { name := "ATTACK: native_decide"
      source := "theorem cand : (List.range 10).length = 10 := by native_decide"
      -- What this leaves behind is not stable across toolchains: v4.28.0 (our pin)
      -- gives `Lean.ofReduceBool` + `Lean.trustCompiler`, while v4.33.0-rc1 minted a
      -- per-declaration axiom named after the declaration itself. Hence the prefix-only
      -- assertion — and hence auditing rather than blacklisting, since a name-based gate
      -- would need names that vary with both declaration and toolchain.
      expect := "unsoundAxioms: " }

  , { name := "ATTACK: home-made axiom"
      source := "axiom oops : ∀ n : Nat, n = n + 1\ntheorem cand : ∀ n : Nat, n = n + 1 := oops"
      expect := "unsoundAxioms: [oops]" }

  , { name := "ATTACK: proves the NEGATION of what was asked (v1's live failure)"
      source := "theorem cand : ∀ n : Nat, n = n + 1 → False := by omega"
      expected := some "∀ n : Nat, n = n + 1"
      expect := "statementMismatch: " }

  , { name := "does not elaborate"
      source := "theorem cand : ∀ n : Nat, n + 0 = n := fun _ => Nat.zero"
      expect := "elabFailed: " }

  , { name := "elaborates, but defines the wrong name"
      source := "theorem somethingElse : True := trivial"
      expect := "missingDecl: cand" }

  , { name := "whitelisted classical reasoning is fine"
      source := "theorem cand : ∀ p : Prop, p ∨ ¬p := fun p => Classical.em p"
      expect := "checked (axioms: [Classical.choice, Quot.sound, propext])" }
  ]

def main : IO UInt32 := do
  let env ← mkBaseEnv #[`Init]
  let mut failed := 0
  for c in cases do
    let outcome ← verify env
      { preamble := c.preamble, source := c.source, declName := c.decl, expected? := c.expected }
    let got := describe outcome
    if got.startsWith c.expect then
      IO.println s!"  ok    {c.name}"
    else
      failed := failed + 1
      IO.println s!"  FAIL  {c.name}"
      IO.println s!"        expected prefix: {c.expect}"
      IO.println s!"        got:             {got}"
  if failed == 0 then
    IO.println s!"  {cases.length} oracle cases passed"
    return 0
  else
    IO.println s!"  {failed} of {cases.length} oracle cases FAILED"
    return 1

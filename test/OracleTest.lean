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
  /-- What the oracle is supposed to say. -/
  want : String

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
      want := "checked, no axioms" }

  , { name := "honest proof, statement matches"
      source := "theorem cand : ∀ n : Nat, n + 0 = n := fun _ => rfl"
      expected := some "∀ n : Nat, n + 0 = n"
      want := "checked" }

  , { name := "ATTACK: sorry"
      source := "theorem cand : ∀ n : Nat, n = n + 1 := by sorry"
      want := "unsoundAxioms [sorryAx] — note `sorry` is only a WARNING to the elaborator" }

  , { name := "ATTACK: native_decide"
      source := "theorem cand : (List.range 10).length = 10 := by native_decide"
      -- Observed on v4.33.0-rc1: this mints a *per-declaration* axiom,
      -- `cand._native.native_decide.ax_1`, rather than the `Lean.ofReduceBool` one
      -- might expect. Which is precisely the argument for auditing rather than
      -- blacklisting: a name-based gate would have to know that name in advance, and
      -- it varies with the declaration. The whitelist needs to know nothing.
      want := "unsoundAxioms [a generated native_decide axiom] — not named anywhere in Kernel.lean" }

  , { name := "ATTACK: home-made axiom"
      source := "axiom oops : ∀ n : Nat, n = n + 1\ntheorem cand : ∀ n : Nat, n = n + 1 := oops"
      want := "unsoundAxioms [oops]" }

  , { name := "ATTACK: proves the NEGATION of what was asked (v1's live failure)"
      source := "theorem cand : ∀ n : Nat, n = n + 1 → False := by omega"
      expected := some "∀ n : Nat, n = n + 1"
      want := "statementMismatch — elaborates and is axiom-clean, but is not the goal" }

  , { name := "does not elaborate"
      source := "theorem cand : ∀ n : Nat, n + 0 = n := fun _ => Nat.zero"
      want := "elabFailed" }

  , { name := "elaborates, but defines the wrong name"
      source := "theorem somethingElse : True := trivial"
      want := "missingDecl cand" }

  , { name := "whitelisted classical reasoning is fine"
      source := "theorem cand : ∀ p : Prop, p ∨ ¬p := fun p => Classical.em p"
      want := "checked, with Classical.choice + propext in the axiom set" }
  ]

def main : IO Unit := do
  IO.println "building base environment (Init only)..."
  let env ← mkBaseEnv #[`Init]
  IO.println ""
  for c in cases do
    let outcome ← verify env
      { preamble := c.preamble, source := c.source, declName := c.decl, expected? := c.expected }
    IO.println s!"── {c.name}"
    IO.println s!"   want: {c.want}"
    IO.println s!"   got:  {describe outcome}"
    IO.println ""

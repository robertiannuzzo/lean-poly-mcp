import Oracle.Kernel

/-!
# Oracle tests against Mathlib

Split from `test/OracleTest.lean` because this one costs ~65s to import Mathlib, and
`OracleTest` costs none. Run via `./scripts/check.sh --full`.

Every question we have about Mathlib goes in **this one program**, deliberately: the
import is the entire cost, so asking eight things costs the same as asking one, and
iterating candidate-by-candidate across separate runs is the expensive mistake.
-/

open Oracle Lean

structure Case where
  name : String
  source : String
  preamble : String := "open CategoryTheory"
  expected : Option String := none
  /-- Prefix that `describe` must produce. -/
  expect : String

def describe : Outcome → String
  | .checked axs => s!"checked (axioms: {axs.toList})"
  | .elabFailed d => s!"elabFailed: {(d.splitOn "\n").headD ""}"
  | .missingDecl n => s!"missingDecl: {n}"
  | .unsoundAxioms axs => s!"unsoundAxioms: {axs.toList}"
  | .statementMismatch d => s!"statementMismatch: {(d.splitOn "\n").headD ""}"
  | .badStatement d => s!"badStatement: {(d.splitOn "\n").headD ""}"

def cases : List Case :=
  [ { name := "identity is a left unit for ≫"
      source := "theorem cand {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) : 𝟙 X ≫ f = f := by simp"
      expect := "checked" }

  , { name := "iso hom ≫ inv = id, with statement match"
      source := "theorem cand {C : Type*} [Category C] {X Y : C} (f : X ≅ Y) : f.hom ≫ f.inv = 𝟙 X := by simp"
      expected := some "∀ {C : Type*} [Category C] {X Y : C} (f : X ≅ Y), f.hom ≫ f.inv = 𝟙 X"
      expect := "checked" }

  , { name := "functors preserve retractions, with statement match"
      source := "theorem cand {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {X Y : C}\n    (f : X ⟶ Y) (g : Y ⟶ X) (h : f ≫ g = 𝟙 X) : F.map f ≫ F.map g = 𝟙 (F.obj X) := by\n  rw [← F.map_comp, h, F.map_id]"
      expected := some "∀ {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X), f ≫ g = 𝟙 X → F.map f ≫ F.map g = 𝟙 (F.obj X)"
      expect := "checked" }

  , { name := "ATTACK: sorry inside a Mathlib proof"
      source := "theorem cand {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) : f ≫ 𝟙 Y = f := by sorry"
      expect := "unsoundAxioms: [sorryAx]" }

  , { name := "harness bug, NOT a mismatch: goal needs an open we did not supply"
      source := "theorem cand : True := trivial"
      preamble := ""
      expected := some "∀ {C : Type*} [Category C] {X : C}, 𝟙 X ≫ 𝟙 X = 𝟙 X"
      expect := "badStatement: " }
  ]

def main : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let env ← mkBaseEnv #[`Mathlib]
  let t1 ← IO.monoMsNow
  IO.println s!"  [{t1 - t0} ms] import Mathlib (once)"
  let mut failed := 0
  for c in cases do
    let s0 ← IO.monoMsNow
    let outcome ← verify env
      { preamble := c.preamble, source := c.source, expected? := c.expected }
    let s1 ← IO.monoMsNow
    let got := describe outcome
    if got.startsWith c.expect then
      IO.println s!"  ok    [{s1 - s0} ms] {c.name}"
    else
      failed := failed + 1
      IO.println s!"  FAIL  {c.name}"
      IO.println s!"        expected prefix: {c.expect}"
      IO.println s!"        got:             {got}"
  if failed == 0 then
    IO.println s!"  {cases.length} Mathlib oracle cases passed"
    return 0
  else
    IO.println s!"  {failed} of {cases.length} Mathlib oracle cases FAILED"
    return 1

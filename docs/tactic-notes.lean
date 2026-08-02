import Tactics.PolyExt

/-!
# Tactic notes — where things fail, and why

Working notes, kept compiling. Each entry is something that cost time in this project;
the failing forms are quoted rather than executed, with the actual diagnostic beneath.
-/

open Poly

/-! ## 1. `native_decide` is excluded from the whitelist on purpose

`decide` asks the *kernel* to evaluate a decision procedure — the result is checked.
`native_decide` compiles the proposition and runs it, then asks you to believe the
compiler. That is a different trust assumption, and it shows up in the axiom set rather
than in the source, which is exactly why the oracle audits axioms instead of grepping.

On our toolchain it introduces `Lean.ofReduceBool` and `Lean.trustCompiler`; on
v4.33.0-rc1 it minted a per-declaration axiom named after the declaration. A gate built
on names would have to track both. `Oracle.axiomWhitelist` names neither.
-/

example : (List.range 10).length = 10 := by decide   -- kernel-checked: fine
-- by native_decide                                   -- would be rejected by the audit

/-! ## 2. `decide` cannot close a `Type`-level goal

`decide` needs a `Decidable` instance, which lives on `Prop`. A goal that is an equality
of *types* has none, and the error names the missing instance rather than the real
problem:

```lean
example (p q : Poly) (i : p.Pos) : (p ⊕' q).Dir (Sum.inl i) = p.Dir i := by decide
-- failed to synthesize Decidable ((p ⊕' q).Dir (Sum.inl i) = p.Dir i)
```

`rfl` is the right tool — the equality holds definitionally because `sum` is `@[reducible]`.
-/

example (p q : Poly) (i : p.Pos) : (p ⊕' q).Dir (Sum.inl i) = p.Dir i := rfl

/-! ## 3. Ladder order decides which tactic gets credit

`Tactics.ladder` tries `simp` before `aesop_cat`. On the benchmark's tier 0 that means
**`simp` solves all seven** and `aesop_cat` — the tactic actually designed for
category-theory goals — never runs. The measurement is "the ladder solved it", not
"`simp` is the better tactic": reorder the rungs and the attribution changes.

Worth knowing before quoting a per-tactic breakdown as if it meant something. The
ordering is chosen for latency, not for credit.

## 4. Macro hygiene: names a tactic introduces are not the caller's

`poly_ext` originally ran `intro i d` internally and left the goal for the caller. The
caller then could not refer to `d`:

```lean
example : negTwice = Lens.id (monomial Bool) := by
  poly_ext
  exact Bool.not_not d   -- unknown identifier 'd'
```

even though a binder called `d` was plainly visible in the goal. Macro-introduced names
are hygienic — deliberately not capturable. The fix was to `intro` *only* on the branch
that closes the goal outright, and otherwise hand back the un-introduced `∀` so the
caller binds its own names. Introducing inaccessible binders and leaving them behind is
worse than not introducing at all.
-/

def negTwice : Lens (monomial Bool) (monomial Bool) := ⟨id, fun _ d => !(!d)⟩

example : negTwice = Lens.id (monomial Bool) := by
  poly_ext
  intro _ b          -- the caller's own names
  exact Bool.not_not b

/-! ## 5. `exact?` proves nothing new — it finds what you already proved

On the tier-2 corpus `exact?` "solves" lens associativity by locating
`Poly.Lens.comp_assoc`, which is a lemma of `Poly/Basic.lean`. That is library lookup.
A benchmark of restated library lemmas reports a high number that means nothing, which
is why `Formalize/Benchmark.lean` marks the entries that are genuinely absent from the
kernel `[novel]` — and why the one entry needing induction (`a trace of n steps has n
entries`) is the informative one: no discharge tactic does induction, so it is a true
miss and a real argument for escalating.

## 6. `rfl` succeeds surprisingly often here, and that is a design choice

Most `Poly` laws hold by `rfl` because `Lens.comp` was defined so they would, and the
structure operators are `@[reducible]`. That is deliberate — no coherence bookkeeping
leaks into anything built on top — but it means `rfl` passing is weak evidence that a
*statement* is interesting. The benchmark's value is in the misses.
-/

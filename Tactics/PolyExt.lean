import Poly.Basic

/-!
# `poly_ext` — extensionality for lenses

Two lenses are equal when their forward maps agree and their backward maps agree. That
is easy to state and annoying to *use*, because `onDir`'s type mentions `onPos`:

```lean
l.onDir : (i : p.Pos) → q.Dir (l.onPos i) → p.Dir i
```

so once the forward maps are only *propositionally* equal, the backward maps do not even
live in the same type and the goal becomes an `HEq`. This file provides the two lemmas
that matter and a tactic that picks between them, so downstream proofs never have to
think about the transport.

Most real goals fall in the easy case — the forward maps agree *definitionally* and only
the backward maps need work — so that is the case `poly_ext` tries first.
-/

namespace Poly.Lens

/-- Full extensionality. Stated with `HEq` because the backward maps genuinely inhabit
different types until the forward maps are known equal; proved by cases, which is the
only thing that makes the two types line up. -/
theorem ext {p q : Poly.{u}} : ∀ {l₁ l₂ : Lens p q},
    l₁.onPos = l₂.onPos → HEq l₁.onDir l₂.onDir → l₁ = l₂
  | ⟨_, _⟩, ⟨_, _⟩, rfl, .refl _ => rfl

/-- The usable case: the forward maps are *the same function*, so the backward maps share
a type and ordinary function extensionality applies. This is what almost every goal
needs. -/
theorem ext_onDir {p q : Poly.{u}} {f : p.Pos → q.Pos}
    {d₁ d₂ : (i : p.Pos) → q.Dir (f i) → p.Dir i}
    (h : ∀ i d, d₁ i d = d₂ i d) : Lens.mk f d₁ = Lens.mk f d₂ := by
  have hd : d₁ = d₂ := funext fun i => funext fun d => h i d
  cases hd; rfl

end Poly.Lens

/-- Reduce a goal `l₁ = l₂` between lenses to its components.

Tries three things in order:

1. the definitional-forward-map case, introducing the position and direction and closing
   by `rfl` — the common case, which finishes outright;
2. the same lemma *without* introducing, leaving `∀ i d, …` for the caller;
3. full extensionality, leaving the `HEq` obligation, with `rfl` attempted on both parts.

**Why step 2 exists — a hygiene trap.** Names a macro introduces are hygienic: they are
not the caller's `i` and `d`, so a caller writing `poly_ext; exact Bool.not_not d` gets
`unknown identifier 'd'` even though a binder called `d` is visibly in the goal. Doing
the `intro` only on the branch that *closes* the goal keeps the convenience where it is
free and hands back an un-introduced `∀` everywhere else, so the caller binds its own
names. Introducing inaccessible binders and leaving them for the user would be worse than
not introducing at all. -/
syntax "poly_ext" : tactic

macro_rules
  | `(tactic| poly_ext) =>
    `(tactic|
        first
          | (apply Poly.Lens.ext_onDir; intro i d; rfl)
          | apply Poly.Lens.ext_onDir
          | (apply Poly.Lens.ext <;> try rfl))

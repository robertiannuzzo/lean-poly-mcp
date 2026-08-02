/-!
# Formalize

Category-theory autoformalization, and the graded benchmark that doubles as the eval
harness:

* Tier 0 — identity/associativity laws, functors preserve isomorphisms, naturality.
* Tier 1 — Yoneda-adjacent statements, universal properties, triangle identities.
* Tier 2 — statements about `Poly` itself: `Lens` composition is associative, `◁` is
  monoidal with unit `y`, `Lens p y ≃ (i : p.Pos) → p.Dir i`. The system proving theorems
  about the structure it is built from is the point, not a flourish.

  Because our toolchain matches Aristotle's, we submit our *own* project — so Aristotle
  sees `Poly/Basic.lean` and can prove theorems about our kernel. That is what makes this
  tier real rather than aspirational.

One untrusted proposer (Aristotle) feeds one oracle, reached only after the free local
tiers (`aesop_cat`, then `exact?`/`apply?`) have failed.

Not yet implemented — see `docs/lean-upgrade-plan.md` §7.
-/

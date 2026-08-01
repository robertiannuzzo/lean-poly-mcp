/-!
# Formalize

Category-theory autoformalization, and the graded benchmark that doubles as the eval
harness:

* Tier 0 — identity/associativity laws, functors preserve isomorphisms, naturality.
* Tier 1 — Yoneda-adjacent statements, universal properties, triangle identities.
* Tier 2 — statements about `Poly` itself: `Lens` composition is associative, `◁` is
  monoidal with unit `y`, `Lens y p ≃ Σ i, p.Dir i`. The system proving theorems about
  the structure it is built from is the point, not a flourish.

Two untrusted proposers (an LLM, and Aristotle) feed one oracle.

Not yet implemented — see `docs/lean-upgrade-plan.md` §6.
-/

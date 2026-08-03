import Formalize.Benchmark
import Formalize.Miner
import Formalize.PaperBridge
import Formalize.Report

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

`Formalize.Miner` adds the Mathlib side of the corpus: it mines `CategoryTheory.*`
declarations from an already-imported environment and renders their types as Lean
statement strings. The caller pays the Mathlib import once, then feeds those statements
through the same oracle/search/Aristotle path as the hand-curated benchmark.

`Formalize.Report` turns that into a benchmark generator: mine semantic namespace
slices, run the free ladder, and print the locally-unsolved statements that are worth
considering for Aristotle.
-/

/-!
# The graded benchmark

The corpus is data, not code — statements as source strings, elaborated by the oracle
against a base environment. That is deliberate: it is exactly the shape Aristotle
consumes, so the same corpus drives the free ladder and the paid tier without
translation.

Three tiers, in the sense of §7 of the plan:

* **Tier 0** — the laws. Identity and associativity, functoriality, naturality.
* **Tier 1** — statements needing a real lemma or a rewrite, not just a discharge tactic.
* **Tier 2** — statements about **`Poly` itself**. These are the point: the system
  proving theorems about the structure it is built from, verified by its own kernel.
  They elaborate against `Poly.Basic`, which the runner imports alongside Mathlib.

**How far tiers 0/1 get with no network is the reportable result.** A benchmark on which
everything is `rfl` measures nothing, so the corpus deliberately includes statements the
free ladder is not expected to reach — those are what the paid tier is *for*, and
knowing which ones is the point of running this.
-/

namespace Formalize

structure Problem where
  tier : Nat
  name : String
  /-- Lines prepended to the candidate — typically `open` commands. -/
  preamble : String := "open CategoryTheory"
  /-- The goal, as Lean source. -/
  statement : String
  deriving Repr

/-! ## Tier 0 — the laws -/

def tier0 : List Problem :=
  [ { tier := 0, name := "identity is a left unit for ≫"
      statement := "∀ {C : Type} [Category C] {X Y : C} (f : X ⟶ Y), 𝟙 X ≫ f = f" }
  , { tier := 0, name := "identity is a right unit for ≫"
      statement := "∀ {C : Type} [Category C] {X Y : C} (f : X ⟶ Y), f ≫ 𝟙 Y = f" }
  , { tier := 0, name := "composition is associative"
      statement := "∀ {C : Type} [Category C] {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z), (f ≫ g) ≫ h = f ≫ g ≫ h" }
  , { tier := 0, name := "an iso's hom ≫ inv is the identity"
      statement := "∀ {C : Type} [Category C] {X Y : C} (f : X ≅ Y), f.hom ≫ f.inv = 𝟙 X" }
  , { tier := 0, name := "functors preserve identities"
      statement := "∀ {C D : Type} [Category C] [Category D] (F : C ⥤ D) (X : C), F.map (𝟙 X) = 𝟙 (F.obj X)" }
  , { tier := 0, name := "functors preserve composition"
      statement := "∀ {C D : Type} [Category C] [Category D] (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), F.map (f ≫ g) = F.map f ≫ F.map g" }
  , { tier := 0, name := "naturality square commutes"
      statement := "∀ {C D : Type} [Category C] [Category D] {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (f : X ⟶ Y), F.map f ≫ α.app Y = α.app X ≫ G.map f" }
  ]

/-! ## Tier 1 — needs a lemma or a rewrite -/

def tier1 : List Problem :=
  [ { tier := 1, name := "functors preserve retractions"
      statement := "∀ {C D : Type} [Category C] [Category D] (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X), f ≫ g = 𝟙 X → F.map f ≫ F.map g = 𝟙 (F.obj X)" }
  , { tier := 1, name := "functors preserve isomorphisms"
      statement := "∀ {C D : Type} [Category C] [Category D] (F : C ⥤ D) {X Y : C} (f : X ≅ Y), F.map f.hom ≫ F.map f.inv = 𝟙 (F.obj X)" }
  , { tier := 1, name := "inverses are unique"
      statement := "∀ {C : Type} [Category C] {X Y : C} (f : X ⟶ Y) (g h : Y ⟶ X), f ≫ g = 𝟙 X → h ≫ f = 𝟙 Y → g = h" }
  , { tier := 1, name := "vertical composite of natural transformations is natural"
      statement := "∀ {C D : Type} [Category C] [Category D] {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H) {X Y : C} (f : X ⟶ Y), F.map f ≫ (α ≫ β).app Y = (α ≫ β).app X ≫ H.map f" }
  ]

/-! ## Tier 2 — about `Poly` itself

These need no Mathlib at all; they elaborate against our own kernel.

**A caveat that matters for reading the score.** Several of these restate lemmas that
already exist in `Poly/Basic.lean`, so `exact?` solves them by *finding* the lemma. That
is library lookup, not the system proving something about itself, and a tier-2 corpus
made only of those would report a flattering number that means nothing. The entries
marked `[novel]` below are deliberately **not** in `Poly/Basic.lean` — they are the ones
that carry information about what the free ladder can actually do. -/

def tier2 : List Problem :=
  [ { tier := 2, name := "lens composition is associative"
      preamble := "open Poly"
      statement := "∀ {p q r s : Poly} (h : Lens r s) (g : Lens q r) (f : Lens p q), Lens.comp (Lens.comp h g) f = Lens.comp h (Lens.comp g f)" }
  , { tier := 2, name := "identity is a left unit for lens composition"
      preamble := "open Poly"
      statement := "∀ {p q : Poly} (f : Lens p q), Lens.comp (Lens.id q) f = f" }
  , { tier := 2, name := "sections are servers (round-trip)"
      preamble := "open Poly"
      statement := "∀ (p : Poly) (s : Section p), (sectionEquiv p).toFun ((sectionEquiv p).invFun s) = s" }
  , { tier := 2, name := "a lens out of y is a request (round-trip)"
      preamble := "open Poly"
      statement := "∀ (p : Poly) (i : p.Pos), (posEquiv p).toFun ((posEquiv p).invFun i) = i" }
  , { tier := 2, name := "one round-trip is ask, answer, update"
      preamble := "open Poly"
      statement := "∀ {S : Type} {p : Poly} (agent : Agent S p) (server : Lens p y) (s : S), step agent server s = agent.onDir s ((sectionEquiv p).toFun server (agent.onPos s))" }
  , { tier := 2, name := "◁ is unital on the right: p ◁ y positions are p positions"
      preamble := "open Poly"
      statement := "∀ (p : Poly) (i : p.Pos) (f : p.Dir i → PUnit), ((⟨i, f⟩ : (p ◁ y).Pos)).1 = i" }
  , { tier := 2, name := "the registry's direction is the summand's direction"
      preamble := "open Poly"
      statement := "∀ {I : Type} (pf : I → Poly) (i : I) (j : (pf i).Pos), (Poly.sigma pf).Dir ⟨i, j⟩ = (pf i).Dir j" }

    -- [novel] — not lemmas of Poly/Basic.lean, so `exact?` cannot look them up.
  , { tier := 2, name := "[novel] ⊗ directions are pairs of directions"
      preamble := "open Poly"
      statement := "∀ (p q : Poly) (i : p.Pos) (j : q.Pos), (p ⊗ q).Dir (i, j) = (p.Dir i × q.Dir j)" }
  , { tier := 2, name := "[novel] a trace of n steps has n entries"
      preamble := "open Poly"
      statement := "∀ {S : Type} {p : Poly} (agent : Agent S p) (server : Lens p y) (n : Nat) (s : S), (trace agent server n s).length = n" }
  , { tier := 2, name := "[novel] a one-step trace is the starting state"
      preamble := "open Poly"
      statement := "∀ {S : Type} {p : Poly} (agent : Agent S p) (server : Lens p y) (s : S), trace agent server 1 s = [s]" }
  , { tier := 2, name := "[novel] the coproduct's left directions are the left summand's"
      preamble := "open Poly"
      statement := "∀ (p q : Poly) (i : p.Pos), (p ⊕' q).Dir (Sum.inl i) = p.Dir i" }
  ]

def all : List Problem := tier0 ++ tier1 ++ tier2

end Formalize

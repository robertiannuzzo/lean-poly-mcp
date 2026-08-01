/-!
# The Poly kernel

Objects of `Poly` (equivalently, containers in the sense of Abbott–Altenkirch–Ghani),
lenses between them, and the four monoidal structures we need.

Deliberately **Mathlib-free**, for two reasons: it compiles in seconds, and it is the
part of the development we most want to be readable on its own. `Poly/Bridge.lean`
relates it to `Mathlib.Data.PFunctor`; `Poly/Category.lean` installs the Mathlib
`Category` instance.
-/

universe u v

/-- A polynomial functor `p = Σ_{i : Pos} y ^ Dir i`, presented as a container:
positions are requests, directions are the responses that request admits. -/
structure Poly : Type (u + 1) where
  Pos : Type u
  Dir : Pos → Type u

namespace Poly

/-- The functor `p` actually denotes: `p X = Σ (i : Pos), Dir i → X`. -/
def apply (p : Poly.{u}) (X : Type u) : Type u := (i : p.Pos) × (p.Dir i → X)

/-- A morphism of polynomial functors — a dependent lens. Forward on positions,
**backward** on directions: a request is translated outward, and a response to the
translated request is translated back. -/
structure Lens (p q : Poly.{u}) : Type u where
  onPos : p.Pos → q.Pos
  onDir : (i : p.Pos) → q.Dir (onPos i) → p.Dir i

/-- A bare equivalence, so this file need not depend on Mathlib's `Equiv`. -/
structure Equiv (α : Type u) (β : Type v) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b

namespace Lens

/-- The identity lens. -/
protected def id (p : Poly.{u}) : Lens p p where
  onPos i := i
  onDir _ d := d

/-- Composition of lenses: forwards compose forwards, backwards compose backwards
in the opposite order. -/
protected def comp {p q r : Poly.{u}} (g : Lens q r) (f : Lens p q) : Lens p r where
  onPos := g.onPos ∘ f.onPos
  onDir i d := f.onDir i (g.onDir (f.onPos i) d)

/-!
The category laws hold by `rfl` — composition was defined so that they would, which is
worth noticing rather than hiding: it means no coherence bookkeeping leaks into
anything built on top.
-/

@[simp] theorem id_comp {p q : Poly.{u}} (f : Lens p q) : Lens.comp (Lens.id q) f = f := rfl

@[simp] theorem comp_id {p q : Poly.{u}} (f : Lens p q) : Lens.comp f (Lens.id p) = f := rfl

theorem comp_assoc {p q r s : Poly.{u}} (h : Lens r s) (g : Lens q r) (f : Lens p q) :
    Lens.comp (Lens.comp h g) f = Lens.comp h (Lens.comp g f) := rfl

end Lens

/-! ## Distinguished objects -/

/-- The unit for composition: one position, one direction. -/
def y : Poly.{u} := ⟨PUnit, fun _ => PUnit⟩

/-- The monomial `S y^S` — positions and directions both `S`. A system with state `S`
is a lens out of this. -/
def monomial (S : Type u) : Poly.{u} := ⟨S, fun _ => S⟩

/-! ## Sections: the server -/

/-- A section of `p`: a response for every request. -/
def Section (p : Poly.{u}) : Type u := (i : p.Pos) → p.Dir i

/-- **Sections are servers.** A lens `p → y` is exactly a dependent function assigning
to each request a response to *that* request.

This is the statement that makes "the MCP server is a section of its interface
polynomial" a typechecked fact rather than a slogan. -/
def sectionEquiv (p : Poly.{u}) : Equiv (Lens p y) (Section p) where
  toFun l i := l.onDir i PUnit.unit
  invFun f := ⟨fun _ => PUnit.unit, fun i _ => f i⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Lenses out of `y` pick a request, and nothing more.** Note carefully that this
is `p.Pos` and *not* `Σ i, p.Dir i`: the backward map of a lens `y → p` lands in
`y.Dir = PUnit`, so it carries no response. A completed call is `Interaction p`
below, which is not a hom-set of `Poly`. -/
def posEquiv (p : Poly.{u}) : Equiv (Lens y p) p.Pos where
  toFun l := l.onPos PUnit.unit
  invFun i := ⟨fun _ => i, fun _ _ => PUnit.unit⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A completed tool call: a request together with a response *to that request*. -/
def Interaction (p : Poly.{u}) : Type u := (i : p.Pos) × p.Dir i

/-! ## Dynamics: agents

A system with state `S` interacting over `p` is a lens `S y^S → p`. The composite of
such an agent with a server is a state-transition function — one round-trip of the
protocol *is* lens composition.
-/

/-- An agent with state `S` speaking protocol `p`. -/
abbrev Agent (S : Type u) (p : Poly.{u}) : Type u := Lens (monomial S) p

/-- **One round-trip is a composite.** Given an agent and a server, the composite lens
`S y^S → y` is exactly a function `S → S`: the agent's next request, the server's
response to it, and the agent's state update, in one term. -/
def step {S : Type u} {p : Poly.{u}} (agent : Agent S p) (server : Lens p y) : S → S :=
  (sectionEquiv (monomial S)).toFun (Lens.comp server agent)

/-- Unfolding `step` to the obvious thing: ask, answer, update. -/
theorem step_eq {S : Type u} {p : Poly.{u}} (agent : Agent S p) (server : Lens p y)
    (s : S) :
    step agent server s
      = agent.onDir s ((sectionEquiv p).toFun server (agent.onPos s)) := rfl

/-- Run an agent for `n` steps, recording every state visited. The resulting list is a
path through the interaction tree — the data the front end draws. -/
def trace {S : Type u} {p : Poly.{u}} (agent : Agent S p) (server : Lens p y) :
    Nat → S → List S
  | 0, _ => []
  | n + 1, s => s :: trace agent server n (step agent server s)

/-! ## Monoidal structures -/

/-- Coproduct. The tool registry: adding a tool is taking a coproduct. -/
def sum (p q : Poly.{u}) : Poly.{u} where
  Pos := p.Pos ⊕ q.Pos
  Dir
    | .inl i => p.Dir i
    | .inr j => q.Dir j

/-- Product: choose a position in each, respond in *one* of them. -/
def prod (p q : Poly.{u}) : Poly.{u} where
  Pos := p.Pos × q.Pos
  Dir := fun (i, j) => p.Dir i ⊕ q.Dir j

/-- Dirichlet (parallel) product: run both, respond in both. -/
def tensor (p q : Poly.{u}) : Poly.{u} where
  Pos := p.Pos × q.Pos
  Dir := fun (i, j) => p.Dir i × q.Dir j

/-- Composition `p ◁ q`: a request in `p`, and for each possible response a follow-up
request in `q`. This is the two-step protocol. -/
def compose (p q : Poly.{u}) : Poly.{u} where
  Pos := (i : p.Pos) × (p.Dir i → q.Pos)
  Dir := fun ⟨i, f⟩ => (d : p.Dir i) × q.Dir (f d)

@[inherit_doc] infixl:70 " ◁ " => compose
@[inherit_doc] infixl:65 " ⊕' " => sum
@[inherit_doc] infixl:70 " ⊗ " => tensor

end Poly

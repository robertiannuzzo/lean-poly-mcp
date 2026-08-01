import Poly.Basic

/-!
# Effectful sections

`Poly/Basic.lean` proves that a server is a section, `Lens p y`. That statement is
exact for a *pure* server, and the Phase 2 MCP server really was one.

It stops being exact the moment a handler does something. Verifying a proof means
running the elaborator, which is `IO`, and

  `(i : p.Pos) → IO (p.Dir i)`

is **not** a `Lens p y`. It is a section of `p` in the Kleisli category of `IO`. The
distinction is small and easy to paper over, so it gets a name and a file rather than a
footnote: `Lens p y` claims the server is a function from requests to responses, and
that claim is false once answering a request can fail, block, or read the outside world.

What survives is the embedding: every pure section is an effectful one, and the pure
statement continues to hold on that image. Nothing more is claimed here — in
particular, no proof relates the compiled program's actual IO behaviour to any of this.
-/

namespace Poly

/-- A section of `p` in the Kleisli category of `IO`: a response to each request,
computed effectfully. Restricted to `Poly.{0}` because `IO : Type → Type`. -/
def IOSection (p : Poly.{0}) : Type := (i : p.Pos) → IO (p.Dir i)

/-- Every pure section is an effectful one. This is the embedding along which the
`Lens p y` statement continues to hold. -/
def Section.toIO {p : Poly.{0}} (s : Section p) : IOSection p := fun i => pure (s i)

/-- A lens `p → y` gives an effectful section, via its pure one. -/
def Lens.toIOSection {p : Poly.{0}} (l : Lens p y) : IOSection p :=
  Section.toIO ((sectionEquiv p).toFun l)

/-- The embedding is faithful on the pure fragment: reading a pure section back out of
its effectful image returns the same responses. -/
theorem toIO_pure {p : Poly.{0}} (s : Section p) (i : p.Pos) :
    Section.toIO s i = pure (s i) := rfl

end Poly

import Poly.Basic

/-!
# Kernel tests

A concrete two-method protocol, a server, and an agent — small enough to check by
hand, dependent enough that getting the variance of `Lens.onDir` backwards would not
compile.
-/

open Poly

/-- A toy protocol: `ping` is answered with a `Bool`, `count` with a `Nat`. The two
responses have *different types*, which is the whole point. -/
inductive Toy where
  | ping
  | count
  deriving Repr, DecidableEq

/-- `abbrev`, not `def`: instance search only unfolds at reducible transparency, and
without that a numeral like `42` cannot be seen to inhabit `toyP.Dir .count`. -/
abbrev ToyDir : Toy → Type
  | .ping => Bool
  | .count => Nat

abbrev toyP : Poly := ⟨Toy, ToyDir⟩

/-- The server, as a section. Each branch must produce a value of *that* request's
response type — `42` for `count`, `true` for `ping`. Swapping them is a type error,
not a runtime bug. -/
def toyServer : Lens toyP y :=
  (sectionEquiv toyP).invFun fun
    | .ping => true
    | .count => 42

/-- Agent state. The constructor determines which request is issued next, so the
dependent response type reduces when we pattern-match. -/
inductive St where
  | counting (total : Nat)
  | pinging (total : Nat)
  deriving Repr, DecidableEq

/-- An agent: accumulate one `count`, then `ping`, and keep going while the server
says `true`. -/
def toyAgent : Agent St toyP where
  onPos
    | .counting _ => .count
    | .pinging _ => .ping
  onDir
    | .counting t => fun (n : Nat) => .pinging (t + n)
    | .pinging t => fun (b : Bool) => if b then .counting t else .pinging t

/-! ## The run -/

-- Expected: counting 0 → pinging 42 → counting 42 → pinging 84
#guard trace toyAgent toyServer 4 (.counting 0)
        = [.counting 0, .pinging 42, .counting 42, .pinging 84]

/-- The composite really is a state-transition function, computed by lens
composition alone. -/
example : step toyAgent toyServer (.counting 0) = .pinging 42 := rfl

/-- ...and it agrees with doing it by hand: ask, answer, update. -/
example (s : St) :
    step toyAgent toyServer s
      = toyAgent.onDir s ((sectionEquiv toyP).toFun toyServer (toyAgent.onPos s)) :=
  step_eq toyAgent toyServer s

/-! ## Negative test

Uncommenting this must fail: it answers `count` with a `Bool`. Kept as a comment
because a build that fails is not a test suite.

```lean
def badServer : Lens toyP y :=
  (sectionEquiv toyP).invFun fun
    | .ping => true
    | .count => false
```

Verified against v4.33.0-rc1; the compiler says, verbatim:

```
error: Type mismatch
  false
has type
  Bool
but is expected to have type
  toyP.Dir Toy.count
```
-/

/-! ## Composition

A position of `p ◁ p` is a first request together with a follow-up request for every
possible response to it — a two-step protocol, as a single object. -/

example : (toyP ◁ toyP).Pos = ((i : Toy) × (ToyDir i → Toy)) := rfl

/-- Directions of the composite are the pairs of responses actually realisable. -/
example (i : Toy) (f : ToyDir i → Toy) :
    (toyP ◁ toyP).Dir ⟨i, f⟩ = ((d : ToyDir i) × ToyDir (f d)) := rfl

import Poly.Basic

/-!
# Poly

The vendored Poly kernel: objects, lenses, the monoidal structures, and the
equivalences that license the design —

  `Lens p y ≃ ((i : p.Pos) → p.Dir i)`  (sections of `p` are servers)
  `Lens (S y^S) y ≃ (S → S)`            (agent ∘ server is a state transition)
  `Lens y p ≃ p.Pos`                    (a lens out of `y` is a request, no response)

Deliberately small and self-contained rather than depending on `sinhp/Poly`, which
pins an older toolchain (v4.28.0-rc1) than Mathlib master (v4.33.0-rc1). See
`Poly/Bridge.lean` for the agreement proof against `Mathlib.Data.PFunctor`.
-/

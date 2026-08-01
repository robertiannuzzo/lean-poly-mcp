/-!
# Poly

The vendored Poly kernel: objects, lenses, the monoidal structures, and the two
equivalences that license the whole design —

  `Lens y p ≃ (i : p.Pos) × p.Dir i`   (elements of `p` are completed tool calls)
  `Lens p y ≃ ((i : p.Pos) → p.Dir i)` (sections of `p` are servers)

Deliberately small and self-contained rather than depending on `sinhp/Poly`, which
pins an older toolchain (v4.28.0-rc1) than Mathlib master (v4.33.0-rc1). See
`Poly/Bridge.lean` for the agreement proof against `Mathlib.Data.PFunctor`.

Not yet implemented — see `docs/lean-upgrade-plan.md` §3.
-/

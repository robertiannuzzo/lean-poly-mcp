import Tactics.PolyExt
import Tactics.Search

/-!
# Tactics

`poly_ext` — extensionality for lenses, handling the dependent-`HEq` obligation that
makes `Lens` equalities awkward by hand.

`Tactics.search` — tiers 0 and 1 of the escalation ladder, run through the oracle so a
local success is trusted no more than a remote one.
-/

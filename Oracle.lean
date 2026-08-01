/-!
# Oracle

The only trusted component. Elaborates candidate declarations in-process via
`Lean.Elab.runFrontend`, then audits the resulting term with `Lean.collectAxioms`,
accepting only when the axiom set is contained in
`{propext, Classical.choice, Quot.sound}` — `sorryAx` is rejected outright.

This replaces v1's substring blacklist (`v1-idris/src/MCP/Proof.idr`, `forbiddenTokens`)
with a kernel-level audit, and adds the check v1 could not do at all: that the
elaborated statement is α-equivalent to the statement that was requested.

Not yet implemented — see `docs/lean-upgrade-plan.md` §5.
-/

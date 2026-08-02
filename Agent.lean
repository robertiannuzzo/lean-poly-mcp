import Agent.Prover
import Agent.Runner

/-!
# Agent

An agent is a lens `S y^S → MCP`: `onPos` picks the next request from the current
state, `onDir` folds the response back into a new state. Running it is iterating that
lens against the server's section, and the resulting session is a path through the
cofree comonoid `𝒞_MCP` — which is exactly the data the front end draws.

Not yet implemented — see `docs/lean-upgrade-plan.md` §9 — the escalation ladder in §2.
-/

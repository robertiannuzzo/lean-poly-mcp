/-!
# Mcp

The MCP interface as a polynomial functor: `Method` are the positions, `ResultOf` the
directions, and the server is a section — a `Lens MCP y`. Transport is JSON-RPC over
stdio via `Lean.Data.JsonRpc`, replacing the hand-written `v1-idris/src/JSONRPC.idr`.

The constraint that matters: the *live* dispatch must be the section itself, not a
parallel idealized copy of it. See `docs/lean-upgrade-plan.md` §1, §4.

Not yet implemented.
-/

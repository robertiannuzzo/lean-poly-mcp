import Mcp.Transport

/-!
The MCP server executable: JSON-RPC 2.0 over stdio, newline-delimited.

Arguments are the modules to import into the oracle's base environment. This is a real
tradeoff, not a knob for its own sake:

    ./.lake/build/bin/server                 -- Init only; starts instantly
    ./.lake/build/bin/server Mathlib         -- ~65s startup, then category theory

The cost is paid **once**, at startup. Every subsequent `check` reuses the environment
and takes milliseconds — which is the whole reason the oracle elaborates in-process
instead of shelling out to `lake env lean` per candidate.
-/

def main (args : List String) : IO Unit := do
  let imports := if args.isEmpty then [`Init] else args.map (·.toName)
  Mcp.logErr s!"lean-poly-mcp: importing {imports} ..."
  let t0 ← IO.monoMsNow
  let env ← Oracle.mkBaseEnv imports.toArray
  let t1 ← IO.monoMsNow
  Mcp.logErr s!"lean-poly-mcp: ready in {t1 - t0} ms"
  Mcp.loop env (← IO.getStdin) (← IO.getStdout)
  Mcp.logErr "lean-poly-mcp: exiting (stdin closed)"

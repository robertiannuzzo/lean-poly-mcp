/-!
The MCP server executable: JSON-RPC 2.0 over stdio, newline-delimited — the same
framing `v1-idris/gui/server_gui.py` already speaks, so that bridge survives the port.

Not yet implemented; this stub exists so the `server` target in `lakefile.toml`
resolves.
-/

def main : IO Unit :=
  IO.eprintln "lean-poly-mcp: not implemented yet (see docs/lean-upgrade-plan.md)"

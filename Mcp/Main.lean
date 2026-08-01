import Mcp.Transport

/-!
The MCP server executable: JSON-RPC 2.0 over stdio, newline-delimited.

    echo '{"jsonrpc":"2.0","id":1,"method":"tools/list"}' | ./.lake/build/bin/server
-/

def main : IO Unit := do
  Mcp.logErr "lean-poly-mcp server starting"
  Mcp.loop (← IO.getStdin) (← IO.getStdout)
  Mcp.logErr "lean-poly-mcp server exiting (stdin closed)"

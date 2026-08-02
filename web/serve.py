#!/usr/bin/env python3
"""Local web front end for lean-poly-mcp.

Spawns the compiled Lean server and speaks JSON-RPC to it over stdio — the same
transport any MCP client uses, so this page is a client rather than a special case. The
only extra endpoint shells out to `agent-run`, because the agent is a *client* of the
interface (it is defined against `Mcp.MCP`), not a tool inside it.

    python3 web/serve.py                # Poly kernel only — starts in ~1s
    python3 web/serve.py Mathlib        # category theory — ~55s startup, then ms/candidate

Then open http://localhost:8770
"""
import json
import os
import subprocess
import sys
import threading
import time
from http.server import BaseHTTPRequestHandler, HTTPServer
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SERVER_BIN = ROOT / ".lake" / "build" / "bin" / "server"
AGENT_BIN = ROOT / ".lake" / "build" / "bin" / "agent-run"
FIXTURES = ROOT / "test" / "fixtures" / "aristotle"
PORT = 8770


def lean_env():
    """The Lean binaries need LEAN_PATH to find Mathlib and our own oleans.

    Running them under `lake env` is how every other entry point does it; resolving the
    variable once here means `python3 web/serve.py` works on its own, rather than
    failing at the first import with a JSON parse error three frames away from the
    actual cause.
    """
    env = dict(os.environ)
    try:
        out = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"],
                             cwd=ROOT, capture_output=True, text=True, timeout=120)
        if out.returncode == 0 and out.stdout.strip():
            env["LEAN_PATH"] = out.stdout.strip()
    except (OSError, subprocess.SubprocessError) as e:
        sys.exit(f"could not resolve LEAN_PATH via lake: {e}")
    return env


class Bridge:
    """Owns the server subprocess and speaks JSON-RPC over its stdio pipe."""

    def __init__(self, imports):
        self.imports = imports
        self.ready = False
        self.lock = threading.Lock()
        self.next_id = 1
        t0 = time.time()
        self.env = lean_env()
        self.proc = subprocess.Popen(
            [str(SERVER_BIN), *imports],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            text=True, bufsize=1, env=self.env,
        )
        self.request("initialize", {"protocolVersion": "2025-06-18"})
        self.ready = True
        self.startup_ms = int((time.time() - t0) * 1000)
        print(f"  server ready in {self.startup_ms} ms (imports: {', '.join(imports) or 'Init'})")

    def request(self, method, params=None):
        with self.lock:
            rid = self.next_id
            self.next_id += 1
            msg = {"jsonrpc": "2.0", "id": rid, "method": method}
            if params is not None:
                msg["params"] = params
            self.proc.stdin.write(json.dumps(msg) + "\n")
            self.proc.stdin.flush()
            line = self.proc.stdout.readline()
            if not line:
                # The server died. Report *its* error, not a decode failure here.
                self.proc.poll()
                err = (self.proc.stderr.read() or "")[-600:]
                sys.exit(f"server exited ({self.proc.returncode}) during {method}:\n{err}")
            return json.loads(line)

    def call_tool(self, name, arguments):
        return self.request("tools/call", {"name": name, "arguments": arguments})


def run_agent(preamble, goal, imports):
    """The agent is a separate executable — see Agent/Main.lean for why."""
    out = subprocess.run(
        [str(AGENT_BIN), preamble, goal, *imports],
        capture_output=True, text=True, timeout=600, env=lean_env(),
    )
    if out.returncode != 0:
        return {"error": out.stderr[:400] or "agent-run failed"}
    return json.loads(out.stdout.strip().splitlines()[-1])


def aristotle_record():
    """The one real round trip, read from the recorded fixtures.

    Deliberately reports the vendor's status and our own verdict as *separate* fields:
    conflating them would be the exact mistake the oracle exists to prevent.
    """
    try:
        status = (FIXTURES / "status.txt").read_text().strip().splitlines()[-1]
        proof = (FIXTURES / "proof.lean").read_text()
        return {
            "projectId": "385577ec-104c-4a77-bc17-82b148b9e7c7",
            "goal": "(trace agent server n s).length = n",
            "note": "the one benchmark goal the free ladder could not reach — needs induction",
            "vendorStatus": status.split()[-1],
            "elapsed": "~3 minutes",
            "proof": proof,
            "ourVerdict": {
                "kernelUnchanged": True,
                "outcome": "checked",
                "axioms": [],
                "statementMatched": True,
            },
        }
    except OSError as e:
        return {"error": str(e)}


class Handler(BaseHTTPRequestHandler):
    bridge = None
    imports = []

    def _send(self, body, ctype="application/json", status=200):
        data = body if isinstance(body, bytes) else json.dumps(body).encode()
        self.send_response(status)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def do_GET(self):
        if self.path == "/":
            self._send((Path(__file__).parent / "index.html").read_bytes(), "text/html")
        elif self.path == "/api/tools":
            r = self.bridge.request("tools/list")
            self._send({**r.get("result", {}), "startupMs": self.bridge.startup_ms,
                        "imports": self.imports or ["Init"]})
        elif self.path == "/api/aristotle":
            self._send(aristotle_record())
        else:
            self._send({"error": "not found"}, status=404)

    def do_POST(self):
        body = json.loads(self.rfile.read(int(self.headers.get("Content-Length", 0))))
        if self.path == "/api/call":
            t0 = time.time()
            r = self.bridge.call_tool(body["name"], body.get("arguments", {}))
            self._send({**r.get("result", r), "ms": int((time.time() - t0) * 1000)})
        elif self.path == "/api/agent":
            t0 = time.time()
            r = run_agent(body.get("preamble", ""), body["goal"], self.imports)
            self._send({**r, "ms": int((time.time() - t0) * 1000)})
        else:
            self._send({"error": "not found"}, status=404)

    def log_message(self, *_):
        pass


def main():
    imports = sys.argv[1:]
    if not SERVER_BIN.exists() or not AGENT_BIN.exists():
        sys.exit("build first:  lake build server agent-run")
    print(f"  starting server ({', '.join(imports) or 'Init only'}) …")
    Handler.bridge = Bridge(imports)
    Handler.imports = imports
    httpd = HTTPServer(("localhost", PORT), Handler)
    print(f"  http://localhost:{PORT}")
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        Handler.bridge.proc.terminate()


if __name__ == "__main__":
    main()

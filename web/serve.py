#!/usr/bin/env python3
"""Single-purpose local UI for mined Mathlib statements.

    python3 web/serve.py

Then open http://localhost:8770
"""
import json
import os
import subprocess
import sys
import threading
from http.server import BaseHTTPRequestHandler, HTTPServer
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MINER_BIN = ROOT / ".lake" / "build" / "bin" / "miner-report"
PORT = int(os.environ.get("PORT", "8770"))


def lean_env():
    env = dict(os.environ)
    try:
        out = subprocess.run(
            ["lake", "env", "printenv", "LEAN_PATH"],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=120,
        )
        if out.returncode == 0 and out.stdout.strip():
            env["LEAN_PATH"] = out.stdout.strip()
    except (OSError, subprocess.SubprocessError) as e:
        sys.exit(f"could not resolve LEAN_PATH via lake: {e}")
    return env


class MineCache:
    def __init__(self):
        self.lock = threading.Lock()
        self.report = None
        self.index = 0

    def load(self):
        if self.report is not None:
            return self.report
        out = subprocess.run(
            [str(MINER_BIN), "--limit", "2", "--max-tier", "0", "--json"],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=300,
            env=lean_env(),
        )
        if out.returncode != 0:
            return {"error": out.stderr[-800:] or out.stdout[-800:] or "miner-report failed"}
        try:
            self.report = json.loads(out.stdout.strip().splitlines()[-1])
        except (IndexError, json.JSONDecodeError) as e:
            return {"error": f"could not parse miner-report JSON: {e}", "raw": out.stdout[-800:]}
        return self.report

    def next(self):
        with self.lock:
            report = self.load()
            if "error" in report:
                return report
            entries = report.get("entries", [])
            if not entries:
                return {"error": "miner report returned no entries"}
            item = entries[self.index % len(entries)]
            self.index += 1
            return {
                "index": self.index,
                "count": len(entries),
                "report": {k: report.get(k) for k in ["importMs", "total", "solved", "misses", "unusable"]},
                "entry": item,
            }


class Handler(BaseHTTPRequestHandler):
    mine_cache = MineCache()

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
        elif self.path == "/api/mine-next":
            self._send(self.mine_cache.next())
        else:
            self._send({"error": "not found"}, status=404)

    def log_message(self, *_):
        pass


def main():
    if not MINER_BIN.exists():
        sys.exit("build first:  lake build miner-report")
    httpd = HTTPServer(("localhost", PORT), Handler)
    print(f"  http://localhost:{PORT}")
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()

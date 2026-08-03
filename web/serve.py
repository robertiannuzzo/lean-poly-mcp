#!/usr/bin/env python3
"""Single-purpose local UI for mined Mathlib statements.

    python3 web/serve.py

Then open http://localhost:8770
"""
import json
import os
import re
import shutil
import subprocess
import sys
import tarfile
import threading
import time
import uuid
from urllib.parse import parse_qs, urlparse
from http.server import BaseHTTPRequestHandler, HTTPServer
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MINER_BIN = ROOT / ".lake" / "build" / "bin" / "miner-report"
JOB_ROOT = ROOT / ".aristotle" / "jobs"
CONJECTURE_ROOT = ROOT / ".aristotle" / "conjectures"
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
                "entry": {**item, "quality": score_candidate(item)},
            }

    def next_candidate(self):
        with self.lock:
            report = self.load()
            if "error" in report:
                return report
            entries = report.get("entries", [])
            if not entries:
                return {"error": "miner report returned no entries"}
            best = None
            start = self.index
            for offset in range(len(entries)):
                raw = entries[(start + offset) % len(entries)]
                quality = score_candidate(raw)
                outcome = (raw.get("verdict") or {}).get("outcome", "")
                enriched = {**raw, "quality": quality}
                if best is None or quality["score"] > best["entry"]["quality"]["score"]:
                    best = {
                        "index": ((start + offset) % len(entries)) + 1,
                        "count": len(entries),
                        "scanned": offset + 1,
                        "report": {k: report.get(k) for k in ["importMs", "total", "solved", "misses", "unusable"]},
                        "entry": enriched,
                    }
                if outcome == "interesting_miss" and quality["label"] in ["good", "maybe"]:
                    self.index = ((start + offset) % len(entries)) + 1
                    return best
            self.index = (start + len(entries)) % len(entries)
            if best is not None:
                best["noCandidate"] = True
                best["message"] = "No maybe/good Aristotle candidate found in this cached corpus; showing the highest-scoring entry."
                return best
            return {"error": "miner report returned no entries"}


def score_candidate(entry):
    name = entry.get("name", "")
    topic = entry.get("topic", "")
    statement = entry.get("statement", "")
    verdict = (entry.get("verdict") or {}).get("outcome", "")
    generated = entry.get("source") == "agentic_conjecture"
    reasons = []
    score = 0

    if generated:
        score += 35
        reasons.append("agentic conjecture; not known to be in Mathlib")
    elif verdict == "interesting_miss":
        score += 35
        reasons.append("local free tactics missed")
    else:
        score -= 40
        reasons.append("already solved locally")

    conceptual = ["Adjunction", "Equivalence", "Yoneda", "yoneda", "Limits", "Iso", "NatTrans"]
    if any(x in name for x in conceptual):
        score += 20
        reasons.append("conceptual CategoryTheory namespace")

    if topic in ["adjunctions", "equivalences", "yoneda", "limits", "natural transformations"]:
        score += 10
        reasons.append(f"topic: {topic}")

    length = len(statement)
    at_count = statement.count("@CategoryTheory")
    line_count = statement.count("\n") + 1
    internal = ["_proof_", ".eq_", "eq_1", "inst", "ofShape", "Accessible.Limits"]

    if length <= 1800:
        score += 20
        reasons.append("moderate statement length")
    elif length <= 5000:
        score += 5
        reasons.append("long but still inspectable")
    else:
        score -= 30
        reasons.append("statement is very large")

    if at_count <= 8:
        score += 15
        reasons.append("low explicit elaborator noise")
    elif at_count <= 30:
        score -= 5
        reasons.append("some explicit elaborator noise")
    else:
        score -= 25
        reasons.append("too many explicit @CategoryTheory terms")

    if line_count > 80:
        score -= 15
        reasons.append("too many rendered lines for a clean demo")

    if any(x in name for x in internal):
        score -= 25
        reasons.append("looks generated or implementation-heavy")

    score = max(0, min(100, score))
    label = "good" if score >= 70 else "maybe" if score >= 40 else "skip"
    return {"score": score, "label": label, "reasons": reasons}


class AgenticProposer:
    def __init__(self, mine_cache):
        self.mine_cache = mine_cache
        self.lock = threading.Lock()
        self.index = 0
        CONJECTURE_ROOT.mkdir(parents=True, exist_ok=True)

    def propose(self):
        with self.lock:
            report = self.mine_cache.load()
            if "error" in report:
                return report
            seeds = report.get("entries", [])
            if not seeds:
                return {"error": "miner report returned no entries"}
            template = PROPOSAL_TEMPLATES[self.index % len(PROPOSAL_TEMPLATES)]
            seed = seeds[self.index % len(seeds)]
            self.index += 1
            proposal_id = uuid.uuid4().hex[:12]
            proposal = {
                "id": proposal_id,
                "topic": template["topic"],
                "title": template["title"],
                "prose": template["prose"],
                "rationale": template["rationale"],
                "seed": {
                    "name": seed.get("name", ""),
                    "topic": seed.get("topic", ""),
                    "summary": seed.get("summary", ""),
                },
                "chain": [
                    {
                        "artifact": "open_need",
                        "status": "created",
                        "text": "Generate a category theory theorem candidate outside the mined-proof reconstruction path.",
                    },
                    {
                        "artifact": "seed_context",
                        "status": "attached",
                        "text": seed.get("name", ""),
                    },
                    {
                        "artifact": "proposal",
                        "status": "ready",
                        "text": template["prose"],
                    },
                    {
                        "artifact": "gate",
                        "status": "waiting",
                        "text": "Aristotle formalization requires an explicit click; proof submission requires a second explicit click.",
                    },
                ],
            }
            path = CONJECTURE_ROOT / proposal_id
            path.mkdir(parents=True, exist_ok=False)
            (path / "proposal.json").write_text(json.dumps(proposal, indent=2), encoding="utf-8")
            return {"proposal": proposal}

    def formalize(self, proposal):
        if not os.environ.get("ARISTOTLE_API_KEY"):
            return {"error": "ARISTOTLE_API_KEY is not set in the environment running web/serve.py"}
        proposal_id = proposal.get("id") or uuid.uuid4().hex[:12]
        path = CONJECTURE_ROOT / proposal_id
        path.mkdir(parents=True, exist_ok=True)
        prose = proposal.get("prose", "")
        input_file = path / "formalize.md"
        input_file.write_text(
            "# Category theory theorem proposal\n\n"
            "Translate the following prose theorem into one Lean 4 proposition using Mathlib.\n"
            "Return only the Lean statement after the colon, with no proof.\n\n"
            f"{prose}\n",
            encoding="utf-8",
        )
        out = subprocess.run(
            ["aristotle", "formalize", str(input_file)],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=180,
            env=os.environ.copy(),
        )
        (path / "formalize.stdout").write_text(out.stdout, encoding="utf-8")
        (path / "formalize.stderr").write_text(out.stderr, encoding="utf-8")
        if out.returncode != 0:
            return {"error": out.stderr[-1600:] or out.stdout[-1600:] or "aristotle formalize failed"}
        raw = (out.stdout + "\n" + out.stderr).strip()
        statement = parse_formalized_statement(raw)
        if not statement:
            return {"error": "could not parse Aristotle formalization", "raw": raw[-2000:]}
        well_formed = is_well_formed_statement(statement)
        entry = {
            "source": "agentic_conjecture",
            "kind": "conjecture",
            "name": f"AgenticConjecture.{proposal_id}",
            "topic": proposal.get("topic", "category theory"),
            "statement": statement,
            "summary": "generated conjecture; not known to be in Mathlib",
            "verdict": {
                "outcome": "interesting_miss" if well_formed else "unusable",
                "tried": [],
            },
            "proposal": proposal,
        }
        entry["quality"] = score_candidate(entry)
        record = {"proposal": proposal, "raw": raw, "wellFormed": well_formed, "entry": entry}
        (path / "formalization.json").write_text(json.dumps(record, indent=2), encoding="utf-8")
        return record


PROPOSAL_TEMPLATES = [
    {
        "topic": "isomorphisms",
        "title": "isomorphisms compose with reversed inverse",
        "prose": (
            "In any category, if f is an isomorphism from X to Y and g is an isomorphism "
            "from Y to Z, then the composite f followed by g is an isomorphism from X to Z, "
            "and its inverse is g inverse followed by f inverse."
        ),
        "rationale": "Tests a basic closure law and whether the prover finds existing category isomorphism API.",
    },
    {
        "topic": "natural transformations",
        "title": "componentwise isomorphism is stable under composition",
        "prose": (
            "For functors F, G, and H between two categories, if a natural transformation "
            "from F to G is componentwise an isomorphism and a natural transformation from "
            "G to H is componentwise an isomorphism, then their vertical composite is "
            "componentwise an isomorphism."
        ),
        "rationale": "Uses typed artifacts already visible in mined NatTrans statements but asks for a new formulation.",
    },
    {
        "topic": "adjunctions",
        "title": "left adjoints preserve colimits",
        "prose": (
            "Given an adjunction between two categories, the left adjoint preserves colimits "
            "of any fixed shape whenever those colimits exist."
        ),
        "rationale": "A conceptual category theory fact that should push Aristotle toward Mathlib's adjunction/limits API.",
    },
    {
        "topic": "yoneda",
        "title": "Yoneda reflects isomorphisms",
        "prose": (
            "In a locally small category, if the images of two objects under the Yoneda "
            "embedding are isomorphic, then the original objects are isomorphic."
        ),
        "rationale": "A compact representability-style theorem with a clear CategoryTheory target vocabulary.",
    },
]


def parse_formalized_statement(text):
    lines = []
    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith("```") or line.startswith("--"):
            continue
        lines.append(line)
    text = "\n".join(lines).strip()
    if text.startswith("#check"):
        text = text[len("#check"):].strip()
    elif text.startswith("example :"):
        text = text[len("example :"):].strip()
    elif text.startswith("theorem "):
        match = re.match(r"theorem\s+\S+\s*:\s*(.*)", text, flags=re.DOTALL)
        if match:
            text = match.group(1).strip()
    for suffix in [" := by sorry", " := sorry"]:
        if suffix in text:
            text = text.split(suffix, 1)[0].strip()
    return text


def is_well_formed_statement(statement):
    src = f"import Mathlib\n\nopen CategoryTheory\n\nexample : {statement} := by\n  sorry\n"
    out = subprocess.run(
        ["lake", "env", "lean", "--stdin"],
        input=src,
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
        env=lean_env(),
    )
    return out.returncode == 0


class AristotleJobs:
    def __init__(self):
        self.lock = threading.Lock()
        self.jobs = {}
        JOB_ROOT.mkdir(parents=True, exist_ok=True)

    def submit(self, entry):
        quality = score_candidate(entry)
        if quality["label"] == "skip":
            return {"error": "candidate quality is skip; choose a cleaner miss before spending Aristotle", "quality": quality}
        if not os.environ.get("ARISTOTLE_API_KEY"):
            return {"error": "ARISTOTLE_API_KEY is not set in the environment running web/serve.py", "quality": quality}

        local_id = uuid.uuid4().hex[:12]
        job_dir = JOB_ROOT / local_id
        job_dir.mkdir(parents=True, exist_ok=False)
        statement = entry.get("statement", "")
        goal_file = job_dir / "AristotleGoal.lean"
        goal_file.write_text(
            "import Mathlib\n\n"
            "open CategoryTheory\n\n"
            f"theorem cand : {statement} := by\n"
            "  sorry\n",
            encoding="utf-8",
        )
        for name in ["lean-toolchain", "lakefile.toml", "lake-manifest.json"]:
            source = ROOT / name
            if source.exists():
                shutil.copy2(source, job_dir / name)
        (job_dir / "entry.json").write_text(json.dumps({"entry": entry, "quality": quality}, indent=2), encoding="utf-8")

        prompt = (
            "Fill the sorry in AristotleGoal.lean. Do not change the theorem statement. "
            "Use Lean 4 and Mathlib only."
        )
        out = subprocess.run(
            ["aristotle", "submit", prompt, "--project-dir", str(job_dir)],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=120,
            env=os.environ.copy(),
        )
        (job_dir / "submit.stdout").write_text(out.stdout, encoding="utf-8")
        (job_dir / "submit.stderr").write_text(out.stderr, encoding="utf-8")
        if out.returncode != 0:
            return {"error": out.stderr[-1200:] or out.stdout[-1200:] or "aristotle submit failed", "quality": quality}

        raw_submit = (out.stdout + "\n" + out.stderr).strip()
        project_id = self.parse_project_id(raw_submit)
        if not project_id:
            return {"error": "could not parse Aristotle project id", "raw": raw_submit[-2000:], "quality": quality}

        record = {
            "localId": local_id,
            "projectId": project_id,
            "jobDir": str(job_dir),
            "submittedAt": int(time.time()),
            "entry": entry,
            "quality": quality,
        }
        (job_dir / "job.json").write_text(json.dumps(record, indent=2), encoding="utf-8")
        with self.lock:
            self.jobs[project_id] = record
        return record

    def status(self, project_id):
        record = self.jobs.get(project_id) or self.load_record(project_id)
        if not record:
            return {"error": f"unknown Aristotle project id: {project_id}"}
        out = subprocess.run(
            ["aristotle", "tasks", project_id, "--limit", "1"],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=60,
            env=os.environ.copy(),
        )
        if out.returncode != 0:
            return {**record, "status": "ERROR", "error": out.stderr[-1200:] or out.stdout[-1200:]}
        status = self.parse_status(out.stdout)
        response = {**record, "status": status, "rawStatus": out.stdout}
        if status in ["COMPLETE", "COMPLETED", "SUCCEEDED", "DONE"]:
            response.update(self.download(record))
        return response

    def download(self, record):
        archive = Path(record["jobDir"]) / "download.tar.gz"
        extract_dir = Path(record["jobDir"]) / "download"
        extract_dir.mkdir(exist_ok=True)
        out = subprocess.run(
            ["aristotle", "download", record["projectId"], "--destination", str(archive)],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=120,
            env=os.environ.copy(),
        )
        if out.returncode != 0:
            return {"downloadError": out.stderr[-1200:] or out.stdout[-1200:]}

        if archive.exists() and archive.stat().st_size > 0:
            try:
                self.extract_archive(archive, extract_dir)
            except (tarfile.TarError, OSError) as e:
                return {"downloadError": f"downloaded Aristotle archive, but could not extract it: {e}"}

        lean_files = [p for p in extract_dir.rglob("*.lean") if ".lake" not in p.parts]
        proof = ""
        proof_path = ""
        for path in lean_files:
            text = path.read_text(encoding="utf-8", errors="replace")
            if "theorem cand" in text or "sorry" not in text:
                proof = text
                proof_path = str(path)
                break
        summary = self.read_first(extract_dir, "ARISTOTLE_SUMMARY.md")
        readme = self.read_first(extract_dir, "README.md")
        files = [str(p.relative_to(extract_dir)) for p in extract_dir.rglob("*") if p.is_file()]
        return {
            "downloaded": True,
            "proofPath": proof_path,
            "proof": proof[:20000],
            "summary": summary[:8000],
            "readme": readme[:4000],
            "downloadFiles": files[:80],
        }

    @staticmethod
    def extract_archive(archive, extract_dir):
        with tarfile.open(archive, "r:*") as tar:
            for member in tar.getmembers():
                target = (extract_dir / member.name).resolve()
                if not str(target).startswith(str(extract_dir.resolve()) + os.sep):
                    raise tarfile.TarError(f"unsafe archive path: {member.name}")
            tar.extractall(extract_dir)

    @staticmethod
    def read_first(root, name):
        for path in root.rglob(name):
            if ".lake" not in path.parts:
                return path.read_text(encoding="utf-8", errors="replace")
        return ""

    def load_record(self, project_id):
        for path in JOB_ROOT.glob("*/job.json"):
            try:
                record = json.loads(path.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError):
                continue
            if record.get("projectId") == project_id:
                with self.lock:
                    self.jobs[project_id] = record
                return record
        return None

    @staticmethod
    def parse_project_id(text):
        for marker in ["Project created:", "Project ID:", "Project id:", "project_id:", "projectId:"]:
            if marker in text:
                candidate = text.split(marker, 1)[1].splitlines()[0].strip().strip('"').strip("'")
                candidate = candidate.replace(" ", "")
                if candidate:
                    return candidate
        match = re.search(r"\b[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}\b", text)
        return match.group(0) if match else ""

    @staticmethod
    def parse_status(text):
        rows = [line for line in text.splitlines() if line and not line.startswith("ID ") and not line.startswith("---")]
        if not rows:
            return "UNKNOWN"
        fields = rows[0].split()
        return fields[-1] if fields else "UNKNOWN"


class Handler(BaseHTTPRequestHandler):
    mine_cache = MineCache()
    agentic_proposer = AgenticProposer(mine_cache)
    aristotle_jobs = AristotleJobs()

    def _send(self, body, ctype="application/json", status=200):
        data = body if isinstance(body, bytes) else json.dumps(body).encode()
        self.send_response(status)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def do_GET(self):
        parsed = urlparse(self.path)
        if parsed.path == "/":
            self._send((Path(__file__).parent / "index.html").read_bytes(), "text/html")
        elif parsed.path == "/api/mine-next":
            self._send(self.mine_cache.next())
        elif parsed.path == "/api/find-candidate":
            self._send(self.mine_cache.next_candidate())
        elif parsed.path == "/api/propose-theorem":
            self._send(self.agentic_proposer.propose())
        elif parsed.path == "/api/aristotle-status":
            project_id = parse_qs(parsed.query).get("projectId", [""])[0]
            self._send(self.aristotle_jobs.status(project_id))
        else:
            self._send({"error": "not found"}, status=404)

    def do_POST(self):
        body = json.loads(self.rfile.read(int(self.headers.get("Content-Length", 0))))
        if self.path == "/api/aristotle-submit":
            self._send(self.aristotle_jobs.submit(body.get("entry", {})))
        elif self.path == "/api/aristotle-formalize":
            self._send(self.agentic_proposer.formalize(body.get("proposal", {})))
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

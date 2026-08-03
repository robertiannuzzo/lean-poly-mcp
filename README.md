# lean-poly-mcp

A Lean 4 project that treats an MCP tool interface as a polynomial functor, then uses
Lean's kernel as the trust boundary for proof-producing agents.

The current demo mines real `Mathlib.CategoryTheory` theorem statements, hides their
existing proofs, tries cheap local tactics, and optionally sends good misses to
Aristotle for proof reconstruction. Aristotle is useful, but never trusted directly:
anything it returns must elaborate locally, pass the axiom whitelist, and match the
requested statement.

## What this is

This project has three connected parts:

1. A small polynomial-functor kernel in Lean.
2. An MCP server whose tool registry is modeled as a coproduct of polynomial functors.
3. A proof oracle and demo workflow for category theory statements from Mathlib.

The practical question is:

> Can an agent or external prover work on real formal category theory while Lean remains
> the only trusted judge?

The answer this repo demonstrates is yes, for proof reconstruction tasks. It does not
claim to discover new mathematics.

## What it does not claim

The Mathlib miner is a benchmark generator, not a conjecture generator.

When the UI shows an `interesting miss`, that means:

> Mathlib already contains this theorem, but the local free tactic ladder did not
> reprove it cheaply from the statement alone.

It does not mean:

> The theorem was previously unknown or unproved.

The value of the workflow is that it produces real, checkable proof tasks from a large
formal library without spending model calls inventing random lemmas.

## Demo

For the clean local demo, double-click one of these from the repo root:

```text
Mathlib Statement Miner.app
Launch Mathlib Miner.command
```

Or run it manually:

```sh
lake build miner-report
python3 web/serve.py
```

Then open:

```text
http://localhost:8770
```

The first click imports Mathlib and builds the cached mining report, so it can take
roughly 60-120 seconds. Later clicks use the cached report.

The page does one thing: mine a real `Mathlib.CategoryTheory` statement and show whether
the local tactic ladder solved it or missed it. If a miss is scored as a good Aristotle
candidate, the UI can submit it explicitly, poll for status changes, and display the
downloaded Aristotle summary and Lean output.

There is also an experimental **Propose theorem** path. It adds a small local agentic
pre-chain inspired by typed discovery systems:

1. create an open need,
2. attach a mined Mathlib seed as context,
3. propose a category theory theorem in prose from a typed template,
4. wait at an explicit Aristotle gate.

From there, **Formalize with Aristotle** can translate the prose into a Lean statement.
If the statement parses locally, **Send to Aristotle** can submit the generated theorem
as a proof-filling job. This path is not a claim of novelty or truth; it is a controlled
way to create candidate conjectures with visible provenance and gates.

Tests and replay fixtures do not contact Aristotle. Live Aristotle calls happen only
when the UI submit button or a live Aristotle command is used deliberately.

## Quick Check

Build and run the compact local sweep:

```sh
lake build
./scripts/check.sh
```

Run the full Mathlib-backed sweep:

```sh
./scripts/check.sh --full
```

The full sweep imports Mathlib several times and is slower. It covers the Mathlib oracle
tests, the category theory miner, the benchmark, and the agent runs.

## MCP Smoke Test

The MCP server speaks JSON-RPC over stdio:

```sh
lake build server
printf '%s\n' \
  '{"jsonrpc":"2.0","id":1,"method":"tools/call","params":{"name":"check","arguments":{"source":"theorem cand : 2 + 2 = 4 := rfl"}}}' \
  | ./.lake/build/bin/server
```

The server prints startup lines, then a JSON-RPC response with this shape:

```json
{
  "content": [
    {
      "text": "... checked ... depends on no axioms ...",
      "type": "text"
    }
  ],
  "isError": false,
  "structuredContent": {
    "axioms": [],
    "outcome": "checked"
  }
}
```

The exposed MCP tools are:

| tool | purpose |
|---|---|
| `hello` | simple connectivity check |
| `check` | elaborate and audit a Lean candidate |
| `search` | run the local tactic ladder before escalation |

## How Mathlib Mining Works

The miner does not scrape source files and does not ask a language model for ideas.
It works inside Lean:

1. Import `Mathlib`.
2. Read Lean's elaborated environment.
3. Walk declarations whose names start with `CategoryTheory`.
4. Keep theorem-like declarations with usable types.
5. Pretty-print each declaration type as a Lean statement.
6. Group statements into slices such as functors, natural transformations, adjunctions,
   equivalences, Yoneda, limits, and isomorphisms.
7. Run the local tactic ladder through the same oracle used everywhere else.
8. Mark each candidate as `solved locally`, `interesting miss`, or unusable.
9. Score misses for Aristotle using local heuristics: topic, statement length,
   namespace signal, and elaborator noise.

The command-line report is:

```sh
lake exe miner-report --limit 2 --max-tier 0
```

JSON mode is what the web UI uses:

```sh
lake exe miner-report --limit 2 --max-tier 0 --json
```

## Agentic Theorem Proposal

The proposal path is the first step beyond proof reconstruction. It borrows a minimal
structure from self-revising discovery systems: every generated theorem proposal is an
artifact with provenance, an open need, a seed, a proposal, and a gate.

The current implementation is deliberately small and deterministic. It does not call a
general-purpose LLM to brainstorm. Instead, it rotates through category theory theorem
templates and attaches mined Mathlib context. Aristotle is used only after an explicit
click, first for prose-to-Lean formalization and then, optionally, for proof filling.

This keeps the spend boundary and trust boundary clean:

| stage | local or external | trusted? |
|---|---|---|
| propose theorem in prose | local | no, it is just a candidate |
| formalize prose to Lean | Aristotle | no, local parsing only checks shape |
| fill proof | Aristotle | no, output must be rechecked |
| verify proof | local Lean oracle | yes, subject to the stated axiom whitelist |

## Trust Model

Everything that produces a proof is untrusted. Lean is the judge.

The oracle has three gates:

1. **Elaboration:** Lean must accept the candidate.
2. **Axiom audit:** `Lean.collectAxioms` must be contained in the whitelist.
3. **Statement match:** the accepted theorem statement must match the requested one.

The axiom whitelist is:

```text
propext
Classical.choice
Quot.sound
```

This catches failures that string filters miss. For example, `sorry` elaborates but
depends on `sorryAx`, and `native_decide` can introduce compiler trust axioms. Those are
rejected by the axiom audit rather than by searching for banned words.

## Aristotle Integration

Aristotle has two roles:

| command | role |
|---|---|
| `formalize` | prose or LaTeX to a Lean statement |
| `submit` | fill `sorry`s in a Lean project |

The demo currently emphasizes `submit`: mine a known Mathlib theorem statement, create
a small Lean project with `theorem cand : ... := by sorry`, submit it to Aristotle, poll
the job, download the result, and display the summary and Lean file.

Downloaded Aristotle output is not evidence until it is rechecked locally by the oracle.
Replay fixtures cover Aristotle paths offline so normal tests do not spend credits or
depend on network availability.

## Architecture

The core dictionary is:

| polynomial structure | system meaning |
|---|---|
| positions | requests |
| directions | valid responses for a request |
| section `Lens p y` | server implementation |
| coproduct `Poly.sigma` | tool registry |
| composite with a stateful lens | one agent step |
| completed pair `Sigma i, p.Dir i` | completed tool call |

Two Lean facts carry the main interpretation:

```lean
Lens p y        ~=  ((i : p.Pos) -> p.Dir i)
Lens (S y^S) y  ~=  (S -> S)
```

In prose: a server is a section of its interface, and an agent composed with a server is
a state transition.

The project deliberately keeps the elegant model and the running transport connected:
the live MCP server dispatch follows the same typed interface that the polynomial model
describes, then flattens to JSON only at the wire boundary.

## Toolchain

The Lean and Mathlib versions are pinned to Aristotle's current target:

```text
leanprover/lean4:v4.28.0
mathlib 8f9d9cff6bd728b17a24e163c9402775d9e6a365
```

Do not bump these casually. The trust story depends on rechecking Aristotle output
against the same Lean and Mathlib versions used to produce it. If the versions drift, a
failed verification becomes ambiguous: the proof might be wrong, or the library might
simply have changed.

Setup:

```sh
brew install elan-init
lake update
lake exe cache get
lake build
./scripts/check.sh --full
```

## Repository Layout

```text
Poly/         polynomial functor kernel: objects, lenses, products, sums, composition
Mcp/          MCP interface, tool registry, server section, JSON-RPC transport
Oracle/       in-process Lean elaboration, axiom audit, statement matching
Tactics/      local proof-search ladder
Formalize/    Mathlib category theory miner and benchmark reports
Agent/        agent as a lens-driven runtime
Aristotle/    Aristotle client plus offline replay fixtures
web/          local demo UI and server
test/         Lean tests and replay tests
docs/         longer design notes and paper-style explanation
v1-idris/     Idris2 predecessor, preserved for comparison
```

## Further Reading

- [`docs/paper-style-explanation.md`](docs/paper-style-explanation.md) gives the longer
  research narrative.
- [`docs/lean-upgrade-plan.md`](docs/lean-upgrade-plan.md) records the implementation
  phases and design history.
- [`v1-idris/`](v1-idris/) contains the predecessor system.

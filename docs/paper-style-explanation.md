# Paper-Style Explanation

This note is the longer narrative behind `lean-poly-mcp`. The README is optimized for a
first-time reader and a live demo; this file keeps the deeper argument and the current
end-to-end workflow in one place.

## Abstract

An MCP interface can be modeled as a polynomial functor: positions are requests and
directions are the responses available for each request. A server is a section of that
interface. A stateful agent is a lens whose interaction with the server induces a state
transition.

This repository implements that idea in Lean 4 and connects it to a proof workflow for
category theory. The system mines theorem statements from Mathlib's `CategoryTheory`
namespace, tries cheap local tactics, scores selected misses for escalation, and can
send proof-filling jobs to Aristotle. A second path proposes theorem candidates in
prose, optionally with a cheap language-model proposer, asks Aristotle to formalize the
prose into Lean, and then routes locally parseable statements into the same proof-filling
pipeline.

The trust boundary is deliberately narrow: Lean's kernel is the only trusted component.
Every accepted proof must elaborate locally, pass an axiom whitelist, and, when a target
statement is supplied, match that requested statement.

## Core Idea

In `Poly`, an object is written informally as:

```text
p = Sigma (i : p.Pos), y ^ p.Dir i
```

The interpretation used by the project is:

| `Poly` | system |
|---|---|
| `p.Pos` | requests |
| `p.Dir i` | possible responses to request `i` |
| `Lens p y` | a server, choosing a response for each request |
| `Poly.sigma toolPoly` | the MCP tool registry |
| `Lens (S y^S) MCP` | an agent with internal state |
| `Sigma i, p.Dir i` | a completed request-response pair |

The two most important checked equivalences are:

```lean
Lens p y        ~=  ((i : p.Pos) -> p.Dir i)
Lens (S y^S) y  ~=  (S -> S)
```

So the operational reading is simple: a server is a section, and an agent interacting
with a server produces a state transition.

## Why Lean

The Idris2 predecessor in `v1-idris/` demonstrated the same container idea, but it had
three structural limitations.

First, the proof checker had to run as a subprocess. Lean exposes its elaborator and
environment through `import Lean`, so candidates can be checked in-process against an
environment imported once.

Second, v1's soundness gate was a blacklist of suspicious strings. Lean lets this
project audit the accepted proof term with `Lean.collectAxioms`, which is a semantic
check on what the term actually depends on.

Third, Mathlib gives the project a large target vocabulary. In particular,
`Mathlib.CategoryTheory` provides real theorem statements rather than synthetic examples.

## The Oracle

The oracle accepts a candidate only after three checks:

1. The candidate elaborates.
2. Its collected axioms are contained in `{propext, Classical.choice, Quot.sound}`.
3. Its statement matches the requested statement, when a requested statement is supplied.

This is stronger than checking that Lean emitted no errors. For example, `sorry` can
elaborate while adding `sorryAx`, and `native_decide` can introduce trust axioms. Those
are rejected because the final proof term depends on disallowed axioms.

The statement-matching gate matters just as much. A prover can produce a true theorem
that is not the theorem requested. That is not a soundness failure in Lean, but it is a
workflow failure for autoformalization or proof filling. The oracle catches that by
checking whether the accepted declaration inhabits the requested proposition, not by
string-comparing theorem text.

## Mathlib Mining

The category theory miner works from Lean's elaborated environment:

1. Import `Mathlib`.
2. Scan declarations under `CategoryTheory`.
3. Select theorem-like declarations.
4. Pretty-print their types as Lean statements.
5. Reparse candidate statements under the project preamble.
6. Run the local tactic ladder through the same oracle used everywhere else.
7. Report local wins, interesting misses, and unusable statements.

The miner therefore uses Mathlib as a ground-truth corpus. It is not proving new
theorems. It is producing proof reconstruction tasks whose original proofs are known to
exist but are hidden from the local search and from Aristotle submissions.

That distinction is important. An interesting miss means the local ladder could not
recover the proof cheaply. It does not mean the theorem was unknown.

## Local Tactic Ladder

The local ladder is intentionally small. It tries tactics such as `rfl`, `trivial`,
`simp`, `aesop_cat`, `decide`, `omega`, `simp_all`, `aesop`, and `exact?`.

Technically, each rung is turned into a complete Lean declaration:

```lean
theorem cand : <goal> := by
  <tactic>
```

Lean elaborates that declaration. If the tactic closes the goal, Lean produces a proof
term, and the oracle audits that theorem exactly as it would audit Aristotle output. The
tactic layer therefore has no special trust. It is only a cheap proof generator.

Keeping the ladder small is a demo choice. It makes the boundary clear:

```text
cheap local reasoning -> interesting miss -> optional Aristotle escalation
```

Adding more tactics is mechanically easy, but it would change what the benchmark means.
A very aggressive local search could reduce misses while making it less clear which
statements are genuinely good escalation candidates.

## Candidate Scoring

Lean decides the formal status of each mined statement: solved locally, interesting
miss, or unusable. The Python UI server then assigns a demo-quality score.

That score is not a mathematical claim. It is a heuristic for choosing useful Aristotle
candidates. It rewards things like:

- local tactics missed,
- conceptual namespaces such as adjunctions, equivalences, Yoneda, limits, isomorphisms,
  and natural transformations,
- preferred topics for the demo,
- moderate statement length,
- low explicit elaborator noise.

It penalizes things like:

- statements that do not parse locally,
- statements already solved locally,
- very long statements,
- large amounts of explicit `@CategoryTheory` output,
- names that look generated or implementation-heavy.

The labels are `good`, `maybe`, and `skip`. They are produced by Python, not Lean.

## Aristotle Boundary

Aristotle is integrated as an external, untrusted prover service.

For proof filling, the project creates a small Lean project containing:

```lean
import Mathlib

open CategoryTheory

theorem cand : <statement> := by
  sorry
```

The submission is job-based. The UI receives a project id, polls for status changes,
downloads the completed artifact, and displays Aristotle's summary and Lean output.

The artifact is still only a proposal. The intended final step is local verification by
the oracle, which checks elaboration, axioms, and statement equality under the pinned
Lean and Mathlib versions.

## Agentic Proposal Path

The current demo has a second path beyond mining known Mathlib statements.

`Propose theorem` creates a small artifact chain:

1. an open need,
2. a mined Mathlib seed as context,
3. a prose theorem proposal,
4. an explicit Aristotle formalization gate.

By default, the proposal comes from local deterministic templates. This keeps the demo
predictable and avoids spending model calls just to create a candidate.

Optionally, the proposal stage can call a cheap OpenAI or Anthropic model. In the OpenAI
path, the Python server uses the Responses API with:

```text
instructions = system prompt
input        = mined seed, seed result, statement excerpt, and fallback example
output       = strict JSON: title, topic, prose, rationale
```

The model is not asked to produce Lean and is not trusted. It only proposes prose. If the
configured provider fails or is missing credentials, the UI records the failure and
falls back to the local template.

From there, `Formalize with Aristotle` sends the prose theorem to Aristotle's
formalization command. The server extracts a Lean proposition from the returned artifact,
checks that the proposition parses locally, and displays it as a generated conjecture.
Only after that can the user explicitly submit the formalized statement for proof
filling.

This path is not a claim of novelty or truth. It is a controlled way to produce
candidate conjectures with visible provenance and explicit gates.

## Local Web App

The demo UI is intentionally small. The frontend is a single plain HTML/CSS/JavaScript
file, `web/index.html`, with MathJax for rendering proposal prose. There is no React,
Vite, Next.js, or frontend build step.

The local server is `web/serve.py`, a Python standard-library HTTP server. It serves the
HTML page and provides JSON endpoints for:

- returning the next mined statement,
- scanning for a better Aristotle candidate,
- proposing a theorem,
- asking Aristotle to formalize prose,
- submitting a proof-filling job,
- polling Aristotle status and reading returned artifacts.

The server is glue. Lean performs mining, local tactic search, and verification.
Aristotle and optional language models are external proposers. The frontend displays the
current artifact state and requires explicit clicks before spending external resources.

## Toolchain Pin

The project is pinned to:

```text
leanprover/lean4:v4.28.0
mathlib 8f9d9cff6bd728b17a24e163c9402775d9e6a365
```

This is deliberate. If Aristotle proves against one Mathlib version and the local oracle
checks against another, failures become ambiguous. A version mismatch can look like a bad
proof even when the only problem is library drift.

## What Is Novel Here

The project does not claim novelty for polynomial functors, containers, interaction
structures, lenses as dynamical systems, category theory statements mined from Mathlib,
or external theorem proving.

The contribution is the working integration:

- an MCP tool interface modeled as a polynomial functor,
- a live server shaped by that model,
- an in-process Lean kernel oracle,
- a Mathlib category theory miner,
- a local tactic baseline,
- a Python demo server that exposes the workflow,
- a prose theorem proposal path with optional cheap model support,
- Aristotle formalization and proof-filling gates,
- and an explicit trust boundary around all remote generation.

The practical result is a demoable system where agentic proof work can happen while the
trusted claim remains local and kernel-checked.

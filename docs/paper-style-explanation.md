# Paper-Style Explanation

This note is the longer narrative behind `lean-poly-mcp`. The README is now optimized
for a first-time reader and a live demo; this file keeps the deeper argument in one
place.

## Abstract

An MCP interface can be modeled as a polynomial functor: positions are requests and
directions are the responses available for each request. A server is a section of that
interface. A stateful agent is a lens whose interaction with the server induces a state
transition.

This repository implements that idea in Lean 4 and connects it to a proof workflow for
category theory. The system mines theorem statements from Mathlib's `CategoryTheory`
namespace, tries local tactics, and escalates selected misses to Aristotle. The only
trusted component is Lean's kernel: every candidate proof must elaborate, pass an axiom
whitelist, and match the requested statement.

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
3. Its statement matches the requested statement.

This is stronger than checking that Lean emitted no errors. For example, `sorry` can
elaborate while adding `sorryAx`, and `native_decide` can introduce trust axioms. Those
are rejected because the final proof term depends on disallowed axioms.

The statement-matching gate matters just as much. A prover can produce a true theorem
that is not the theorem requested. That is not a soundness failure in Lean, but it is a
workflow failure for autoformalization or proof filling.

## Mathlib Mining

The category theory miner works from Lean's elaborated environment:

1. Import `Mathlib`.
2. Scan declarations under `CategoryTheory`.
3. Select theorem-like declarations.
4. Pretty-print their types as Lean statements.
5. Reparse candidate statements through the oracle preamble.
6. Run a local tactic ladder.
7. Report local wins and local misses.

The miner therefore uses Mathlib as a ground-truth corpus. It is not proving new
theorems. It is producing proof reconstruction tasks whose original proofs are known to
exist but are hidden from the local search and from Aristotle submissions.

That distinction is important. An interesting miss means the local ladder could not
recover the proof cheaply. It does not mean the theorem was unknown.

## Escalation Ladder

The local ladder tries cheap tactics first. These include tactics such as `rfl`,
`trivial`, `simp`, `aesop_cat`, `decide`, and arithmetic tactics where appropriate.

This gives a budget boundary: Aristotle is reserved for statements that are already
known to be well-formed and not solved by the free local layer. The UI scores candidates
using local features such as topic, statement length, namespace signal, and pretty-print
noise.

## Aristotle Boundary

Aristotle is integrated as an external, untrusted prover service.

For proof filling, the project creates a small Lean project containing:

```lean
import Mathlib

open CategoryTheory

theorem cand : <mined statement> := by
  sorry
```

The submission is job-based. The UI receives a project id, polls for status changes,
downloads the completed artifact, and displays Aristotle's summary and Lean output.

The artifact is still only a proposal. The intended final step is local verification by
the oracle, which checks elaboration, axioms, and statement equality under the pinned
Lean and Mathlib versions.

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
structures, or lenses as dynamical systems. Those are established ideas.

The contribution is the working integration:

- an MCP tool interface modeled as a polynomial functor,
- a live server shaped by that model,
- an in-process Lean kernel oracle,
- a Mathlib category theory miner,
- a local tactic baseline,
- and an explicit boundary around remote proof generation.

The practical result is a demoable system where agentic proof work can happen while the
trusted claim remains local and kernel-checked.

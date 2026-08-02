# lean-poly-mcp — design and plan

**Status: Phases 1–3 built and machine-checked. Phases 4–8 planned.**
Revised 2026-08-01 for the Aristotle-only architecture. Supersedes the original
`idris-mcp` upgrade plan.

Seven requirements:

1. convert the project to Lean
2. focus the autoformalization on category theory
3. involve containers, using Poly as the structure of tool calls
4. demonstrate agentic AI
5. invoke the Aristotle API
6. build a front end
7. demonstrate understanding of Lean tactics

These are not seven features. §1 is the single idea that makes them one project;
everything after it is execution.

---

## 1. The organizing idea

In **Poly** — the category of polynomial functors, equivalently containers in the sense
of Abbott–Altenkirch–Ghani — an object is

```
p  =  Σ_{i : p.Pos}  y ^ p.Dir i
```

Positions are requests; directions are the responses that request admits. An MCP
interface *is* this. Once you say so, the rest of the system follows from the algebra
instead of being designed separately:

| Poly concept | What it is here |
|---|---|
| a lens `p → y` | **the server** — a section, `(i : p.Pos) → p.Dir i` |
| a lens `y → p` | **a request**, only — the backward map lands in `1`, so no response rides along |
| `Σ (i : p.Pos), p.Dir i` | **one completed tool call** — request plus its response; *not* a hom-set |
| a lens `S y^S → p` | **the agent** — a Moore machine |
| the composite `S y^S → p → y` | **one round-trip**, which is exactly a state transition `S → S` |
| coproduct `⊕'` | **the tool registry** — adding a family of tools is a coproduct |
| composition `◁` | **a two-step protocol** |
| cofree comonoid `𝒞_p` | **the space of all sessions**; one run is a path through it |
| `p` for the tactic engine | positions = proof states, directions = tactic outcomes (Hancock–Setzer) |

That last row is what earns requirement 7. Lean's tactic engine is itself an interaction
structure — a polynomial — so proof search is an agent, a lens `S y^S → p_tactic`.
"Demonstrate tactics" and "demonstrate agentic AI" are the same demo at two altitudes.

Three facts license the table, all proved in `Poly/Basic.lean`, all **axiom-free**:

```lean
sectionEquiv : Lens p y        ≃ ((i : p.Pos) → p.Dir i)   -- sections are servers
step/step_eq : Lens (S y^S) y  ≃ (S → S)                   -- agent ∘ server is a transition
posEquiv     : Lens y p        ≃ p.Pos                     -- a lens out of y is a request
```

### Correction log

Kept deliberately, because §10 is about distinguishing what is checked from what merely
sounds right — and that discipline is worthless if this document quietly launders its
own mistakes.

- **An earlier draft claimed `Lens y p ≃ Σ i, p.Dir i`** ("elements of Poly are tool
  calls"). False: the backward map of a lens out of `y` lands in `y.Dir = 1` and carries
  no response. `posEquiv` now proves the true statement, and the "completed tool call"
  type is the pair type, which is not a hom-set at all. The replacement — `Lens (S y^S) y
  ≃ (S → S)` — is stronger, and does the work the false claim was reaching for.
- **An earlier draft budgeted for `leanprover-community/repl`** with pickled Mathlib
  environments to make verification tractable. Unnecessary — see §4.
- **An earlier draft said `sinhp/Poly` could not be a dependency.** That was true at the
  toolchain we had then, and is false at the one we are moving to — see §3.

---

## 2. Aristotle is the only external service

**Decision: no Anthropic API key, no LLM in the loop.** Aristotle covers both halves we
would otherwise have needed a model for — `aristotle formalize` (English/LaTeX → Lean
statement) and `aristotle submit` (fill `sorry`s). One vendor, one key, one failure mode.

### Why this is a simplification, not a compromise

**`sorry` is exactly the right interface.** Aristotle's contract is "hand me a file with
`sorry`s and I'll fill them." Our Phase 3 oracle already audits axioms with
`Lean.collectAxioms` — so **`sorryAx` absent is literally "Aristotle honoured its
contract."** The soundness gate and the completion check are the same check.

**The trust boundary gets crisper.** Aristotle is purely the untrusted proposer; we are
purely the verifier and orchestrator. Nothing blurs the line.

**Statement matching matters more, and we have it.** `formalize` performs the
English→Lean step, which is precisely where misformalization lives. The two-probe check
(§4) is aimed at exactly that.

### The agent is still agentic

Removing the LLM appears to remove the agent. It does not — it relocates the decision
from a prompt into a verified policy. The agent's job is choosing where to spend on an
escalation ladder:

```
tier 0   rfl / simp / aesop_cat            free, milliseconds, local
tier 1   exact? / apply? library search    free, seconds, local
tier 2   Aristotle                         paid, minutes to hours
```

That is autonomous, multi-step, feedback-driven tool use — and the agent remains a
`Lens (S y^S) MCP` **written in Lean**, not an external client. This is strictly the best
outcome for requirements 3 and 4 together, and it fuses 4 with 7: the ladder *is* the
tactics demo.

**Stated honestly:** if "agentic AI" is read as "an LLM makes the decisions", this design
puts the decisions in a Lean policy and calls an AI system (Aristotle) as a tool. That is
a shift in interpretation and should be presented as one. Adding a second proposer later
is `⊕'` on the interface — no redesign.

### What this removes

`ANTHROPIC_API_KEY`; the LLM proposer and its system prompt; the bounded repair loop;
v1's `paraphrase` disclosure hack (statement matching supersedes it); one of the two
cost-cap regimes in `CLAUDE.md`.

---

## 3. Toolchain: pin to Aristotle's

Aristotle runs on fixed versions:

```
lean-toolchain   leanprover/lean4:v4.28.0
mathlib          8f9d9cff6bd728b17a24e163c9402775d9e6a365   (= tag v4.28.0, 2026-02-16)
```

We are currently on `v4.33.0-rc1` with Mathlib pinned to `master` — **4980 commits
ahead** of Aristotle's. Both are wrong, for reasons beyond compatibility warnings:

**The trust story requires it.** Phase 5's discipline is *never trust Aristotle's claim of
verification — re-check it locally*. That only works if both sides speak the same Mathlib.
Under version skew, a failed re-verification is ambiguous: unsound, or a lemma renamed
across 4980 commits? An ambiguous verdict from the oracle destroys the thing the oracle
exists to provide. Handing Aristotle a separate pinned subproject does not help — it moves
the skew into the one place we cannot afford it.

**We are on a release candidate.** Nobody pins an rc. Moving to `v4.28.0` also gets
Mathlib off `master`, which is a moving target and bad for reproducibility regardless.

**It makes `sinhp/Poly` usable.** Poly pins `v4.28.0-rc1` — the same release line. The
toolchain Harmonic requires and the toolchain the serious Poly formalization targets are
the same one. Keep the vendored kernel as the thing the server compiles against (small,
readable, no version risk), and add `sinhp/Poly` as an optional comparison rather than
writing it off.

**Risk to verify by trying:** the oracle depends on `Lean.Elab.process`'s signature and on
`importModules (loadExts := true)`. `loadExts` is load-bearing — without it the
environment cannot parse `n + 0`. If it is absent at 4.28 there is another route, but this
is the item most likely to bite. `collectAxioms` and `enableInitializersExecution` are
long-standing and safe. Cost is one-time and unattended: a toolchain download and a fresh
Mathlib olean cache.

---

## 4. What is built (Phases 1–3)

### Poly kernel — `Poly/`

Objects, dependent lenses, `⊕' × ⊗ ◁`, sections, agents, traces. Deliberately
Mathlib-free: **typechecks standalone in 1.7s**. The category laws hold by `rfl`, so no
coherence bookkeeping leaks into anything above.

`#print axioms` on every result: *"does not depend on any axioms"* — stronger than the
whitelist requires.

`Poly/Kleisli.lean` names the one place the pure statement stops being exact: a handler
that runs the elaborator is `(i : p.Pos) → IO (p.Dir i)`, which is **not** a `Lens p y` —
it is a section in the Kleisli category of `IO`. Given a name and a file rather than a
footnote, because `Lens p y` would otherwise quietly overclaim.

### MCP server — `Mcp/`

`Method` as positions, `ResultOf` as directions, the server as a section. Transport is
newline-delimited JSON-RPC on `Lean.JsonRpc` — deliberately *not* LSP framing, which
prefixes `Content-Length` headers MCP does not use. v1's hand-written 181-line
`JSONRPC.idr` has no counterpart.

The structural fix from v1 holds: `Mcp.respond` answers live requests by projecting the
lens through `sectionEquiv`, and `dispatch_eq_handle` proves that equals the handler by
`rfl`. One source of truth, no runtime cost. In v1 the dependent-lens model and the
program that ran were two different artifacts.

With the oracle added, `MCP` became a genuine coproduct:

```lean
abbrev MCP : Poly := PureMCP ⊕' OracleMCP
```

which is what lets the pure claim survive intact on the summand where it is true, instead
of being weakened everywhere. The coproduct is load-bearing here, not decorative.

Verified end to end against the compiled binary: initialize, tools/list, tools/call,
unknown tool (`isError`, not a protocol error), malformed params (`-32602`), unknown
method (`-32601`), notification producing no response. v1's Python GUI drives the Lean
binary **unchanged**.

### Oracle — `Oracle/`

Three gates: elaborate → audit axioms → match statement.

Elaboration is **in-process** via `Lean.Elab.process`, against an environment imported
once at startup:

```
[64588 ms] import Mathlib (ONCE, at startup)
   [138 ms] identity is a left unit for ≫          → checked [propext]
    [17 ms] iso hom ≫ inv = id, statement matched  → checked [propext]
    [24 ms] functors preserve retractions          → checked []
     [4 ms] ATTACK: sorry in a Mathlib proof       → unsoundAxioms [sorryAx]
```

No subprocess, no IPC, no external REPL. Two results worth recording:

- **`sorry` is only a warning** to the elaborator, so it passes gate 1 cleanly. It is
  caught solely by the audit — a system gating on "did it compile" accepts it.
- **`native_decide` mints a per-declaration axiom** (`cand._native.native_decide.ax_1`)
  whose name varies with the declaration. A name-based gate would need a name it cannot
  know in advance. Nothing in `Oracle/Kernel.lean` mentions `native_decide`. This is the
  concrete argument for auditing over v1's substring blacklist.

Statement matching is **two probes, not one**: first, is the requested statement
well-formed here; only then, does the candidate inhabit it. Found by hitting it — the
first implementation reported `statementMismatch` on a *correct* Mathlib proof because
`open CategoryTheory in` does not scope across `process` calls. Conflating a harness bug
with "the prover proved the wrong thing" is exactly the false confidence this module
exists to prevent, hence `badStatement` as a distinct outcome and `Request.preamble`.

v1's live failure is now caught rather than disclosed: asked for `∀ n, n = n + 1` and
given a proof of its negation, the oracle returns `statementMismatch` with the type
mismatch verbatim.

---

## 5. Phase 4 — tools, not methods

`check` is currently a top-level JSON-RPC method, following v1. **That is wrong for any
standards-compliant MCP client**, which discovers only `tools/list` and calls
`tools/call` — it never sees a custom method. v1's design quietly locked it to a
hand-written client.

Move the oracle surface into `tools`:

| tool | does |
|---|---|
| `check` | verify a declaration: elaborate, audit, match |
| `search` | run the free tactic ladder (tier 0/1) |
| `aristotle_submit` / `aristotle_status` / `aristotle_fetch` | the paid tier, job-based |

The registry is already `⊕'`, so this is adding a summand rather than editing an
inductive type. Drop `hello`.

---

## 6. Phase 5 — Aristotle

Client via the `aristotle` CLI shelled out from Lean (`IO.Process`), so the vendor SDK is
the only non-Lean dependency. `ARISTOTLE_API_KEY`.

**Never blocking.** Published runtimes reach ~8 hours. `aristotle_submit` returns a job
handle; `status`/`fetch` poll. In Poly terms the submit position's direction is a *job
handle*, not a proof — a clean illustration of why the direction type depends on the
position.

**Always re-verified.** Aristotle's output goes through the Phase 3 oracle before it is
ever labelled `checked`. The vendor's assertion of verification is an input, not evidence.

**We submit our own project.** Because the toolchain matches, Aristotle sees
`Poly/Basic.lean` — so it can prove theorems *about our own kernel*, which is what makes
Tier 2 below real rather than aspirational.

**Mandatory in code, not by convention:** hard attempt cap; `--replay` mode backed by
cached job outputs so demos and tests never hit the network; no retry-on-timeout without
a ceiling.

---

## 7. Phase 6 — category theory, graded

The benchmark doubles as the eval harness.

- **Tier 0** — identity and associativity laws, functors preserve isomorphisms,
  naturality squares. Mostly `aesop_cat`; expected to need no network at all.
- **Tier 1** — Yoneda-adjacent statements, universal properties, triangle identities.
- **Tier 2** — statements about **`Poly` itself**: `Lens` composition is associative, `◁`
  is monoidal with unit `y`, `sectionEquiv`. The system proves theorems about the
  structure it is built from, verified by its own kernel.

**How far tier 0/1 gets with no network is itself a result worth reporting** — it bounds
what the paid tier is actually for.

---

## 8. Phase 7 — tactics

Four levels, so the understanding is shown rather than claimed:

1. **Use them well** — `ext`, `funext`, `aesop_cat`, a curated `@[simp]` set on `Lens`.
2. **Write one** — `poly_ext`, reducing a `Lens` equality to `onPos`/`onDir` goals and
   handling the dependent `HEq` obligation. (Note: `sectionEquiv`/`posEquiv` closed by
   `rfl` thanks to `PUnit` eta, so this is needed for the harder lemmas, not the ones
   already done.)
3. **Expose them** — `tactic/state` and `tactic/apply`, making the tactic engine a
   polynomial the agent drives.
4. **Fail informatively** — `docs/tactic-notes.lean`: where `simp` loops, why
   `native_decide` is excluded from the whitelist, what `decide` cannot close.

---

## 9. Phases 8–9 — the agent, and the front end

The agent is `Lens (S y^S) MCP`, defined in Lean, executing the escalation ladder from §2.
Every step is a node in the session tree — a path in `𝒞_MCP` — which is the front end's
data model, so the front end is not decoration either.

Four panels, one self-contained page (no build step, no CDN — reviewable, and shareable
as an artifact):

1. **Polynomial explorer** — positions and directions of the live server; adding tools
   visibly changes the coproduct.
2. **Session tree** — the run as a path through `𝒞_p`, with abandoned tier-0/1 branches
   greyed. The picture that makes the categorical story legible without reading Lean.
3. **Proof panel** — statement, term, **axiom set**, match result, and which tier solved
   it. The axiom list is the trust story; keep it prominent.
4. **Aristotle queue** — jobs, elapsed time, and local re-verification shown *separately*
   from Harmonic's own claim.

---

## 10. What is claimed, and what is not

Stated precisely, because the distinction is the point of the project.

**Kernel-checked:**
- The MCP interface is a polynomial functor; the server is a section of it; exhaustiveness
  and result-shape correctness are kernel facts.
- Every accepted proof elaborates and depends only on
  `{propext, Classical.choice, Quot.sound}` — with the axiom list shown.
- The proved statement is α-equivalent to the statement requested.

**Design discipline, not theorem:**
- The agent policy is a Lean value that the runtime executes. There is no mechanized
  bridge from the Lean semantics to the compiled binary's IO behaviour.

**Not claimed:**
- That an **English** prompt was proven. Formalization is unverified in principle, and
  `aristotle formalize` performing that step is exactly why statement matching exists.
- Novelty for the theory. Containers ≅ polynomial functors (Abbott–Altenkirch–Ghani),
  interaction structures (Hancock–Setzer), and systems as lenses (Niu–Spivak) are
  established. The contribution is a working system built on them.

**Where Poly is currently doing least work:** at Phase 2, with one tool, the job was done
by `ResultOf : Method → Type` — obtainable without ever saying "polynomial functor". It
starts earning its place in Phases 4–9, where the registry (`⊕'`), multi-step protocols
(`◁`), the session log (`𝒞_p`), and the tactic engine all come from one algebra rather
than four ad-hoc designs. If by Phase 9 it still is not carrying weight, the right move is
to say so, not to dress it up.

---

## 11. Risks

| risk | mitigation |
|---|---|
| `loadExts` / `Lean.Elab.process` differ at v4.28 | Verify by building; the oracle is 250 lines and easy to adapt |
| Aristotle latency (~8h worst case) | Job-based, never blocking; `--replay` for demos and tests |
| Aristotle cost, unknown rate limits | Hard caps in code; tiers 0/1 free and local; decide a spend ceiling before Phase 5 |
| Mathlib 5.5 months behind current | Accepted deliberately — see §3 |
| Context/session cost while building | `CLAUDE.md` rules; `./scripts/check.sh`; fresh session per phase |

---

## 12. Order

**4** (tools not methods) → **3′** (toolchain downgrade + full re-verification) → **6/7**
(benchmark and tactics together — Tier 2 *is* the Poly proof set) → **8** (agent) → **5**
(Aristotle, whenever the key exists) → **9** (front end).

The toolchain move should happen early, before there is more code to revalidate. Aristotle
stays off the critical path as long as possible: it is the most externally blocked item,
and tiers 0/1 make the system demonstrable without it.

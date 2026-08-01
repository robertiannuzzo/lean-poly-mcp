# Upgrade plan: `idris-mcp` → a Lean 4 / Poly autoformalization system

Status: **plan only, nothing implemented.** Written 2026-07-31.

Seven requirements, in the user's words:

1. convert this project to Lean
2. focus the autoformalization part on category theory
3. involve containers, using **elements of Poly as tool calls**
4. demonstrate agentic AI
5. invoke the Aristotle API
6. build a front end
7. demonstrate understanding of Lean tactics

The good news: these are not seven separate features bolted together. There is one
idea that makes all seven the same project, and §1 is that idea. Everything after it
is execution.

---

## 1. The organizing idea

In **Poly** (the category of polynomial functors / containers), an object is

```
p  =  Σ_{i : p.Pos}  y ^ p.Dir i
```

Positions are requests; directions are the responses that request admits. The MCP
interface is already exactly this, and the current Idris code already says so
(`src/MCP/Container.idr:56`, `MCP = (m : Method) !> ResultOf m`). What the Idris
version does *not* do is use the rest of the structure. That structure is where
requirements 3, 4 and 7 come from, for free:

| Poly concept | What it is in this system |
|---|---|
| a **lens `p → y`** | **the server** — a section, `(i : p.Pos) → p.Dir i`; handles every request |
| a **lens `y → p`** | **a request**, only — the backward map lands in `1`, so no response rides along |
| the pair type `Σ (i : p.Pos), p.Dir i` | **one completed tool call** — request plus its response; *not* a hom-set |
| a **lens `S y^S → p`** | **the agent** — a Moore machine; state, a request per state, a state update per response |
| the **composite `S y^S → p → y`** | **one round-trip**, which is precisely a state transition `S → S` |
| **coproduct `Σ_t p_t`** | **the tool registry** — adding a tool is taking a coproduct |
| **composition `p ◁ q`** | **a two-step protocol** — "call this, then depending on what came back, call that" |
| **cofree comonoid `𝒞_p`** | **the space of all sessions**; one agent run is a path through it |
| **`p` for the tactic engine** | positions = proof states, directions = tactic outcomes (Hancock–Setzer interaction structures) |

That last row is the one that earns requirement 7. Lean's tactic engine is itself an
interaction structure — a polynomial. Proof search is an agent, i.e. a lens
`S y^S → p_tactic`. So "demonstrate Lean tactics" and "demonstrate agentic AI" are
the *same demo* viewed at two altitudes.

Two facts worth stating because they are one-liners in Lean and they make the
mapping above a theorem rather than an analogy:

```lean
Lens p y        ≃  ((i : p.Pos) → p.Dir i)   -- sections are servers
Lens (S y^S) y  ≃  (S → S)                   -- so agent ∘ server is a state transition
```

**Done** — both are proved in `Poly/Basic.lean` (`sectionEquiv`, `step`, `step_eq`),
axiom-free, as is `posEquiv : Lens y p ≃ p.Pos`. That third one is the correction to an
earlier draft of this plan, which claimed `Lens y p ≃ Σ i, p.Dir i`. It does not: the
backward map of a lens out of `y` lands in `y.Dir = 1` and carries no response. The
"completed tool call" type is `Σ (i : p.Pos), p.Dir i`, which is not a hom-set. Worth
recording the slip rather than quietly fixing it, since the whole point of §11 is that
this project distinguishes what is checked from what merely sounds right.

### What Lean buys us that Idris could not

This matters, because "port to another dependently typed language" is otherwise a
lateral move. `src/MCP/Proof.idr:1-10` states the Idris limitation plainly: the
elaborator is baked into the `idris2` binary, so "the typechecker is the oracle" had
to be realized by *spawning a subprocess per candidate*. In Lean 4:

- **The kernel is a library.** `import Lean` gives `Lean.Elab.runFrontend`, so a
  candidate can be elaborated **in process** and the resulting `Environment`
  inspected directly. The oracle stops being a shell-out.
- **The soundness gate becomes real.** `src/MCP/Proof.idr:76-83` gates on a
  *string grep* for `believe_me`, `assert_total`, etc. That is a blacklist, and
  blacklists leak. Lean replaces it with `Lean.collectAxioms` — a kernel-level audit
  of what the proof term actually depends on — accepted only if the axiom set is a
  subset of `{propext, Classical.choice, Quot.sound}`. `sorryAx` present ⇒ reject.
  This is the single biggest correctness upgrade in the whole plan, and it is worth
  saying out loud in the writeup that v1's gate was weaker.
- **JSON-RPC comes with the language.** `Lean.Data.JsonRpc` and `Lean.Data.Json`
  (with `deriving ToJson, FromJson`) are in core, used by Lean's own LSP server.
  `src/JSONRPC.idr` (181 lines, hand-written) mostly deletes.
- **Mathlib.** `Mathlib.CategoryTheory.*` is the target vocabulary for requirement 2.
  There is nothing comparable to formalize *into* on the Idris side.

### One structural fix to carry over

In v1, `vendor/container-compendium/mcp-demo/McpReal.idr` models the client as a real
value of the compendium's dependent-lens type — and the README admits it is "not wired
into the live transport." So the elegant part and the running part are two different
programs. **In v2 they must be one program.** The Lean server's live dispatch *is* the
section; the Lean agent *is* the lens; the trace the front end draws *is* the run. If
that unification does not survive implementation, the paper claim weakens, so treat it
as the primary architectural constraint, not a nicety.

---

## 2. Repo restructure

Do not delete the Idris work — it is the strongest available evidence that the design
is language-independent, and it's a genuine asset in the writeup.

```
CLAUDE CONTAINERS/
  lean-poly-mcp/              ← new Lake project, the real repo now
    Poly/                     Poly kernel + proofs
    Mcp/                      server, transport, tools
    Oracle/                   kernel oracle + axiom audit
    Formalize/                category-theory autoformalization
    Agent/                    the lens-driven agent
    Aristotle/                Harmonic client (Python side-process)
    web/                      front end
    test/
    lakefile.toml, lean-toolchain
  idris-mcp/                  ← preserved, README retitled "v1 (Idris2)"
```

Toolchain: pin `lean-toolchain` to whatever Mathlib's current release requires, and
resolve `sinhp/Poly` against it (see §3 risk note).

---

## 3. Phase 1 — the Poly kernel

**Decision to make first: vendor vs depend.**

- [`sinhp/Poly`](https://github.com/sinhp/Poly) (Awodey/Hazratpour) is the serious
  Lean 4 formalization — LCCCs, Beck–Chevalley, univariate and multivariate
  polynomial functors, composition, monoidal and bicategory structure. It currently
  pins `v4.28.0-rc1`.
- `Mathlib.Data.PFunctor.Univariate.Basic` is `PFunctor` = container `(A, B : A → Type)`,
  with W-types. Small, stable, already a Mathlib dependency.

Recommendation: **write a small self-contained `Poly/` (~300 lines) and connect it to
both.** The self-contained version is what the server compiles against (fast, no
version risk, and it is the part we want to *show*); then add `Poly/Bridge.lean`
proving it agrees with `PFunctor`, and optionally a `sinhp/Poly` comparison behind a
lake feature flag. This exactly mirrors the v1 strategy of vendoring a patched slice
of container-compendium, which worked.

Contents:

```lean
structure Poly where
  Pos : Type
  Dir : Pos → Type

structure Lens (p q : Poly) where
  onPos : p.Pos → q.Pos
  onDir : (i : p.Pos) → q.Dir (onPos i) → p.Dir i
```

then: `id`, `comp`, category laws; `y`, `𝟘`, `𝟙`; coproduct `+`, product `×`,
Dirichlet `⊗`, composition `◁`; the two equivalences from §1; `Category Poly` instance
so Mathlib's category-theory machinery applies. Cofree comonoid `𝒞_p` last — it is the
hardest and the front end only needs the *tree*, which can be defined directly.

**Risk:** `sinhp/Poly` toolchain may not match Mathlib's. Mitigation is the vendored
kernel above; the dependency is then optional rather than load-bearing.

---

## 4. Phase 2 — the MCP server in Lean

Port `src/MCP/{Types,Container,Transport}.idr`, `src/{Server,JSONRPC}.idr`.

```lean
inductive Method where
  | initialize (protocolVersion : String)
  | listTools
  | callTool (name : String) (args : Json)
  | check (decl : String)
  | prove (prompt : String)
  ...

abbrev ResultOf : Method → Type
  | .initialize _ => InitializeResult
  ...

def MCP : Poly := ⟨Method, ResultOf⟩

def server : Lens MCP y          -- ← the section; exhaustiveness is the kernel's job
```

The v1 compile-time-safety demo (README §"The compile-time safety demo") ports
directly and gets *better*: keep a `docs/negative-examples.lean` with the wrong-shape
handler commented out and the actual Lean error text pasted beneath it.

Transport: `Lean.Data.JsonRpc` over stdio, same newline-delimited framing the Python
GUI already speaks, so `gui/server_gui.py`'s bridge logic survives the port.

---

## 5. Phase 3 — the oracle

`Oracle/Kernel.lean`:

1. `elaborate (src : String) : IO (Environment ⊕ Diagnostics)` via `Lean.Elab.runFrontend`.
2. `auditAxioms (env) (declName) : Except String Unit` via `Lean.collectAxioms`,
   whitelist `{propext, Classical.choice, Quot.sound}`, explicit `sorryAx` rejection.
3. Reject `unsafe`, `partial`, `native_decide`, `@[implemented_by]`, and `macro`/`elab`
   in candidate source — not as the primary gate (the axiom audit is) but as defense
   in depth.
4. Confirm the elaborated statement is **α-equivalent to the goal we asked for** — v1
   could not do this and the README documents the consequence honestly (the model
   silently proved the *negation* of a false prompt and reported `checked`). In Lean,
   separating "statement file" from "proof file" and comparing types makes that class
   of misformalization *checkable*, not just disclosable. Keep the `paraphrase` field
   anyway; belt and braces.

Keep v1's evidence-carrying `ProofResult` (`Checked / Refuted / Unknown / ParseErr`) —
its distinction between "this candidate failed" and "we ran out of attempts" is
correct and unusually careful. Add `axioms : List Name` to `Checked`.

**Performance — resolved, and more cheaply than planned.** This section proposed running
[`leanprover-community/repl`](https://github.com/leanprover-community/repl) as a side
process with pickled environments. That turned out to be unnecessary. `Lean.Elab.process`
takes an existing `Environment` and returns the new one plus the message log, so Mathlib
is imported **once, in-process**, and every candidate reuses it:

```
[64588 ms] import Mathlib (ONCE, at startup)
   [138 ms] first category-theory candidate
    [17 ms] .. subsequent candidates
     [4 ms] .. a rejected one
```

No subprocess, no IPC, no pickling, no external dependency. Startup cost is real and is
paid once; `Mcp/Main.lean` takes the import set as an argument so `Init`-only runs start
instantly for tests.

---

## 6. Phase 4 — category-theory autoformalization

Retarget `prove` from "arbitrary Nat lemmas" to `Mathlib.CategoryTheory`. A graded
benchmark set, easiest first — this doubles as the eval harness:

- **Tier 0 (must pass):** identity/associativity in a given category; functors preserve
  isomorphisms; a natural transformation's naturality square; uniqueness of inverses.
- **Tier 1:** Yoneda-adjacent statements; limits/colimits as universal properties;
  adjunction unit/counit triangle identities.
- **Tier 2 (our home turf):** statements *about Poly itself* — `Lens` composition is
  associative; `◁` is monoidal with unit `y`; `Lens y p ≃ Σ i, p.Dir i`. These are the
  showpiece: the system proves theorems about the very structure it is built from.

Tier 2 is the answer to "why category theory *here*" and it is what makes the project
self-referential in a way that reads as design rather than decoration.

---

## 7. Phase 5 — Aristotle

[`aristotlelib`](https://pypi.org/project/aristotlelib/) (Python ≥3.10),
`ARISTOTLE_API_KEY`, keys from `aristotle.harmonic.fun/dashboard/keys`. CLI:
`aristotle submit "<prompt>" --project-dir <dir> [--wait]`, `aristotle formalize
paper.tex`, `aristotle list`, `aristotle download <id>`.

**Critical design constraint: Aristotle is slow.** The published case study reports an
~8 hour run on a hard formalization. So:

- **Never block a tool call on it.** Model it as a job: `aristotle/submit` returns a
  job id; `aristotle/status`, `aristotle/fetch` poll. In Poly terms the submit
  position's direction is a *job handle*, not a proof — and that is a nice, honest
  illustration of why the direction type is dependent on the position.
- **Re-verify everything locally.** Aristotle's output goes through *our* Phase 3
  oracle — elaborate, axiom-audit, statement-match — before it is ever labelled
  `checked`. The vendor's assertion of verification is an input, not evidence. Say
  this explicitly in the README; it is the same discipline v1 applied to the LLM.
- Two proposers, one oracle: `prove` (LLM, fast, cheap, from v1) and
  `prove_aristotle` (slow, strong). Comparing them on the Phase 4 benchmark is a
  genuine result to report.

**Risk:** paid key, unknown rate limits, and an 8-hour worst case means the demo needs
pre-warmed cached results. Plan for a `--replay` mode backed by stored job outputs.

---

## 8. Phase 6 — tactics

Four levels, so "demonstrates understanding of tactics" is shown rather than claimed:

1. **Use them well.** The Phase 1 proofs should read idiomatically — `ext`, `funext`,
   `aesop_cat`, `simp` with a curated `@[simp]` set on `Lens`, `induction ... with`.
   `aesop_cat` in particular is the Mathlib category-theory discharge tactic; using it
   correctly is itself a signal.
2. **Write one.** A custom `poly_ext` tactic (Lean metaprogramming: `elab` /
   `macro_rules`) that reduces a `Lens` equality to `onPos` and `onDir` goals,
   handling the dependent-`HEq` obligation that makes this annoying by hand. Small,
   genuinely useful in Phase 1, and unfakeable.
3. **Expose them.** MCP tools `tactic/state` and `tactic/apply` backed by the REPL's
   `proofState` mode. Now the tactic engine is a polynomial the agent can drive:
   positions = proof states, directions = outcomes.
4. **Fail informatively.** A `docs/tactic-notes.lean` of worked failures — where
   `simp` loops, why `decide` won't close a `Type`-level goal, what `native_decide`
   costs you in trust (it is excluded from the whitelist for a reason).

---

## 9. Phase 7 — the agent

`Agent/` — an agent is `Lens (S y^S) MCP`, defined in Lean, and *the runtime executes
that value* (see the §1 structural fix).

```lean
structure AgentState where
  goal      : String
  attempts  : List Attempt
  proofState: Option ProofStateId
  phase     : Phase

def prover : Lens (AgentState.poly) MCP
```

The loop: pick a request from the state (`onPos`), receive the response, update
(`onDir`). Strategy inside `onPos`: try `check` on cached lemmas → `tactic/apply`
search → `prove` (LLM) → `prove_aristotle` on the ones that survive. Every step is
logged as a node in the session tree, i.e. a path in `𝒞_MCP`. That log is the front
end's data model, which is why the front end is not decoration either.

Multi-agent, if time allows: a *proposer* agent and an *auditor* agent that only ever
reads axiom sets and statement-matching results. The auditor's inability to propose
is a type-level fact, not a prompt instruction.

---

## 10. Phase 8 — front end

Replace the 198-line stdlib GUI with something that shows the mathematics. Backend
stays thin (the existing Python bridge in `gui/server_gui.py` already speaks exactly
the right protocol and can be extended); the UI is where the work goes.

Four panels:

1. **Polynomial explorer** — the server's `p`: positions listed, directions per
   position, live. Adding a tool visibly changes the coproduct.
2. **Session tree** — the agent's run drawn as a path through `𝒞_p`. Branches the
   agent considered and abandoned shown greyed. This is the picture that makes the
   categorical story legible to someone who does not want to read Lean.
3. **Proof panel** — statement, candidate, kernel verdict, **axiom set**, and
   statement-match result. The axiom list is the trust story; make it prominent.
4. **Aristotle queue** — submitted jobs, elapsed time, and local re-verification
   status shown *separately* from Harmonic's own claim.

Recommend a single self-contained page (no build step, no CDN) over a React app —
it stays reviewable, it can be published as an Artifact for sharing, and the audience
for this is researchers, not consumers.

---

## 11. What to claim, and what not to

Given this may be read by people who work on container theory, the writeup should be
scrupulous about the boundary. Verified claims and marketing claims must not be
adjacent in the same sentence.

**Can claim, because the kernel checks it:**
- The MCP interface is a polynomial functor; the server is a section of it; the agent
  is a lens into it; exhaustiveness and result-shape correctness are kernel facts.
- Every returned proof elaborated under Lean's kernel and depends only on
  `{propext, Classical.choice, Quot.sound}` — with the axiom list shown.
- The returned theorem's statement matches the requested statement up to α-equivalence.

**Must not claim:**
- That the *English prompt* was proven. It was not; a statement was proven, and the
  formalization step is unverified in principle. v1's README is exemplary on this
  (the `n = S n` incident) — carry that section forward, updated.
- That the running server "is" a morphism in Poly in a mechanized sense. It is
  *specified* as one in Lean and the Lean value is what executes; there is no
  mechanized bridge between the Lean semantics and the compiled binary's IO behaviour.
  State it that way.
- Novelty for the correspondence itself. Containers ≅ polynomial functors
  (Abbott–Altenkirch–Ghani), interaction structures (Hancock–Setzer), and dynamical
  systems as lenses (Niu–Spivak) are established. The contribution here is that a
  *working system* is built on them, not the theory.

---

## 12. Suggested order

Phases 1 → 2 → 3 are the spine and must land in that order; nothing else is
demonstrable without them. After that: 6 (tactics) and 4 (category theory) together,
since the Tier-2 benchmark *is* the Phase 1 proof set. Then 7 (agent), then 8 (front
end), with 5 (Aristotle) slotted in whenever the API key exists — it is the most
externally-blocked item and the least structurally coupled, so it should never be on
the critical path.

Highest-risk items, watch early: Mathlib/`sinhp-Poly` toolchain alignment (§3), REPL
environment-pickling performance (§5), and Aristotle latency (§7).

## Sources

- [Aristotle API — Harmonic (support overview)](https://eco.com/support/en/articles/14114345-what-is-the-harmonic-aristotle-api-formal-verification-ai-for-developers)
- [`aristotlelib` on PyPI](https://pypi.org/project/aristotlelib/)
- [Using the Aristotle API for AI-Assisted Theorem Proving in Lean 4 (arXiv)](https://arxiv.org/html/2605.20120v1)
- [`sinhp/Poly` — Lean 4 formalization of polynomial functors](https://github.com/sinhp/Poly)
- [`Mathlib.Data.PFunctor.Univariate.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/PFunctor/Univariate/Basic.html)
- [`Lean.Data.JsonRpc`](https://leanprover-community.github.io/mathlib4_docs/Lean/Data/JsonRpc.html)
- [`leanprover-community/repl`](https://github.com/leanprover-community/repl)
- [Validating a Lean Proof — Lean reference manual](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
- [Did you prove it? — leanprover-community](https://leanprover-community.github.io/did_you_prove_it.html)

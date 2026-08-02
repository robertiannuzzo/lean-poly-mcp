# lean-poly-mcp

An MCP server whose interface **is** a polynomial functor, written in Lean 4, driving
an agent that autoformalizes category theory — where Lean's kernel is the only thing
ever trusted.

> **Status: Phases 1–4, 6, 7 done.** The Poly kernel is proved and axiom-free; the MCP
> server builds, runs, and answers real JSON-RPC over stdio; the kernel oracle
> verifies candidates against Mathlib in milliseconds; the graded benchmark and the
> free tiers of the escalation ladder run locally. The agent, Aristotle, and the front
> end are not written yet.
> **Aristotle is the only external service** — there is no LLM and no
> `ANTHROPIC_API_KEY`; see [`docs/lean-upgrade-plan.md`](docs/lean-upgrade-plan.md) §2.
> See [`docs/lean-upgrade-plan.md`](docs/lean-upgrade-plan.md) for the full plan and
> [`v1-idris/`](v1-idris/) for the Idris2 predecessor this is derived from.

```sh
lake build server
printf '%s\n' \
  '{"jsonrpc":"2.0","id":1,"method":"tools/call","params":{"name":"check","arguments":{"source":"theorem cand : 2 + 2 = 4 := rfl"}}}' \
  | ./.lake/build/bin/server
# → {"content":[{"text":"checked — depends on no axioms","type":"text"}],
#    "isError":false,"structuredContent":{"axioms":[],"outcome":"checked"}}
```

The oracle is an ordinary **MCP tool**, so any MCP client can drive it:

```sh
claude mcp add lean-poly-mcp -- "$(pwd)/.lake/build/bin/server" Mathlib
```

## The idea

In **Poly**, the category of polynomial functors (equivalently, containers in the
sense of Abbott–Altenkirch–Ghani), an object is

```
p  =  Σ_{i : p.Pos}  y ^ p.Dir i
```

— positions are requests, directions are the responses that request admits. An MCP
interface is exactly this. Once you say so, the rest of the system falls out of the
structure rather than being designed separately:

| Poly | Here |
|---|---|
| lens `p → y` | the **server** — a section, `(i : p.Pos) → p.Dir i` |
| lens `y → p` | a **request**, and nothing more (see the caveat below) |
| lens `S y^S → p` | the **agent** — a Moore machine |
| the composite `S y^S → p → y` | **one round-trip**, which is exactly a state transition `S → S` |
| `Σ (i : p.Pos), p.Dir i` | a **completed tool call** — request plus its response |
| indexed coproduct `Σ_t p_t` | the **tool registry** — `Poly.sigma`, one summand per tool |
| composition `p ◁ q` | a **two-step protocol** |
| cofree comonoid `𝒞_p` | the space of **all sessions**; one run is a path through it |
| `p` for the tactic engine | positions = proof states, directions = tactic outcomes |

The last row is why tactic-level proof search and agentic tool use are the same
construction here, seen at two altitudes.

Two facts license the table, and both are machine-checked in
[`Poly/Basic.lean`](Poly/Basic.lean) — `sectionEquiv` and `step`/`step_eq`:

```lean
Lens p y        ≃  ((i : p.Pos) → p.Dir i)   -- sections are servers
Lens (S y^S) y  ≃  (S → S)                   -- so agent ∘ server is a state transition
```

**A caveat worth stating precisely,** since it is easy to get backwards and an earlier
draft of this README did: a lens `y → p` is *not* a completed tool call. Its backward
map lands in `y.Dir = 1`, so it carries no response; `Lens y p ≃ p.Pos` picks out a
request only. A completed call is an element of `Σ (i : p.Pos), p.Dir i`, which is not
a hom-set of `Poly` at all. Both statements are proved as `sectionEquiv` and `posEquiv`
so the distinction is enforced rather than remembered.

## Why Lean, and not Idris2

`v1-idris/` is a complete, working MCP server and client in Idris2 built on the same
container idea. Three things it documents as limitations are structural, not
incidental, and Lean removes them:

- **The oracle had to be a subprocess.** Idris2's elaborator lives inside the `idris2`
  binary, so v1 spawned a compiler per candidate
  ([`v1-idris/src/MCP/Proof.idr`](v1-idris/src/MCP/Proof.idr)). Lean's kernel is a
  library — `import Lean` gives `Lean.Elab.process`, which takes an existing
  `Environment` and returns the new one plus the message log, so candidates elaborate
  in-process against an environment imported once.
- **The soundness gate was a string grep.** v1 rejects candidates containing
  `believe_me`, `assert_total`, `unsafePerformIO` and friends by substring search — a
  blacklist, and blacklists leak. Lean replaces it with `Lean.collectAxioms`: a
  kernel-level audit of what the proof term actually depends on, accepted only if that
  set is contained in `{propext, Classical.choice, Quot.sound}`, with `sorryAx`
  rejected outright.
- **There was nothing to formalize *into*.** Mathlib's `CategoryTheory` hierarchy is
  the target vocabulary that makes "autoformalize category theory" a real task.

There is also a structural flaw in v1 being fixed here: its most elegant artifact,
[`McpReal.idr`](v1-idris/vendor/container-compendium/mcp-demo/McpReal.idr), models the
client as a genuine value of a dependent-lens type — but is not wired into the live
transport. The elegant program and the running program are two different programs. In
v2 they must be one: the server's live dispatch *is* the section, and the agent driving
it *is* the lens.

## The tool registry is the coproduct

`ToolMCP = Poly.sigma toolPoly` — a position is a tool together with *that tool's*
arguments, and a direction is *that tool's* own result type:

```lean
@[reducible] def toolPoly : ToolId → Poly
  | .hello => ⟨Option String, fun _ => String⟩
  | .check => ⟨CheckRequest, fun _ => Oracle.Outcome⟩
```

Adding a tool is one constructor and one case; the claim "adding a tool is taking a
coproduct" is discharged in code rather than asserted in prose. The dependent structure
survives all the way to the handler — `check` returns an `Oracle.Outcome`, not a
stringly-typed envelope — and is flattened exactly once, at the wire boundary. Swap two
branches and the compiler names the direction family:

```
but is expected to have type
  ToolMCP.Dir ⟨ToolId.hello, snd✝⟩
```

## How far free tactics get

Tiers 0 and 1 of the escalation ladder are ordinary Lean tactics run through the same
oracle as everything else — a local success is trusted no more than a remote one. The
`search` tool exposes them, and `test/BenchmarkTest.lean` measures them:

```
tier 0:  7/7   solved with no network        (the category laws)
tier 1:  2/4                                 (needs a real rewrite)
tier 2: 10/11                                (statements about Poly itself)
```

That bounds what a paid prover is actually for. Two caveats matter more than the numbers:
`exact?` "solving" a tier-2 goal often means it *found* a lemma we already proved, so the
corpus marks genuinely-absent statements `[novel]`; and the one informative miss —
`a trace of n steps has n entries` — needs **induction**, which no discharge tactic does.

## The oracle

The only trusted component. Three gates: elaborate, audit axioms, match the statement.
Everything that *produces* proofs is untrusted.

The audit is the part that matters. It is not a list of banned words — it is
`Lean.collectAxioms` on the accepted term, rejecting anything outside
`{propext, Classical.choice, Quot.sound}`. Measured behaviour, from
[`test/OracleTest.lean`](test/OracleTest.lean):

| attack | verdict |
|---|---|
| `by sorry` | `unsoundAxioms [sorryAx]` — note `sorry` is only a *warning* to the elaborator, so it sails through gate 1 |
| `by native_decide` | `unsoundAxioms [Lean.ofReduceBool, Lean.trustCompiler]` |
| a hand-rolled `axiom` | `unsoundAxioms [oops]` |
| proves the **negation** of the request | `statementMismatch`, with the type mismatch verbatim |
| `Classical.em` | `checked [Classical.choice, Quot.sound, propext]` — allowed, and disclosed |

The `native_decide` row is the argument for auditing over blacklisting, and the
toolchain move sharpened it. On our pin it introduces `Lean.ofReduceBool` and
`Lean.trustCompiler`; on v4.33.0-rc1 it instead minted a *per-declaration* axiom named
after the declaration being proved. So a name-based gate would need names that vary with
both the declaration **and** the toolchain. The whitelist needs to know none of them —
`native_decide` is named nowhere in `Oracle/Kernel.lean`.

The `statementMismatch` row is the failure v1 hit live: asked to prove something false,
the model proved its negation — a true theorem, axiom-clean, and *not what was asked*.
v1 could only disclose this in a prose paraphrase. Here it is caught.

### Performance

The oracle elaborates **in-process** via `Lean.Elab.process`, against an environment
imported once at startup:

```
[63843 ms] import Mathlib (ONCE, at startup)
   [139 ms] identity is a left unit for ≫          → checked [propext]
    [23 ms] iso hom ≫ inv = id, statement matched  → checked [propext]
    [25 ms] functors preserve retractions          → checked []
     [6 ms] ATTACK: sorry in a Mathlib proof       → unsoundAxioms [sorryAx]
```

The plan anticipated needing `leanprover-community/repl` as a side process with pickled
environments to make this tractable. It isn't necessary: reusing the `Environment`
in-process gives millisecond candidates directly, with no subprocess and no IPC.

## Layout

```
Poly/         the Poly kernel — objects, lenses, ⊕ ⊗ × ◁, and the two equivalences above
Mcp/          the MCP interface as a polynomial; server as a section; JSON-RPC transport
Oracle/       in-process elaboration, axiom audit, statement matching
Formalize/    category-theory autoformalization and its graded benchmark
Agent/        the agent as a lens S y^S → MCP
Aristotle/    Harmonic Aristotle API client (job-based; output re-verified locally)
web/          front end — polynomial explorer, session tree, axiom audit, job queue
test/
v1-idris/     the Idris2 predecessor, preserved intact
```

Git history from v1 is preserved in this repository, so `git log` shows the whole
evolution rather than starting from a synthetic initial commit.

## Toolchain — pinned to Aristotle's, deliberately

```
leanprover/lean4:v4.28.0
mathlib  8f9d9cff6bd728b17a24e163c9402775d9e6a365   (= tag v4.28.0)
```

**Do not bump either to chase a newer Mathlib.** Re-verifying Aristotle's output against
our own kernel is the whole trust story, and it only works if both sides speak the same
Mathlib. Under version skew a failed re-verification is ambiguous — unsound, or a lemma
renamed in the intervening commits? — and an ambiguous verdict destroys exactly what the
oracle exists to provide.

Two things fall out of this. It puts us on a stable release rather than a release
candidate, with Mathlib pinned to a commit rather than the moving `master`. And
[`sinhp/Poly`](https://github.com/sinhp/Poly) pins `v4.28.0-rc1` — the same release line
— so it is back in range as an optional cross-check. The small vendored `Poly/` kernel
stays as the thing the server compiles against: fast, readable, no version risk.

```bash
brew install elan-init
lake update && lake exe cache get
lake build
./scripts/check.sh --full
```

## What this will and will not claim

Stated up front, because the distinction is the point of the project.

**Checkable by the kernel:** that the interface is a polynomial functor and the server
a section of it; that every returned proof elaborates and depends only on the
whitelisted axioms, with the axiom list shown; that the proved statement matches the
requested statement up to α-equivalence.

**Not claimed:** that an *English* prompt was proven — the formalization step is
unverified in principle, and v1's README documents a live instance where a model
silently proved the negation of a false prompt and reported success. Nor that the
running binary "is" a morphism in Poly in any mechanized sense: it is *specified* as
one in Lean, and that Lean value is what executes, but there is no mechanized bridge
between the Lean semantics and the compiled program's IO behaviour.

The container/polynomial-functor correspondence, interaction structures
(Hancock–Setzer), and dynamical systems as lenses (Niu–Spivak) are established
results. Nothing here claims novelty for the theory; the contribution is a working
system built on it.

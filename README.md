# lean-poly-mcp

An MCP server whose interface **is** a polynomial functor, written in Lean 4, driving
an agent that autoformalizes category theory — where Lean's kernel is the only thing
ever trusted.

> **Status: Phases 1–3 done.** The Poly kernel is proved and axiom-free; the MCP
> server builds, runs, and answers real JSON-RPC over stdio; the kernel oracle
> verifies candidates against Mathlib in milliseconds. The autoformalization
> benchmark, tactics, the agent, Aristotle, and the front end are not written yet.
> See [`docs/lean-upgrade-plan.md`](docs/lean-upgrade-plan.md) for the full plan and
> [`v1-idris/`](v1-idris/) for the Idris2 predecessor this is derived from.

```sh
lake build server
printf '%s\n' \
  '{"jsonrpc":"2.0","id":1,"method":"check","params":{"source":"theorem cand : 2 + 2 = 4 := rfl"}}' \
  | ./.lake/build/bin/server
# → {"axioms":[],"outcome":"checked","source":"theorem cand : 2 + 2 = 4 := rfl"}
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
| coproduct `Σ_t p_t` | the **tool registry** |
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
  library — `import Lean` gives `Lean.Elab.runFrontend`, and candidates elaborate
  in-process.
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
| `by native_decide` | `unsoundAxioms [cand._native.native_decide.ax_1]` |
| a hand-rolled `axiom` | `unsoundAxioms [oops]` |
| proves the **negation** of the request | `statementMismatch`, with the type mismatch verbatim |
| `Classical.em` | `checked [propext, Classical.choice, Quot.sound]` — allowed, and disclosed |

The `native_decide` row is the argument for auditing over blacklisting: on v4.33.0-rc1
it mints a *per-declaration* axiom whose name varies with the declaration, so a
name-based gate would have to know a name it cannot know in advance. The whitelist
needs to know nothing. Nothing in `Oracle/Kernel.lean` mentions `native_decide`.

The `statementMismatch` row is the failure v1 hit live: asked to prove something false,
the model proved its negation — a true theorem, axiom-clean, and *not what was asked*.
v1 could only disclose this in a prose paraphrase. Here it is caught.

### Performance

The oracle elaborates **in-process** via `Lean.Elab.process`, against an environment
imported once at startup:

```
[64588 ms] import Mathlib (ONCE, at startup)
   [138 ms] identity is a left unit for ≫          → checked [propext]
    [17 ms] iso hom ≫ inv = id, statement matched  → checked [propext]
    [24 ms] functors preserve retractions          → checked []
     [4 ms] ATTACK: sorry in a Mathlib proof       → unsoundAxioms [sorryAx]
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

## Toolchain

Pinned to `leanprover/lean4:v4.33.0-rc1`, matching Mathlib master. Note that
[`sinhp/Poly`](https://github.com/sinhp/Poly) currently pins `v4.28.0-rc1`, so it
cannot be a hard dependency at this pin — hence the small vendored `Poly/` kernel,
bridged to `Mathlib.Data.PFunctor` for cross-checking.

```bash
brew install elan-init
lake update
lake build
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

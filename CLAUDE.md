# Working rules for this repo

Read this before doing anything else. These exist to keep sessions cheap; the repo is
1k lines of our own Lean sitting next to a 7.9 GB `.lake` directory, so the default
behaviours are wrong here.

## Never read these into context

- **`.lake/`** — 7.9 GB, 8300+ Mathlib oleans. Never `grep`, `glob`, `find`, or `ls -R`
  it. If you need a Mathlib definition, use `lake env lean` with `#check`/`#print`, or
  read the single specific file under `~/.elan/toolchains/*/src/lean/`.
- **`v1-idris/vendor/`** — ~20k lines of vendored Idris. Reference by path; do not read
  in bulk.
- **`docs/idris-mcp-architecture.pdf`** — read only if specifically asked.

## Filter every build command

`lake build` emits hundreds of lines. Always reduce:

```bash
lake build 2>&1 | grep -E '^(error|✖)|\.lean:' | head -20
```

A bare `lake build` or `lake env lean --run` with unfiltered output is a mistake.

## Use the test script

```bash
./scripts/check.sh          # fast suites only (Init-only) — seconds
./scripts/check.sh --full   # adds the Mathlib suite — ~70s, do this rarely
```

One line per suite. Do not run the suites individually unless one fails and you need
the detail.

## Mathlib is expensive; batch it

Importing Mathlib costs ~65s and several GB of RAM. Everything that can be checked
against `Init` should be. When you *do* need a Mathlib run, put every question you have
into one program and run it once — do not iterate one candidate at a time.

## Don't spawn subagents

Every subagent starts cold and re-derives context this session already has. Do the work
inline. (Only exception: the user explicitly asks.)

## Aristotle is the only external service

**There is no LLM in this project and no `ANTHROPIC_API_KEY`.** Aristotle does both the
formalization (`aristotle formalize`) and the proving (`aristotle submit`); the agent is a
Lean policy, not a prompt. If you find yourself reaching for a model API, that is a design
change — raise it, don't add it. See `docs/lean-upgrade-plan.md` §2.

`ARISTOTLE_API_KEY` is **separately billed** — it does not touch Claude Code usage, but it
costs money and is the real runaway risk, because an escalation loop is by construction a
loop.

Anything that calls out must have, in code and not by convention:

- a hard attempt cap (v1 used 3; keep it)
- a `--replay` mode backed by cached job outputs, so demos and tests never hit the network
- submissions job-based, never blocking; runs of ~8h are documented
- no retry-on-timeout without a ceiling

Write the cap before the call, not after. Tiers 0 and 1 (`aesop_cat`, `exact?`) are free
and local — exhaust them before spending.

## Toolchain is pinned to Aristotle's, deliberately

`leanprover/lean4:v4.28.0` and Mathlib `8f9d9cff` (tag `v4.28.0`). Do **not** bump either
to chase a newer Mathlib: re-verifying Aristotle's output locally is the whole trust story,
and it only works if both sides speak the same Mathlib.

## Session hygiene

Prefer a fresh session per phase. Context is re-sent every turn, so a long session pays
for its whole history repeatedly; the phases are independent enough that a new session
plus this file and the README is enough to continue.

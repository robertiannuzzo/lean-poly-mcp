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

## Caps are mandatory in Phases 4–5

`Formalize/` and `Aristotle/` call **separately billed** APIs (`ANTHROPIC_API_KEY`,
`ARISTOTLE_API_KEY`) — these do not touch Claude Code usage, but they do cost money and
they are the real runaway risk, because a repair loop is by construction a loop.

Anything that calls out must have, in code and not by convention:

- a hard attempt cap (v1 used 3; keep it)
- a `--dry-run` / replay mode backed by cached responses, so demos and tests never hit
  the network
- Aristotle submissions job-based, never blocking; runs of ~8h are documented
- no retry-on-timeout without a ceiling

Write the cap before the call, not after.

## Session hygiene

Prefer a fresh session per phase. Context is re-sent every turn, so a long session pays
for its whole history repeatedly; the phases are independent enough that a new session
plus this file and the README is enough to continue.

import Oracle.Kernel

/-!
# Aristotle client

Tier 2 of the escalation ladder: the one component that leaves the machine.

Three properties this file is built around.

**Never blocking.** Published runtimes reach hours. `submit` returns a project id and
returns *immediately*; `status` and `fetch` poll. In Poly terms the submit position's
direction is a **job handle, not a proof** — a clean illustration of why the direction
type depends on the position.

**Never trusted.** Whatever comes back goes through `Oracle.verify` before it is called
anything. Aristotle's own claim of verification is an input, not evidence. This is the
entire reason the toolchain is pinned to Aristotle's (`docs/lean-upgrade-plan.md` §3): if
our Mathlib differed from theirs, a failed re-verification would be ambiguous between
"unsound" and "a lemma was renamed", and an ambiguous verdict is exactly what the oracle
exists to eliminate.

**Offline by default in tests.** Setting `ARISTOTLE_REPLAY` to a directory makes every
call read a cached response instead of hitting the network — so the suite is fast and
deterministic, and CI never spends money. That is a testing property, not a spend cap.

The key is read from `ARISTOTLE_API_KEY` in the environment, inherited by the child
process. It is never passed as a command-line flag, because flags are visible in `ps`.
-/

namespace Aristotle

open Lean

/-- A submitted job. The direction of a `submit` is this, not a proof. -/
structure Job where
  projectId : String
  deriving Repr, Inhabited, BEq

/-- A formalized theorem statement, before any proof search. This is an untrusted
proposal: callers still use statement matching after a proof is produced, because
English/LaTeX → Lean is exactly where misformalization can enter. -/
structure Formalization where
  statement : String
  preamble : String := ""
  deriving Repr, Inhabited, BEq

inductive Status where
  | queued
  | running
  | succeeded
  | failed (detail : String)
  /-- The CLI said something we do not recognise. Reported rather than guessed at. -/
  | unrecognised (raw : String)
  deriving Repr, Inhabited

def Status.isTerminal : Status → Bool
  | .succeeded | .failed _ => true
  | _ => false

/-- Resolve the replay directory: an explicit argument wins, otherwise the
`ARISTOTLE_REPLAY` environment variable.

Passing it explicitly rather than only reading the environment keeps tests from mutating
global process state to exercise a code path — and `IO.setEnv` does not exist on this
toolchain anyway, so the parameter is both cleaner and necessary. -/
def resolveReplay (replay : Option String) : IO (Option String) := do
  match replay with
  | some d => return some d
  | none => return (← IO.getEnv "ARISTOTLE_REPLAY")

private def readReplay (replay : Option String) (name : String) : IO (Option String) := do
  match ← resolveReplay replay with
  | none => return none
  | some dir =>
    let path := System.FilePath.mk dir / name
    if ← path.pathExists then return some (← IO.FS.readFile path) else return none

/-- Run the `aristotle` CLI. The API key rides in the inherited environment, never in
`args`. -/
private def runCli (args : List String) : IO (Except String String) := do
  let out ← IO.Process.output { cmd := "aristotle", args := args.toArray }
  if out.exitCode == 0 then
    return .ok out.stdout
  else
    return .error s!"aristotle {args} exited {out.exitCode}: {out.stderr}{out.stdout}"

/-- Submit a staged project directory. Returns as soon as the job is accepted. -/
def submit (projectDir : String) (prompt : String) (replay : Option String := none) :
    IO (Except String Job) := do
  if let some cached ← readReplay replay "submit.txt" then
    return parseProjectId cached
  match ← runCli [prompt, "--project-dir", projectDir] with
  | .error e => return .error e
  | .ok out => return parseProjectId out
where
  /-- The CLI prints `Project created: <uuid>` among human-facing warnings (it also warns
  about a missing `.lake`, so the id is not simply the last line). Split on the marker
  rather than trimming: `String.trimLeft` returns a `Slice` on this toolchain, and
  reaching for it here costs more than it saves. -/
  parseProjectId (out : String) : Except String Job :=
    match out.splitOn "Project created:" with
    | _ :: rest :: _ =>
      let id := ((rest.splitOn "\n").headD "").replace " " ""
      if id.isEmpty then
        .error s!"empty project id in aristotle output:\n{out}"
      else .ok ⟨id⟩
    | _ => .error s!"could not find a project id in aristotle output:\n{out}"

/-- Ask Aristotle to translate prose/LaTeX into a Lean statement.

Replay reads `formalize.txt`; tests and demos therefore exercise the parsing path without
touching the network. The CLI output observed/documented for `formalize` is intentionally
treated as text, not trusted structure: comments and Markdown fences are stripped, then
the remaining Lean statement is handed to our own elaborator by callers. -/
def formalize (prompt : String) (imports : List String := ["Mathlib"])
    (replay : Option String := none) : IO (Except String Formalization) := do
  if let some cached ← readReplay replay "formalize.txt" then
    return parseFormalize cached
  let importArgs := imports.foldr (fun i acc => "--import" :: i :: acc) []
  let args := ["formalize", prompt] ++ importArgs
  match ← runCli args with
  | .error e => return .error e
  | .ok out => return parseFormalize out
where
  stripFence (s : String) : String :=
    let lines := s.splitOn "\n"
    let lines := lines.filter fun l =>
      let t := l.trimAscii.toString
      !(t.startsWith "```") && !(t.startsWith "--")
    "\n".intercalate lines

  firstStatementLine (s : String) : String :=
    let candidates := (stripFence s).splitOn "\n" |>.map (·.trimAscii.toString) |>.filter (!·.isEmpty)
    match candidates.find? (fun l => l.startsWith "∀" || l.startsWith "theorem " ||
        l.startsWith "example " || l.startsWith "def " || l.startsWith "class " ||
        l.startsWith "instance " || l.startsWith "#check ") with
    | some line =>
      let line := line.replace "#check" ""
      let line := line.replace "theorem cand :" ""
      let line := line.replace "example :" ""
      let line := line.replace " := by sorry" ""
      let line := line.replace " := sorry" ""
      line.trimAscii.toString
    | none => (stripFence s).trimAscii.toString

  parseFormalize (out : String) : Except String Formalization :=
    let stmt := firstStatementLine out
    if stmt.isEmpty then
      .error s!"empty formalization in aristotle output:\n{out}"
    else
      .ok { preamble := "open CategoryTheory", statement := stmt }

/-- Poll. Uses `tasks` rather than `show`: `show` is a live TUI that redraws with ANSI
escapes and does not terminate, which is unparseable and unpollable. -/
def status (j : Job) (replay : Option String := none) : IO Status := do
  let out ← match ← readReplay replay "status.txt" with
    | some cached => pure (.ok cached)
    | none => runCli ["tasks", j.projectId, "--limit", "1"]
  match out with
  | .error e => return .failed e
  | .ok text =>
    -- First data row of the table; the STATUS column is the last field.
    let rows := (text.splitOn "\n").filter (fun l =>
      !l.isEmpty && !(l.startsWith "ID ") && !(l.startsWith "---"))
    match rows.head? with
    | none => return .unrecognised text
    | some row =>
      let fields := (row.splitOn " ").filter (!·.isEmpty)
      match fields.getLast? with
      | none => return .unrecognised row
      | some st =>
        if st == "QUEUED" then return .queued
        else if st == "IN_PROGRESS" || st == "RUNNING" then return .running
        -- Observed live: the CLI reports `COMPLETE`, not `COMPLETED`. Guessing the
        -- plural cost one wrong poll; the others are kept as tolerated synonyms rather
        -- than as guesses, and anything unrecognised is reported rather than assumed.
        else if st == "COMPLETE" || st == "COMPLETED" || st == "SUCCEEDED" || st == "DONE"
        then return .succeeded
        else if st == "FAILED" || st == "ERROR" || st == "CANCELLED" then return .failed st
        else return .unrecognised row

/-- Download the finished project archive. -/
def fetch (j : Job) (destination : String) (replay : Option String := none) :
    IO (Except String Unit) := do
  if (← resolveReplay replay).isSome then return .ok ()
  match ← runCli ["download", j.projectId, "--destination", destination] with
  | .error e => return .error e
  | .ok _ => return .ok ()

/-! ## Re-verification — the part that matters

Aristotle returning a filled file is a claim. This turns it into a verdict. -/

/-- Verify a candidate Aristotle produced, against our own kernel.

`sorryAx` absent is literally "Aristotle honoured its contract" — the soundness gate and
the completion check are the same check, which is the reason `sorry` is such a good
interface here. -/
def reverify (env : Environment) (preamble source : String)
    (statement : Option String) : IO Oracle.Outcome :=
  Oracle.verify env
    { preamble := preamble, source := source, expected? := statement }

end Aristotle

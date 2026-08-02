import Aristotle.Client

/-!
# Aristotle round trip — replayed offline

Reproduces a **real** submission without touching the network. The fixtures in
`test/fixtures/aristotle/` are the verbatim output of one live run on 2026-08-01:

* goal: `(trace agent server n s).length = n` — the one benchmark entry the free ladder
  could not reach, because it needs induction and no discharge tactic does induction;
* project `385577ec-104c-4a77-bc17-82b148b9e7c7`, `COMPLETE` after ~3 minutes;
* `proof.lean` is exactly what came back.

The point of replaying it is that **the verification is not replayed**. Parsing is
exercised against recorded bytes, but `reverify` runs the real oracle against the real
kernel every time — so this test still fails if the proof stops checking, or starts
depending on an axiom, or stops proving the statement we asked for.
-/

open Lean Aristotle

def fixtures : String := "test/fixtures/aristotle"

/-- The statement submitted — kept separate from the proof on purpose, so the
statement-match check compares against what we *asked for* rather than against whatever
came back. -/
def requestedStatement : String :=
  "∀ {S : Type} {p : Poly} (agent : Agent S p) (server : Lens p y) (n : Nat) (s : S), (trace agent server n s).length = n"

def main : IO UInt32 := do
  let mut failed := 0

  -- 1. Parsing the submit response.
  match ← Aristotle.submit "unused-in-replay" "unused-in-replay" (replay := some fixtures) with
  | .error e => IO.println s!"  FAIL  submit parse: {e}"; failed := failed + 1
  | .ok job =>
    if job.projectId == "385577ec-104c-4a77-bc17-82b148b9e7c7" then
      IO.println s!"  ok    submit parsed project id ({job.projectId})"
    else
      IO.println s!"  FAIL  submit parsed wrong id: {job.projectId}"; failed := failed + 1

    -- 2. Parsing the status table. `COMPLETE`, not `COMPLETED` — found the hard way.
    match ← Aristotle.status job (replay := some fixtures) with
    | .succeeded => IO.println "  ok    status parsed COMPLETE as succeeded"
    | s => IO.println s!"  FAIL  status parsed as {repr s}"; failed := failed + 1

  -- 3. The verification is real, not replayed.
  let proof ← IO.FS.readFile (System.FilePath.mk fixtures / "proof.lean")
  let env ← Oracle.mkBaseEnv #[`Poly.Basic]
  match ← Aristotle.reverify env "open Poly" proof (some requestedStatement) with
  | .checked axs =>
    let axStr := if axs.isEmpty then "none" else toString (axs.toList.map toString)
    IO.println s!"  ok    Aristotle's proof re-verifies — axioms: {axStr}, statement matched"
  | o =>
    IO.println s!"  FAIL  Aristotle's proof did NOT re-verify: {repr o}"; failed := failed + 1

  -- 4. And the gate still bites: the same statement with the proof removed is rejected,
  --    which is what makes `checked` above mean something.
  let sorried := "theorem cand {S : Type} {p : Poly} (agent : Agent S p) (server : Lens p y)\n    (n : Nat) (s : S) : (trace agent server n s).length = n := by sorry"
  match ← Aristotle.reverify env "open Poly" sorried (some requestedStatement) with
  | .unsoundAxioms axs =>
    IO.println s!"  ok    a sorry'd 'proof' of the same goal is rejected ({axs.toList.map toString})"
  | o =>
    IO.println s!"  FAIL  sorry'd candidate was not rejected: {repr o}"; failed := failed + 1

  if failed == 0 then
    IO.println "  Aristotle round trip verified offline"
    return 0
  else
    IO.println s!"  {failed} Aristotle checks FAILED"
    return 1

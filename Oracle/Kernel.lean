import Lean

/-!
# The oracle

The only trusted component in the system. Everything that *produces* candidate proofs
— Aristotle, a tactic search — is untrusted; this module decides what counts
as established.

Three gates, in order:

1. **Elaboration.** The candidate is elaborated by the real Lean frontend. Not a
   subprocess: `Lean.Elab.process` takes an existing `Environment` and returns the new
   environment plus the message log, so the base environment (Mathlib, once) is
   imported at startup and reused for every candidate.

2. **Axiom audit.** `Lean.collectAxioms` reports what the accepted term *transitively*
   depends on, and anything outside `axiomWhitelist` is rejected.

   This is the gate that replaces v1's substring blacklist
   (`v1-idris/src/MCP/Proof.idr`, `forbiddenTokens`). The difference is not cosmetic.
   A blacklist only catches the escape hatches someone thought to list; the audit
   catches every one, including those introduced *indirectly*. `sorry` is the clearest
   case: it emits a **warning**, not an error, so gate 1 passes it happily — and it is
   caught here because it leaves `sorryAx` in the axiom set.

   `native_decide` is the sharper example. Measured on this toolchain it mints a
   *per-declaration* axiom — `cand._native.native_decide.ax_1` — whose name varies with
   the declaration being proved. A name-based gate would need a name it cannot know in
   advance; the whitelist needs to know nothing, and `native_decide` is named nowhere in
   this file.

3. **Statement match.** Elaboration proving *something* is not the same as proving
   what was asked. The check is `example : <requested> := <declName>`, which succeeds
   exactly when the candidate's type is defeq to the requested statement — kernel
   checked, and stronger than comparing syntax.

   v1 had no equivalent, and its README documents the consequence honestly: asked for
   a false statement, the model silently proved the *negation* and reported success.
   That specific failure is caught here.
-/

namespace Oracle

open Lean Lean.Elab

/-- The axioms a proof is permitted to depend on: the three that Lean's own standard
library is built on. Anything else — `sorryAx`, `Lean.ofReduceBool`, a user-declared
`axiom` — fails the audit. -/
def axiomWhitelist : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- What verification can conclude. Every failure carries evidence: the caller sees
either the accepted term's axiom set, or exactly what went wrong. -/
inductive Outcome where
  /-- Elaborated, audited, and (if a statement was supplied) matched it. -/
  | checked (axioms : Array Name)
  /-- The candidate does not elaborate. Carries Lean's own diagnostic, verbatim. -/
  | elabFailed (diagnostics : String)
  /-- Elaborated, but did not define the declaration it was supposed to. -/
  | missingDecl (declName : Name)
  /-- Elaborated, but depends on axioms outside the whitelist. -/
  | unsoundAxioms (axioms : Array Name)
  /-- Elaborated and audited, but proves a different statement than the one asked for. -/
  | statementMismatch (diagnostics : String)
  /-- The *requested* statement is itself ill-formed in this context, so no comparison
  is meaningful. Kept distinct from `statementMismatch`: conflating them would let a
  harness bug (a missing `open`, a typo in the goal) masquerade as "the prover proved
  the wrong thing", which is exactly the kind of false confidence this module exists to
  prevent. -/
  | badStatement (diagnostics : String)
  deriving Repr, Inhabited, BEq

/-- `collectAxioms` asks only for `MonadEnv`, so it needs no elaboration context and
no `IO` — a bare state monad over the environment is enough, and keeps the audit as
small and inspectable as the thing it is auditing. -/
abbrev EnvM := StateM Environment

instance : MonadEnv EnvM where
  getEnv := get
  modifyEnv f := modify f

/-- The axioms `declName` transitively depends on, in `env`. -/
def axiomsOf (env : Environment) (declName : Name) : Array Name :=
  (collectAxioms (m := EnvM) declName).run' env

/-- Errors from a message log, formatted as Lean prints them. Warnings are dropped:
they are not failures, and the one warning that *matters* (`declaration uses 'sorry'`)
is caught by the axiom audit instead, which is the point. -/
def errorText (log : MessageLog) : IO String := do
  let errs := log.toList.filter (·.severity matches .error)
  let strs ← errs.mapM (·.toString)
  return "\n".intercalate strs

/-- Build the base environment once. Callers pass e.g. `#[`Mathlib]`; the cost is paid
here rather than per candidate.

`loadExts := true` is essential and easy to miss: notation, instances and syntax all
live in environment extensions, and without it the environment cannot even *parse*
`n + 0` — `+` is not a token. Loading extensions runs module initializers, which
requires `enableInitializersExecution`, which is `unsafe`; it is confined here so the
rest of the oracle stays safe code. -/
unsafe def mkBaseEnvImpl (imports : Array Name) : IO Environment := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  importModules (imports.map fun m => { module := m }) {} (trustLevel := 0) (loadExts := true)

@[implemented_by mkBaseEnvImpl]
opaque mkBaseEnv (imports : Array Name) : IO Environment

/-- What to verify. -/
structure Request where
  /-- Lines prepended to the candidate *and* to the statement probes — typically `open`
  commands. This must be separate from `source`, because each `Lean.Elab.process` call
  is its own command sequence: an `open CategoryTheory in` inside `source` scopes to the
  next command only and does not reach the probe, which would make every Mathlib-flavoured
  statement fail to parse and be reported as a mismatch. -/
  preamble : String := ""
  /-- Source defining `declName`. -/
  source : String
  /-- The declaration the candidate is required to produce. -/
  declName : Name := `cand
  /-- If present, the statement `declName` must prove, as Lean source. -/
  expected? : Option String := none

/--
Verify one candidate.

Order matters: the axiom audit runs **before** the statement match, so a `sorry`-ed
proof of exactly the right statement is still rejected, and rejected for the right
reason.

The statement check is two probes, not one. The first asks whether the *requested*
statement is well-formed at all (proved by `sorry`, whose axiom we do not care about
here — nothing from this probe is ever accepted as evidence). Only if that succeeds
does the second probe ask whether the candidate inhabits it. Without the split, a
missing `open` in the request looks identical to the prover having proved the wrong
theorem.
-/
def verify (baseEnv : Environment) (req : Request) : IO Outcome := do
  let candidateSrc := req.preamble ++ "\n" ++ req.source
  let (env, log) ← Lean.Elab.process candidateSrc baseEnv {} "<candidate>"
  if log.hasErrors then
    return .elabFailed (← errorText log)
  if (env.find? req.declName).isNone then
    return .missingDecl req.declName
  let axioms := axiomsOf env req.declName
  let unsound := axioms.filter (!axiomWhitelist.contains ·)
  if !unsound.isEmpty then
    return .unsoundAxioms unsound
  match req.expected? with
  | none => return .checked axioms
  | some stmt =>
    -- Probe 1: is the requested statement even a well-formed proposition here?
    let wf := req.preamble ++ "\n" ++ s!"example : {stmt} := by sorry"
    let (_, wfLog) ← Lean.Elab.process wf env {} "<statement-wellformed>"
    if wfLog.hasErrors then
      return .badStatement (← errorText wfLog)
    -- Probe 2: does the candidate actually inhabit it?
    let probe := req.preamble ++ "\n" ++ s!"example : {stmt} := {req.declName}"
    let (_, probeLog) ← Lean.Elab.process probe env {} "<statement-match>"
    if probeLog.hasErrors then
      return .statementMismatch (← errorText probeLog)
    return .checked axioms

end Oracle

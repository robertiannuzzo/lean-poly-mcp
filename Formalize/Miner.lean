import Oracle.Kernel

/-!
# Mathlib CategoryTheory miner

The benchmark in `Formalize.Benchmark` is hand-curated. This module is the other half of
that story: it turns Mathlib's `CategoryTheory.*` declarations into statement-shaped
data that can feed the same oracle/search/Aristotle pipeline.

It deliberately mines an already-loaded `Environment`; importing Mathlib remains the
caller's explicit cost. Tests and demos can therefore batch the import once and ask every
question they need in one run.
-/

namespace Formalize

open Lean

/-- The broad declaration class. This is evidence for filtering and display, not a
semantic claim about theoremhood. -/
inductive DeclKind where
  | theorem
  | axiom
  | definition
  | opaque
  | inductive
  | constructor
  | recursor
  | quotient
  deriving Repr, Inhabited, BEq

def DeclKind.toString : DeclKind → String
  | .theorem => "theorem"
  | .axiom => "axiom"
  | .definition => "definition"
  | .opaque => "opaque"
  | .inductive => "inductive"
  | .constructor => "constructor"
  | .recursor => "recursor"
  | .quotient => "quotient"

instance : ToString DeclKind := ⟨DeclKind.toString⟩

/-- One mined declaration, with its type rendered as Lean source. `statement` is what the
oracle consumes; `name` and `kind` explain where it came from. -/
structure MinedDecl where
  name : Name
  kind : DeclKind
  statement : String
  deriving Repr, Inhabited

/-- Defaults for the CategoryTheory corpus. -/
structure MinerConfig where
  namespacePrefix : String := "CategoryTheory."
  includeDefinitions : Bool := false
  includeInternal : Bool := false
  limit : Nat := 200
  deriving Repr

def kindOf : ConstantInfo → DeclKind
  | .axiomInfo _ => .axiom
  | .thmInfo _ => .theorem
  | .opaqueInfo _ => .opaque
  | .defnInfo _ => .definition
  | .ctorInfo _ => .constructor
  | .recInfo _ => .recursor
  | .inductInfo _ => .inductive
  | .quotInfo _ => .quotient

def DeclKind.isStatementLike : DeclKind → Bool
  | .theorem | .axiom => true
  | _ => false

def isInternalName (n : Name) : Bool :=
  let s := n.toString
  s.contains "_proof_" ||
  s.contains ".match_" ||
  s.contains "._match_" ||
  s.contains ".rec_" ||
  s.contains ".noConfusion" ||
  s.endsWith ".injEq"

def keepDecl (cfg : MinerConfig) (ci : ConstantInfo) : Bool :=
  let kind := kindOf ci
  ci.name.toString.startsWith cfg.namespacePrefix &&
    (cfg.includeInternal || !isInternalName ci.name) &&
    (kind.isStatementLike || cfg.includeDefinitions)

def prettyExpr (env : Environment) (e : Expr) : IO String := do
  let opts := ({ } : Options).setBool `pp.all true
  let ctx : Core.Context := { fileName := "<formalize-miner>", fileMap := default, options := opts }
  let state : Core.State := { env := env }
  let (fmt, _) ← (Meta.ppExpr e).run'.toIO ctx state
  return fmt.pretty

/-- Mine declarations from an already-imported environment.

The output is sorted by name so replay/demo artifacts do not depend on the hash-map
iteration order of Lean's environment. -/
def mine (env : Environment) (cfg : MinerConfig := {}) : IO (Array MinedDecl) := do
  let candidates := env.constants.fold
    (fun acc _ ci => if keepDecl cfg ci then acc.push ci else acc)
    (#[] : Array ConstantInfo)
  let sorted := candidates.qsort (fun a b => a.name.toString < b.name.toString)
  let capped := sorted.extract 0 (min cfg.limit sorted.size)
  capped.mapM fun ci => do
    let statement ← prettyExpr env ci.type
    pure { name := ci.name, kind := kindOf ci, statement := statement }

/-- Check whether a mined statement is well-formed as a standalone proposition in the
given preamble. This is intentionally weaker than proof verification: the proof is
`sorry`, and its axioms are ignored, because the only question here is whether the
statement string is usable corpus data. -/
def isWellFormedStatement (env : Environment) (preamble statement : String) : IO Bool := do
  let src := preamble ++ "\n" ++ s!"example : {statement} := by sorry"
  let (_, log) ← Lean.Elab.process src env {} "<mined-statement>"
  return !log.hasErrors

/-- Mine and keep only declarations whose rendered type is usable as a standalone Lean
statement in `preamble`. -/
def mineWellFormed (env : Environment) (cfg : MinerConfig := {})
    (preamble : String := "open CategoryTheory") : IO (Array MinedDecl) := do
  let decls ← mine env cfg
  let mut kept : Array MinedDecl := #[]
  for d in decls do
    if ← isWellFormedStatement env preamble d.statement then
      kept := kept.push d
  return kept

/-- Render a compact, paper-friendly table. -/
def renderTable (decls : Array MinedDecl) : String :=
  "\n".intercalate <| decls.toList.map fun d =>
    s!"{d.kind}\t{d.name}\t{d.statement}"

end Formalize

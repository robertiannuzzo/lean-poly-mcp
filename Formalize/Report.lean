import Formalize.Miner
import Tactics.Search

/-!
# Mined corpus report

This is the cheap source of better category-theory goals.

Instead of asking an LLM to invent lemmas, we mine existing `CategoryTheory.*`
declarations from Mathlib, render their types as statement strings, check that those
strings stand alone, and run the free tactic ladder. The useful output is the locally
unsolved slice: well-formed, real Mathlib statements that are plausible Aristotle
candidates.

The module imports no Mathlib at compile time. `runDefault` imports Mathlib once at
runtime, then batches all topics through that environment.
-/

namespace Formalize.Report

open Lean

/-- A semantic slice of Mathlib's CategoryTheory namespace. -/
structure Topic where
  label : String
  namespacePrefix : String
  deriving Repr, Inhabited

/-- Defaults chosen to avoid the alphabetic `AB4...` front of `CategoryTheory.*` and
sample the places that read like category theory in a paper. -/
def defaultTopics : List Topic :=
  [ ⟨"functors", "CategoryTheory.Functor."⟩
  , ⟨"natural transformations", "CategoryTheory.NatTrans."⟩
  , ⟨"isomorphisms", "CategoryTheory.Iso."⟩
  , ⟨"adjunctions", "CategoryTheory.Adjunction."⟩
  , ⟨"equivalences", "CategoryTheory.Equivalence."⟩
  , ⟨"yoneda", "CategoryTheory.yoneda"⟩
  , ⟨"limits", "CategoryTheory.Limits."⟩ ]

structure Config where
  perTopicLimit : Nat := 12
  maxTier : Nat := 1
  preamble : String := "open CategoryTheory"
  deriving Repr

inductive Verdict where
  | solved (tier : Nat) (tactic : String) (axioms : Array Name)
  | unsolved (tried : List String)
  | unusable
  deriving Repr, Inhabited

structure Entry where
  topic : Topic
  decl : MinedDecl
  verdict : Verdict
  ms : Nat
  deriving Repr

def Verdict.isSolved : Verdict → Bool
  | .solved .. => true
  | _ => false

def Verdict.isUnsolved : Verdict → Bool
  | .unsolved _ => true
  | _ => false

def verdictSummary : Verdict → String
  | .solved tier tac axioms =>
    let ax := if axioms.isEmpty then "no axioms" else s!"{axioms.toList.map toString}"
    s!"solved tier {tier} by `{tac}` ({ax})"
  | .unsolved tried => s!"MISS after {tried.length} local tactics"
  | .unusable => "unusable statement"

def analyzeDecl (env : Environment) (cfg : Config) (topic : Topic) (decl : MinedDecl) :
    IO Entry := do
  let t0 ← IO.monoMsNow
  let verdict ←
    if ← Formalize.isWellFormedStatement env cfg.preamble decl.statement then
      match ← Tactics.search env cfg.preamble decl.statement cfg.maxTier with
      | .solved tier tac axioms => pure (.solved tier tac axioms)
      | .unsolved tried => pure (.unsolved tried)
    else
      pure .unusable
  let t1 ← IO.monoMsNow
  return { topic := topic, decl := decl, verdict := verdict, ms := t1 - t0 }

def analyzeTopic (env : Environment) (cfg : Config) (topic : Topic) : IO (Array Entry) := do
  let mined ← Formalize.mine env
    { namespacePrefix := topic.namespacePrefix, limit := cfg.perTopicLimit,
      includeDefinitions := false, includeInternal := false }
  mined.mapM (analyzeDecl env cfg topic)

def analyzeTopics (env : Environment) (cfg : Config) (topics : List Topic := defaultTopics) :
    IO (Array Entry) := do
  let mut out : Array Entry := #[]
  for topic in topics do
    out := out ++ (← analyzeTopic env cfg topic)
  return out

def countWhere (entries : Array Entry) (p : Entry → Bool) : Nat :=
  entries.foldl (fun n e => if p e then n + 1 else n) 0

def renderEntry (e : Entry) : String :=
  s!"  {e.topic.label} · {e.decl.name} [{e.ms} ms]\n" ++
  s!"    {verdictSummary e.verdict}\n" ++
  s!"    {e.decl.statement}"

def renderReport (entries : Array Entry) (showStatements : Bool := false) : String :=
  let total := entries.size
  let solved := countWhere entries (·.verdict.isSolved)
  let unsolved := countWhere entries (·.verdict.isUnsolved)
  let unusable := countWhere entries (fun e => e.verdict matches .unusable)
  let header :=
    s!"mined corpus report\n" ++
    s!"  total:    {total}\n" ++
    s!"  solved:   {solved}\n" ++
    s!"  misses:   {unsolved}\n" ++
    s!"  unusable: {unusable}\n"
  let misses := entries.filter (·.verdict.isUnsolved)
  let solvedEntries := entries.filter (·.verdict.isSolved)
  let lines :=
    if showStatements then
      "\ninteresting misses\n" ++ "\n\n".intercalate (misses.toList.map renderEntry) ++
      "\n\nlocal wins\n" ++ "\n\n".intercalate (solvedEntries.toList.map renderEntry)
    else
      "\ninteresting misses\n" ++
        "\n".intercalate (misses.toList.map fun e =>
          s!"  {e.topic.label}\t{e.decl.name}\t{verdictSummary e.verdict}") ++
      "\n\nlocal wins\n" ++
        "\n".intercalate (solvedEntries.toList.map fun e =>
          s!"  {e.topic.label}\t{e.decl.name}\t{verdictSummary e.verdict}")
  header ++ lines

def namesToJson (xs : Array Name) : Json :=
  Json.arr (xs.map (fun n => Json.str n.toString))

def verdictToJson : Verdict → Json
  | .solved tier tactic axioms => Json.mkObj
      [ ("outcome", Json.str "solved")
      , ("tier", Json.num tier)
      , ("tactic", Json.str tactic)
      , ("axioms", namesToJson axioms) ]
  | .unsolved tried => Json.mkObj
      [ ("outcome", Json.str "interesting_miss")
      , ("tried", Json.arr ((tried.map Json.str).toArray)) ]
  | .unusable => Json.mkObj
      [ ("outcome", Json.str "unusable") ]

def entryToJson (e : Entry) : Json :=
  Json.mkObj
    [ ("topic", Json.str e.topic.label)
    , ("name", Json.str e.decl.name.toString)
    , ("kind", Json.str e.decl.kind.toString)
    , ("statement", Json.str e.decl.statement)
    , ("ms", Json.num e.ms)
    , ("verdict", verdictToJson e.verdict)
    , ("summary", Json.str (verdictSummary e.verdict)) ]

def reportToJson (importMs : Nat) (entries : Array Entry) : Json :=
  Json.mkObj
    [ ("importMs", Json.num importMs)
    , ("total", Json.num entries.size)
    , ("solved", Json.num (countWhere entries (·.verdict.isSolved)))
    , ("misses", Json.num (countWhere entries (·.verdict.isUnsolved)))
    , ("unusable", Json.num (countWhere entries (fun e => e.verdict matches .unusable)))
    , ("entries", Json.arr (entries.map entryToJson)) ]

def parseNat? (s : String) : Option Nat :=
  s.toNat?

def configFromArgs (args : List String) : Config :=
  let rec go (cfg : Config) : List String → Config
    | "--limit" :: n :: rest => go { cfg with perTopicLimit := (parseNat? n).getD cfg.perTopicLimit } rest
    | "--max-tier" :: n :: rest => go { cfg with maxTier := (parseNat? n).getD cfg.maxTier } rest
    | _ :: rest => go cfg rest
    | [] => cfg
  go {} args

def runDefault (args : List String := []) : IO UInt32 := do
  let cfg := configFromArgs args
  let t0 ← IO.monoMsNow
  let env ← Oracle.mkBaseEnv #[`Mathlib]
  let t1 ← IO.monoMsNow
  let entries ← analyzeTopics env cfg
  if args.contains "--json" then
    IO.println (reportToJson (t1 - t0) entries).compress
  else
    IO.println s!"  [{t1 - t0} ms] import Mathlib (once)"
    IO.println (renderReport entries (showStatements := args.contains "--statements"))
  return 0

end Formalize.Report

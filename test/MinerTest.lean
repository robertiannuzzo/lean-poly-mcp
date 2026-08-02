import Formalize.Report

/-!
# Miner test

Full-sweep only: imports Mathlib once, mines a small `CategoryTheory` slice, and checks
that the mined statement strings are well-formed Lean propositions in the same
environment the oracle uses.
-/

open Lean Formalize

def main : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let env ← Oracle.mkBaseEnv #[`Mathlib]
  let t1 ← IO.monoMsNow
  IO.println s!"  [{t1 - t0} ms] import Mathlib (once)"

  let raw ← Formalize.mine env { limit := 80 }
  let decls ← Formalize.mineWellFormed env { limit := 80 }
  let hasCategory := raw.any (fun d => d.name.toString.startsWith "CategoryTheory.")
  let hasStatement := decls.any (fun d => d.statement.contains "Category")
  if raw.isEmpty || decls.isEmpty || !hasCategory || !hasStatement then
    IO.println s!"  FAIL  miner returned an implausible corpus of size raw={raw.size}, wellformed={decls.size}"
    return 1

  let sample := decls.extract 0 (min 8 decls.size)
  let mut failed := 0
  for d in sample do
    match ← Oracle.verify env
        { preamble := "open CategoryTheory", source := "theorem cand : True := trivial",
          expected? := some d.statement } with
    | .badStatement msg =>
      IO.println s!"  FAIL  mined statement is not well-formed: {d.name}"
      IO.println s!"        {(msg.splitOn "\n").headD ""}"
      failed := failed + 1
    | _ =>
      IO.println s!"  ok    mined {d.kind}: {d.name}"

  if failed != 0 then
    IO.println s!"  {failed} mined statements were ill-formed"
    return 1
  IO.println s!"  miner produced {decls.size} CategoryTheory declarations"

  let entries ← Formalize.Report.analyzeTopics env
    { perTopicLimit := 1, maxTier := 0 }
    [ ⟨"functors", "CategoryTheory.Functor."⟩
    , ⟨"yoneda", "CategoryTheory.yoneda"⟩ ]
  let rendered := Formalize.Report.renderReport entries
  if entries.isEmpty || !(rendered.contains "mined corpus report") then
    IO.println "  FAIL  corpus report smoke test returned no report"
    return 1
  IO.println s!"  report smoke test analyzed {entries.size} mined statements"
  return 0

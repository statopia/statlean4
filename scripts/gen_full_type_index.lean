import Mathlib

/-! # Generate Full Mathlib Type Index (TSV)

Run with: `lake env lean scripts/gen_full_type_index.lean > theme/mathlib_full_type_index.tsv`

Produces a tab-separated file: NAME\tKIND
for ALL Mathlib declarations (excluding internal/auto-generated).

This enables instant offline API lookup:
  grep 'variance' theme/mathlib_full_type_index.tsv
  grep -i 'condexp' theme/mathlib_full_type_index.tsv
  grep 'Integrable' theme/mathlib_full_type_index.tsv
-/

open Lean in
#eval show Elab.Command.CommandElabM Unit from do
  let env ← getEnv

  -- Blacklist: internal / auto-generated names
  let blacklist := #[
    "._", ".proof_", ".match_", ".eq_", ".noConfusion",
    "casesOn", "recOn", "below", "brecOn", "binductionOn",
    "injEq", "sizeOf", "toCtorIdx", ".brecOn",
    "._unary", "._mutual", ".extHelp",
    ".mk.sizeOf_spec", ".ndrec", ".ndrecOn",
    ".rec.", "._sizeOf_", ".autoParam"
  ]
  let isBlacklisted (s : String) : Bool :=
    blacklist.any (s.containsSubstr ·)

  -- Only include relevant mathematical namespaces
  let relevantPrefixes := #[
    "MeasureTheory.", "ProbabilityTheory.",
    "Analysis.", "Topology.", "Order.", "Filter.",
    "Set.", "Finset.", "ENNReal.", "NNReal.", "Real.",
    "Complex.", "Nat.", "Int.", "Metric.",
    "MeasurableSpace.", "Measure.",
    "Mathlib.", "InnerProductSpace.", "NormedSpace.",
    "BoundedContinuousFunction.", "ContinuousMap.",
    "EMetricSpace.", "MetricSpace."
  ]
  let isRelevant (s : String) : Bool :=
    relevantPrefixes.any (s.startsWith ·)

  -- Header
  IO.println "NAME\tKIND"

  let ref ← IO.mkRef (α := Array (String × String)) #[]

  env.constants.forM fun name ci => do
    let s := name.toString
    if !isBlacklisted s && isRelevant s then
      let kind := match ci with
        | .thmInfo _ => "thm"
        | .defnInfo _ => "def"
        | .axiomInfo _ => "ax"
        | .opaqueInfo _ => "opq"
        | .ctorInfo _ => "ctor"
        | .recInfo _ => "rec"
        | .quotInfo _ => "quot"
        | .inductInfo _ => "ind"
      ref.modify (·.push (s, kind))

  let entries ← ref.get
  let sorted := entries.qsort (fun a b => a.1 < b.1)
  for (n, k) in sorted do
    IO.println s!"{n}\t{k}"

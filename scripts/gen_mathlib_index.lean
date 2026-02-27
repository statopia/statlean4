import Mathlib

/-! # Generate Mathlib API Index

Run with: `lake env lean scripts/gen_mathlib_index.lean`

Extracts theorem/def names from Mathlib namespaces relevant to StatLean,
grouped by topic. Output goes to stdout; redirect to `theme/mathlib_api_index.md`.
-/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv

  -- ── Blacklist: internal / auto-generated names ──
  let blacklist := #[
    "._", ".proof_", ".match_", ".eq_", ".noConfusion",
    "casesOn", "recOn", "below", "brecOn", "binductionOn",
    "injEq", "sizeOf", "toCtorIdx"
  ]
  let isBlacklisted (s : String) : Bool :=
    blacklist.any (s.containsSubstr ·)

  -- ── Helper: emit a section (sorted) ──
  let emitSection (title : String) (prefixes : Array String)
      (extra_blacklist : Array String := #[]) : CommandElabM Unit := do
    IO.println s!"## {title}"
    IO.println "```"
    let ref ← IO.mkRef (α := Array String) #[]
    env.constants.forM fun name _ci => do
      let s := name.toString
      let matchesPrefix := prefixes.any (s.startsWith ·)
      let extraBL := extra_blacklist.any (s.containsSubstr ·)
      if matchesPrefix && !isBlacklisted s && !extraBL then
        ref.modify (·.push s)
    let names ← ref.get
    let sorted := names.qsort (· < ·)
    for n in sorted do
      IO.println n
    IO.println "```"
    IO.println ""

  -- ── Header ──
  IO.println "# Mathlib API Index for StatLean"
  IO.println ""
  IO.println "Auto-generated. Do not edit manually."
  IO.println "Regenerate: `lake env lean scripts/gen_mathlib_index.lean > theme/mathlib_api_index.md`"
  IO.println ""

  -- ── 1. Probability: variance, moments, MGF/CGF ──
  emitSection "Variance & Moments"
    #[ "ProbabilityTheory.variance",
       "ProbabilityTheory.evariance",
       "ProbabilityTheory.moment",
       "ProbabilityTheory.centralMoment" ]

  -- ── 2. MGF / CGF ──
  emitSection "MGF & CGF"
    #[ "ProbabilityTheory.mgf",
       "ProbabilityTheory.cgf" ]

  -- ── 3. Sub-Gaussian ──
  emitSection "Sub-Gaussian"
    #[ "ProbabilityTheory.HasSubgaussianMGF",
       "ProbabilityTheory.HasCondSubgaussianMGF" ]
    #[ ".rec", ".mk" ]

  -- ── 4. Characteristic functions ──
  emitSection "Characteristic Functions"
    #[ "ProbabilityTheory.charFun",
       "ProbabilityTheory.charFunDual",
       "ProbabilityTheory.norm_charFun",
       "ProbabilityTheory.measureReal_abs_gt_le_integral_charFun" ]

  -- ── 5. Independence & IdentDistrib ──
  emitSection "Independence"
    #[ "ProbabilityTheory.IndepFun.",
       "ProbabilityTheory.iIndepFun" ]

  emitSection "IdentDistrib"
    #[ "ProbabilityTheory.IdentDistrib" ]
    #[ ".rec", ".mk" ]

  -- ── 6. Conditional expectation & variance ──
  emitSection "Conditional Expectation"
    #[ "MeasureTheory.condExp_" ]

  emitSection "Conditional Variance"
    #[ "ProbabilityTheory.condVar" ]

  -- ── 7. Gaussian ──
  emitSection "Gaussian Measure & Distribution"
    #[ "MeasureTheory.Measure.gaussianReal",
       "MeasureTheory.integral_gaussian",
       "ProbabilityTheory.IsGaussian",
       "ProbabilityTheory.Hermite",
       "MeasureTheory.gaussianPDF",
       "MeasureTheory.deriv_gaussian",
       "MeasureTheory.hasDerivAt_gaussian" ]
    #[ ".rec", ".mk" ]

  -- ── 8. MemLp & integrability ──
  emitSection "MemLp (key methods)"
    #[ "MeasureTheory.MemLp.mono",
       "MeasureTheory.MemLp.integrable",
       "MeasureTheory.MemLp.norm",
       "MeasureTheory.MemLp.add",
       "MeasureTheory.MemLp.sub",
       "MeasureTheory.MemLp.mul",
       "MeasureTheory.MemLp.neg",
       "MeasureTheory.MemLp.smul",
       "MeasureTheory.MemLp.const_mul",
       "MeasureTheory.MemLp.ofReal",
       "MeasureTheory.memLp_finset_sum",
       "MeasureTheory.memLp_one_iff",
       "MeasureTheory.memLp_top" ]

  -- ── 9. Integral lemmas ──
  emitSection "Integral (key lemmas)"
    #[ "MeasureTheory.integral_map",
       "MeasureTheory.integral_mul",
       "MeasureTheory.integral_add",
       "MeasureTheory.integral_sub",
       "MeasureTheory.integral_neg",
       "MeasureTheory.integral_smul",
       "MeasureTheory.integral_const",
       "MeasureTheory.integral_mono",
       "MeasureTheory.integral_nonneg",
       "MeasureTheory.integral_norm",
       "MeasureTheory.integral_complex",
       "MeasureTheory.integral_withDensity",
       "MeasureTheory.integral_dirac",
       "MeasureTheory.integral_indicator",
       "MeasureTheory.integral_finset",
       "MeasureTheory.integral_prod",
       "MeasureTheory.integral_condExp",
       "MeasureTheory.setIntegral_condExp" ]

  -- ── 10. Measure.map ──
  emitSection "Measure.map"
    #[ "MeasureTheory.Measure.map_map",
       "MeasureTheory.Measure.map_apply",
       "MeasureTheory.Measure.map_dirac" ]

  -- ── 11. Complex exponential bounds ──
  emitSection "Complex Exponential Bounds"
    #[ "Complex.norm_exp",
       "Complex.abs_exp",
       "Complex.exp_bound",
       "Complex.I_sq" ]

  -- ── 12. Real exponential bounds ──
  emitSection "Real Exponential & Log Bounds"
    #[ "Real.exp_bound",
       "Real.abs_exp",
       "Real.exp_log",
       "Real.log_exp",
       "Real.add_one_le_exp",
       "Real.one_sub_div_pow_le_exp_neg",
       "abs_pow_sub_pow_le" ]

  -- ── 13. Convexity / Jensen ──
  emitSection "Convexity & Jensen"
    #[ "ConvexOn.map_integral",
       "ConvexOn.inner_smul",
       "convexOn_rpow",
       "convexOn_pow",
       "StrictConvexOn.map_integral" ]

  -- ── 14. Polynomial derivatives ──
  emitSection "Polynomial Derivatives"
    #[ "Polynomial.hasDerivAt",
       "Polynomial.derivative",
       "Polynomial.aeval_map" ]
    #[ "Polynomial.derivative_X", "Polynomial.derivative_C",
       "Polynomial.derivative_one", "Polynomial.derivative_zero",
       "Polynomial.derivative_bit" ]

  -- ── 15. IBP ──
  emitSection "Integration by Parts"
    #[ "MeasureTheory.integral_mul_deriv",
       "intervalIntegral.integral_mul_deriv" ]

  -- ── 16. Grönwall ──
  emitSection "Grönwall"
    #[ "gronwallBound",
       "norm_le_gronwallBound" ]

  -- ── 17. Tilted measures ──
  emitSection "Tilted Measures"
    #[ "ProbabilityTheory.integral_tilted",
       "ProbabilityTheory.variance_tilted",
       "ProbabilityTheory.tilted" ]

  -- ── 18. Smooth density in Lp ──
  emitSection "Smooth Density in Lp"
    #[ "MeasureTheory.Lp.dense_hasCompactSupport" ]

  IO.println "<!-- End of auto-generated index -->"

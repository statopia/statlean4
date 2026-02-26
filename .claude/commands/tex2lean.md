---
description: Convert LaTeX theorem to Lean 4 skeleton
allowed-tools: Read, Write, Edit, Grep, Glob, Bash(lake:*), Task, WebSearch
model: opus
argument-hint: [theorem-id or LaTeX snippet]
---

# LaTeX to Lean 4 Translation

Input: $ARGUMENTS

## Protocol

### Phase 1: Parse the mathematical statement
1. If a theorem ID is given, find it in `output.tex` or the relevant LaTeX source.
2. Extract: hypotheses, conclusion, notation, referenced definitions.
3. Identify the mathematical objects: measure spaces, random variables, function spaces, norms, etc.

### Phase 2: Map to Mathlib types
For each mathematical concept, find the Lean 4 / Mathlib equivalent:
- Probability measure → `[MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]`
- Random variable X ∈ L² → `(X : Ω → ℝ) (hX : MemLp X 2 μ)`
- E[X] → `∫ x, X x ∂μ` (Bochner integral)
- Var[X] → `variance X μ`
- E[X|G] → `μ[X|G]` (condExp)
- σ-algebra → `MeasurableSpace` or sub-sigma-algebra `(m : MeasurableSpace Ω) (hm : m ≤ m0)`
- Product measure → `μ.prod ν` or `Measure.pi`
- Lipschitz → `LipschitzWith K f`
- ‖·‖ → `‖·‖` (NormedAddCommGroup)
- a.s. equality → `=ᵐ[μ]`
- Gaussian → check if `MeasureTheory.Measure.gaussianReal` exists

### Phase 3: Generate skeleton
Create a Lean 4 declaration with:
- Proper imports (check what the project already imports)
- Type-correct statement (hypotheses as explicit arguments)
- `sorry` as proof placeholder
- Module docstring referencing the LaTeX theorem number

### Phase 4: Verify compilation
- Place the skeleton in the appropriate file under `Statlean/`
- Run `lake build <module>` to verify it compiles (with sorry)
- Fix any type errors

### Phase 5: Output
Report the generated skeleton and where it was placed.

## Naming convention
- Theorem names: `snake_case` matching the mathematical content
- Files: match the chapter/section structure of the paper
- Imports: use existing `Statlean.Concentration.Basic` definitions when available

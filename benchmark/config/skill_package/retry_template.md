The previous proof attempt failed with the following compilation error:

```
{error}
```

Please fix the proof. Here are common fixes for frequent errors:

- **unknown identifier**: Check exact Mathlib API name. Common confusions:
  - `condExp_sub` → `condExp_sub'` (different integrability assumptions)
  - `integral_mul` → `integral_mul_left` or `integral_mul_right`
  - `Measure.map_apply` needs `MeasurableSet` argument

- **type mismatch**: Check if you need:
  - `ENNReal.toReal` / `ENNReal.ofReal` conversion
  - `.ae` or `.filter_mono` to change the filter
  - `MeasureTheory.` prefix for ambiguous names

- **failed to synthesize instance**: You may need:
  - `haveI : IsProbabilityMeasure μ := ...`
  - `haveI : SigmaFinite μ := ...`
  - `@foo α _ inst ...` with explicit instance

- **tactic failed**: Try:
  - `simp only [Pi.pow_apply]` before `ring`
  - `convert` instead of `exact` when types are definitionally but not syntactically equal
  - `ext` to reduce function equality to pointwise

Provide the corrected proof body (everything after `:= by`), wrapped in a ```lean code block.

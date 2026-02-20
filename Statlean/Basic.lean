/-! # StatLean — Statistical Learning Theory in Lean 4

This library formalizes results from the paper:
> **"Statistical Learning Theory in Lean 4"**
> Zhang, Lee, Liu (2026) — arXiv:2602.02285

## Module structure

* `Statlean.Concentration` — Efron-Stein, Gaussian Poincaré, LSI, Lipschitz concentration
* `Statlean.EmpiricalProcess` — Covering numbers, Dudley's entropy integral
* `Statlean.Regression` — Least-squares regression, master error bound

## Conventions

All measures are assumed to be probability measures unless otherwise noted.
The standard Gaussian `γ = N(0,1)` is defined in `Statlean.Concentration.GaussianPoincare`.
-/

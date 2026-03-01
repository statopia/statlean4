/-! # StatLean — Statistical Learning Theory in Lean 4

This library formalizes results from the paper:
> **"Statistical Learning Theory in Lean 4"**
> Zhang, Lee, Liu (2026) — arXiv:2602.02285

## Module structure

* `Statlean.Gaussian` — Standard Gaussian, Stein identity, Hermite, Poincaré
* `Statlean.Variance` — Rao-Blackwell, Efron-Stein, ANOVA
* `Statlean.Entropy` — Entropy, log-Sobolev inequality
* `Statlean.SubGaussian` — Herbst argument, Lipschitz concentration
* `Statlean.CharFun` — Characteristic function Taylor bounds
* `Statlean.LimitTheorems` — Berry-Esseen CLT, Uniform SLLN, convergence modes
* `Statlean.Sufficiency` — Factorization, Basu, Lehmann-Scheffé, minimal sufficiency
* `Statlean.Estimator` — MSE decomposition, MLE invariance, risk dominance
* `Statlean.Statistic` — ParametricFamily, IsUnbiased
* `Statlean.Information` — Fisher information, Cramér-Rao
* `Statlean.EmpiricalProcess` — Covering numbers, Dudley's entropy integral
* `Statlean.Regression` — Least-squares regression, master error bound
* `Statlean.SPD` — Log-Cholesky Fréchet mean

## Conventions

All measures are assumed to be probability measures unless otherwise noted.
The standard Gaussian `γ = N(0,1)` is defined in `Statlean.Gaussian.Basic`.
-/

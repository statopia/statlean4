# StatLean — Statistical Learning Theory in Lean 4

A Lean 4 formalization of the paper:

> **"Statistical Learning Theory in Lean 4"**
> Zhang, Lee, Liu (2026) — arXiv:2602.02285

## Project Structure

```
Statlean/
├── RaoBlackwell_MSE.lean          -- [COMPLETE] Rao-Blackwell MSE theorem
├── Concentration/
│   ├── Basic.lean                 -- Shared definitions (sigmaAlgExcept, condExpExceptCoord)
│   ├── EfronStein.lean            -- Efron-Stein inequality (Theorem 3.1)
│   ├── GaussianPoincare.lean      -- Gaussian Poincaré inequality (Corollary 3.2)
│   ├── Density.lean               -- Density of C_c^∞ in W^{1,2}(γ) (Theorem 3.3)
│   ├── LogSobolev.lean            -- Gaussian Log-Sobolev inequality (Theorems 3.5–3.6)
│   └── GaussianLipschitz.lean     -- Gaussian Lipschitz concentration (Theorem 3.7)
├── EmpiricalProcess/
│   ├── CoveringNumber.lean        -- Covering numbers and metric entropy
│   └── Dudley.lean                -- Dudley entropy integral (Theorem 3.8)
└── Regression/
    ├── Basic.lean                 -- Least-squares regression setup
    ├── MasterBound.lean           -- Master error bound (Theorems 4.1–4.2)
    └── Linear.lean                -- Linear/ℓ₁-constrained regression (Theorems 4.3–4.5)
```

## Proof Status

| Theorem | Paper | Status |
|---------|-------|--------|
| Rao-Blackwell MSE reduction | — | ✅ Complete (zero sorry) |
| Efron-Stein inequality | Thm 3.1 | ⚠️ Core step `Var[f] ≤ Σ E[Var[f\|Gᵢ]]` needs proof |
| Gaussian Poincaré | Cor 3.2 | ⚠️ 1D case needs proof via Stein/spectral gap |
| C_c^∞ density in W^{1,2}(γ) | Thm 3.3 | ⚠️ Mollification convergence needed |
| Lipschitz mollification | Lem 3.4 | ⚠️ Same |
| Gaussian LSI | Thm 3.5 | ⚠️ Depends on Poincaré + Rothaus-Simon |
| LSI tensorization | Thm 3.6 | ⚠️ Depends on 1D LSI |
| Gaussian Lipschitz concentration | Thm 3.7 | ⚠️ Herbst ODE argument needed; integrability ✅ |
| Dudley entropy integral | Thm 3.8 | ⚠️ Chaining argument needed |
| Master error bound | Thm 4.1 | ⚠️ Proven with trivial 4M² bound |
| Covering number bound | Thm 4.4 | ⚠️ Finiteness ✅; volumetric bound d·log(1+2R/ε) needed |
| Maurey ℓ₁ covering | Lem 4.5 | ⚠️ Stub |

**Legend**: ✅ = fully proven, ⚠️ = partial/stub

## Key Mathematical Gaps

### 1. Efron-Stein core (highest priority)
The inequality `Var[f(X₁,...,Xₙ)] ≤ Σᵢ E[Var[f|G_i^except]]` for independent variables.

Proof sketch via martingale telescoping:
- `f - E[f] = Σₖ Dₖ` where `Dₖ = E[f|F_k] - E[f|F_{k-1}]`
- Orthogonality: `Var[f] = Σₖ E[Dₖ²]`
- Key Jensen step: `Var[E_B[f(A,B)]] ≤ E_B[Var_A[f(A,B)]]` for independent A,B
- Combine to get each `E[Dₖ²] ≤ E[Var[f|G_k^except]]`

### 2. 1D Gaussian Poincaré
For γ = N(0,1): `Var_γ[f] ≤ E_γ[(f')²]`.
Proof via Stein's identity + integration by parts, or via Hermite expansion.

### 3. Herbst argument
From LSI(c) for f L-Lipschitz: `log E[e^{s(f-Ef)}] ≤ s²L²c/2`.
Proof via ODE comparison (Gronwall-type argument).

### 4. Volumetric covering number bound
`log N(ε, B₂ᵈ(R)) ≤ d · log(1 + 2R/ε)`.
Proof via volume comparison (packing ⊆ expanded ball).

## Setup

```bash
lake build
```

Requires [elan](https://github.com/leanprover/elan) with Lean 4.28.0-rc1.

## GitHub Actions

The repo is configured with GitHub Pages. See Settings → Pages → Source: GitHub Actions.

## Related

- Mathlib4: conditional expectation, variance, martingale theory, sub-Gaussian MGF
- Tag `v1`: Rao-Blackwell proof (first milestone)

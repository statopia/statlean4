# StatLean — Statistical Learning Theory in Lean 4

Lean 4 formalization of core results from:

> **"Statistical Learning Theory in Lean 4"**
> Zhang, Lee, Liu (2026) — arXiv:2602.02285

## Project Structure

```
Statlean/
  Gaussian/
    Basic.lean              # stdGaussian, integrability infrastructure
    Stein.lean              # Stein identity
    Hermite.lean            # IBP, orthogonality, density (zero sorry)
    Poincare.lean           # 1D Poincare + multi-dim condVar bound
  Variance/
    ANOVA.lean              # Jensen sq, ANOVA two-factor (zero sorry)
    RaoBlackwell.lean       # MSE theorem + variants
    EfronStein.lean         # Efron-Stein inequality
  Entropy/
    Basic.lean              # entropy, condEntropy, Jensen nonneg
    LogSobolev.lean         # Gross regularization lemmas + LSI
  SubGaussian/
    Herbst.lean             # sub-Gaussian MGF
    Lipschitz.lean          # concentration theorems
  CharFun/
    Taylor.lean             # charfun Taylor chain (zero sorry)
  LimitTheorems/
    USLLN.lean              # uniform SLLN (zero sorry)
    BerryEsseen.lean        # Berry-Esseen theorem
  Sufficiency/
    Factorization.lean      # Fisher-Neyman factorization (zero sorry)
    Basu.lean               # Basu's theorem (zero sorry)
  Verified.lean             # imports only zero-sorry modules
```

~170 declarations, 10 sorry across 5 files.

## Zero-sorry modules

Hermite, ANOVA, CharFun.Taylor, USLLN, Factorization, Basu

## Setup

```bash
lake build
```

Requires [elan](https://github.com/leanprover/elan) with Lean 4.28.0-rc1.

## Pipeline

See [theme/PIPELINE.md](theme/PIPELINE.md) for the full PDF-to-proof pipeline.

## Sorry backlog

See [theme/input/sorry_backlog.yaml](theme/input/sorry_backlog.yaml) for tracked proof obligations.

## Tag history

- `v1`: Rao-Blackwell MSE proof (first milestone)

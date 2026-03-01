-- Core
import Statlean.Basic

-- Gaussian infrastructure (verified)
import Statlean.Gaussian.Basic
import Statlean.Gaussian.Stein
import Statlean.Gaussian.Hermite

-- Variance (verified)
import Statlean.Variance.ANOVA
import Statlean.Variance.RaoBlackwell
-- Note: Statlean.Variance.EfronStein has 2 sorry gaps (condVar/Jensen, core_gen)
-- The 16 proved declarations there are still usable but not imported here

-- Entropy definitions (verified)
import Statlean.Entropy.Basic

-- Characteristic function Taylor bounds (verified)
import Statlean.CharFun.Taylor

-- USLLN (fully verified — uniform SLLN + all infrastructure)
import Statlean.LimitTheorems.USLLN

-- Sufficiency (fully verified — Factorization + Basu + MinimalSufficiency)
import Statlean.Sufficiency.Factorization
import Statlean.Sufficiency.Basu
import Statlean.Sufficiency.MinimalSufficiency

-- Estimation (verified — MSE decomposition, risk dominance, MLE)
import Statlean.Estimator.Basic
import Statlean.ExpFamily.Basic

-- Empirical process theory (verified)
import Statlean.EmpiricalProcess.CoveringNumber
import Statlean.EmpiricalProcess.Dudley

-- Fisher information and Cramér-Rao (verified)
import Statlean.Information.Basic
import Statlean.Information.CramerRao

-- Regression (verified)
import Statlean.Regression.Basic
import Statlean.Regression.Linear
import Statlean.Regression.MasterBound

-- SPD matrices (verified)
import Statlean.SPD.Determinant
import Statlean.SPD.FrechetMean
import Statlean.SPD.Geodesic

-- Statistics foundations (verified)
import Statlean.Statistic.Basic

-- Lehmann-Scheffé (verified)
import Statlean.Sufficiency.LehmannScheffe

/-! # Statlean Verified Library

**Every declaration reachable from this import is fully proved (zero sorry).**

This is the "clean" entry point for the StatLean library. It only imports
modules that have been verified to contain no sorry — neither directly
nor transitively through their dependency chains.

To check: `lake build Statlean.Verified` should produce zero sorry warnings.

## Contents

- **Gaussian/Basic**: stdGaussian, stdGaussianPi, integrability infrastructure
- **Gaussian/Stein**: Stein identity
- **Gaussian/Hermite**: Hermite derivative, orthogonality, Parseval, density, IBP
- **Variance/ANOVA**: Jensen squared, marginal L², ANOVA two-factor inequality
- **Variance/RaoBlackwell**: Rao-Blackwell MSE theorem and variants
- **Entropy/Basic**: Entropy definitions, LSI interfaces
- **CharFun/Taylor**: Charfun chain, Taylor bounds, Lyapunov (Berry-Esseen chain)
- **LimitTheorems/USLLN**: Uniform Strong Law of Large Numbers (full theorem + infrastructure)
- **Sufficiency/Factorization**: Fisher-Neyman factorization (both directions)
- **Sufficiency/Basu**: Basu's theorem
- **Sufficiency/MinimalSufficiency**: Density ratio criterion (Thm C) + Subfamily extension (Thm A)
- **Estimator/Basic**: MSE = Bias² + Var, unbiased MSE = Var, risk dominance,
  likelihood, IsMLE, MLE invariance (isMLE_comp)
- **ExpFamily/Basic**: MLE existence in natural exponential families
-/

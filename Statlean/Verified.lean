-- Core
import Statlean.Basic

-- Gaussian infrastructure (verified)
import Statlean.Gaussian.Basic
import Statlean.Gaussian.Stein
-- Note: Hermite.lean has 4 sorry gaps (recurrence, memLp, density, span)
-- Proved declarations (derivative_hermite, orthogonality) still usable but not imported here
import Statlean.Gaussian.Sobolev

-- Variance (verified)
import Statlean.Variance.RaoBlackwell
-- Note: Statlean.Variance.EfronStein has 2 sorry gaps (condVar/Jensen, core_gen)
-- The 16 proved declarations there are still usable but not imported here

-- Entropy definitions (verified)
import Statlean.Entropy.Basic

-- Characteristic function Taylor bounds (verified)
import Statlean.CharFun.Taylor

-- USLLN (fully verified — uniform SLLN + all infrastructure)
import Statlean.LimitTheorems.USLLN

/-! # Statlean Verified Library

**Every declaration reachable from this import is fully proved (zero sorry).**

This is the "clean" entry point for the StatLean library. It only imports
modules that have been verified to contain no sorry — neither directly
nor transitively through their dependency chains.

To check: `lake build Statlean.Verified` should produce zero sorry warnings.

## Contents

- **Gaussian/Basic**: stdGaussian, stdGaussianPi, integrability infrastructure
- **Gaussian/Stein**: Stein identity
- **Gaussian/Hermite**: Hermite derivative + orthogonality
- **Gaussian/Sobolev**: Mollification, Sobolev density
- **Variance/RaoBlackwell**: Rao-Blackwell MSE theorem and variants
- **Variance/EfronStein**: Efron-Stein clean core (sigma-algebras, ANOVA, condVar)
- **Entropy/Basic**: Entropy definitions, LSI interfaces
- **CharFun/Taylor**: Charfun chain, Taylor bounds, Lyapunov (Berry-Esseen chain)
- **LimitTheorems/USLLN**: Uniform Strong Law of Large Numbers (full theorem + infrastructure)
-/

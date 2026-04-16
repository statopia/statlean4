-- Core
import Statlean.Basic

-- Gaussian infrastructure (verified)
import Statlean.Gaussian.Basic
import Statlean.Gaussian.Stein
import Statlean.Gaussian.Hermite
import Statlean.Gaussian.OrnsteinUhlenbeck
import Statlean.Gaussian.HilbertSpace

-- Variance (verified)
import Statlean.Variance.ANOVA
import Statlean.Variance.RaoBlackwell
import Statlean.Variance.EfronStein

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

-- Estimation (verified — MSE, MLE, UMVUE, Bayes, robust, asymptotic theory)
import Statlean.Estimator.Basic
import Statlean.Estimator.Asymptotic
import Statlean.Estimator.UMVUE
import Statlean.Estimator.Bayes
import Statlean.Estimator.Robust
import Statlean.ExpFamily.Basic

-- Empirical process theory (verified)
import Statlean.EmpiricalProcess.CoveringNumber
import Statlean.EmpiricalProcess.Dudley

-- Distributions (verified)
import Statlean.Distribution.TDist

-- Fisher information and Cramér-Rao (verified)
import Statlean.Information.Basic
import Statlean.Information.CramerRao

-- Regression (verified)
import Statlean.Regression.Basic
import Statlean.Regression.Linear
import Statlean.Regression.MasterBound
import Statlean.Regression.GaussMarkov
import Statlean.Regression.Estimability

-- SPD matrices (verified)
import Statlean.SPD.Determinant
import Statlean.SPD.FrechetMean
import Statlean.SPD.Geodesic

-- Statistics foundations (verified)
import Statlean.Statistic.Basic
import Statlean.Statistic.Sample

-- Hypothesis testing (verified)
import Statlean.Testing.Basic

-- Confidence sets (verified)
import Statlean.Confidence.Basic

-- Moments (verified)
import Statlean.Moments.Basic
import Statlean.Moments.Covariance

-- Lehmann-Scheffé (verified)
import Statlean.Sufficiency.LehmannScheffe

-- Convergence modes and Slutsky's theorem (verified)
import Statlean.LimitTheorems.Convergence
import Statlean.LimitTheorems.Slutsky

-- Lévy continuity theorem (verified — forward + tightness + reverse)
import Statlean.LimitTheorems.Levy

-- Delta Method (verified — CMT, tightness, delta method, √n corollary)
import Statlean.LimitTheorems.DeltaMethod

-- Scheffé's theorem (verified — L¹ density convergence)
import Statlean.LimitTheorems.Scheffe

-- Central Limit Theorem (verified — iid CLT via charfun + Lévy continuity)
import Statlean.LimitTheorems.CLT

-- Lindeberg-Feller CLT (verified — triangular array CLT for non-iid row-independent RVs)
import Statlean.LimitTheorems.LindebergFeller

-- Cramér-Wold device (verified — multivariate Lévy + projection ⟺ weak convergence)
import Statlean.LimitTheorems.CramerWold

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
- **Estimator/Basic**: MSE = Bias² + Var, unbiased MSE = Var, risk dominance, loss functions,
  likelihood, IsMLE, MLE invariance, IsConsistent, IsAdmissible, IsMinimax, BayesRisk, IsEfficient
- **Estimator/Asymptotic**: IsAsymptoticallyNormal, HasAsymptoticMSE, HasAsymptoticBias,
  ARE, CLT→asymptotic normality bridge, scaled MSE decomposition, ARE inversion/comparison,
  Shao Thm 2.6 (scalar amse delta method: distribution + second moment + variance formulas)
- **Estimator/UMVUE**: UMVUE a.e. uniqueness (parallelogram identity), efficient ⇒ UMVUE,
  Rao-Blackwell UMVUE bridge, exponential family UMVUE, unestimability theorem
- **ExpFamily/Basic**: MLE existence in natural exponential families
- **Statistic/Sample**: sampleMean, sampleVariance, orderStatistic, sampleQuantile, sampleMedian
- **Testing/Basic**: TestFunction, PowerFunction, TypeI/II errors, Size, HasLevel,
  IsUMP, NeymanPearson, pValue, IsUnbiasedTest, IsSimilarTest, IsUMPU,
  HasMonotoneLR, np_integrand_nonneg, np_integral_nonneg,
  neyman_pearson_optimality, karlin_rubin
- **Confidence/Basic**: CoverageProb, IsConfidenceSet, IsConfidenceInterval, IsPivot
- **Moments/Basic**: moment, centralMoment, skewness, kurtosis, excessKurtosis,
  absoluteMoment, truncatedMoment, covariance, correlation, cumulant,
  variance_eq_moment_sub_sq, covariance_self_eq_variance, chebyshev_ineq
- **Moments/Covariance**: variance_add_eq, sq_covariance_le_variance_mul (Cauchy-Schwarz),
  corrCoeff, corrCoeff_abs_le_one, variance_sum_of_covariance_zero, variance_sum_independent
- **LimitTheorems/Convergence**: AlmostSure, InProbability, InLp, CompleteConvergence,
  MomentConvergence, TotalVariationConvergence
- **LimitTheorems/Slutsky**: Slutsky's theorem (add, mul, div) + inv convergence in measure
- **LimitTheorems/DeltaMethod**: Continuous mapping theorem, delta method (Shao Thm 1.12),
  √n corollary (Shao Cor 1.1), tightness lemma (rescaled convergence ⟹ convergence in probability)
- **LimitTheorems/Scheffe**: Scheffé's theorem (Shao Thm 1.5): density convergence a.e. + equal
  integrals ⟹ L¹ convergence, via DCT on positive part
- **Regression/GaussMarkov**: Gauss-Markov theorem (Shao Thm 3.9): OLS minimizes residual norm
  (BLUE optimality via orthogonal projection)
- **LimitTheorems/Levy**: Lévy continuity theorem (Shao Thm 1.9): forward (weak convergence
  ⟹ charfun convergence) + reverse (charfun convergence + continuity at 0 ⟹ weak convergence)
  via tightness + Prokhorov + charFun uniqueness
- **LimitTheorems/CLT**: Central Limit Theorem (Shao Thm 1.4): iid mean-zero L³ random variables
  with σ² > 0 ⟹ standardized sum converges weakly to N(0,1), via charfun Taylor bound + Lévy
- **LimitTheorems/LindebergFeller**: Lindeberg-Feller CLT (Shao Thm 1.6): triangular array of
  row-independent mean-zero L² random variables satisfying the Lindeberg condition ⟹ standardized
  row sums converge weakly to N(0,1), via charfun factorization + telescope + Feller condition
- **LimitTheorems/CramerWold**: Cramér-Wold device (Shao Thm 1.9(iii)): multivariate Lévy
  continuity (charFun convergence → weak convergence in finite dimensions) + Cramér-Wold iff
  (weak convergence ⟺ all 1D projections converge), via ONB tightness + Parseval pigeonhole
-/

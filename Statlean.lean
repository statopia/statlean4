import Statlean.Basic

-- Gaussian infrastructure
import Statlean.Gaussian.Basic
import Statlean.Gaussian.Stein
import Statlean.Gaussian.Hermite
import Statlean.Gaussian.Poincare
import Statlean.Gaussian.OrnsteinUhlenbeck
import Statlean.Gaussian.HilbertSpace
-- Variance inequalities
import Statlean.Variance.ANOVA
import Statlean.Variance.RaoBlackwell
import Statlean.Variance.EfronStein
import Statlean.Variance.UStatistic

-- Entropy and log-Sobolev
import Statlean.Entropy.Basic
import Statlean.Entropy.LogSobolev

-- Sub-Gaussian and Lipschitz concentration
import Statlean.SubGaussian.Herbst
import Statlean.SubGaussian.Lipschitz

-- High-dimensional mediation analysis
import Statlean.HDMediation.Assumptions

-- Conformal prediction (distribution-free inference)
import Statlean.Conformal.Basic
import Statlean.Conformal.Rank
import Statlean.Conformal.MarginalCoverage
import Statlean.Conformal.Split
import Statlean.Conformal.JackknifePlus

-- Multiple testing (FWER + FDR)
import Statlean.MultipleTesting.Basic
import Statlean.MultipleTesting.Bonferroni
import Statlean.MultipleTesting.BenjaminiHochberg

-- Characteristic function Taylor bounds
import Statlean.CharFun.Taylor

-- Fourier analysis infrastructure
import Statlean.Fourier.JacksonKernel
import Statlean.Fourier.CDFInversion


-- Limit theorems
import Statlean.LimitTheorems.Convergence
import Statlean.LimitTheorems.Levy
import Statlean.LimitTheorems.BerryEsseen
import Statlean.LimitTheorems.USLLN

-- Phase 2: Empirical Process Theory
import Statlean.EmpiricalProcess.CoveringNumber
import Statlean.EmpiricalProcess.Dudley
import Statlean.EmpiricalProcess.Donsker
import Statlean.EmpiricalProcess.StochasticOrder
import Statlean.EmpiricalProcess.Symmetrization
import Statlean.EmpiricalProcess.Chaining

-- Phase 3: Least-Squares Framework
import Statlean.Regression.Basic
import Statlean.Regression.MasterBound
import Statlean.Regression.Linear
import Statlean.Regression.GaussMarkov
import Statlean.Regression.Estimability
import Statlean.Regression.NormalLinearModel

-- SPD matrices (Log-Cholesky Fréchet means)
import Statlean.SPD.FrechetMean
import Statlean.SPD.Determinant
import Statlean.SPD.Geodesic

-- Statistic foundations (completeness, ancillary, sample statistics)
import Statlean.Statistic.Basic
import Statlean.Statistic.Sample

-- Time series (strict / wide-sense stationarity, Birkhoff bridge,
-- mixing conditions, ARMA processes)
import Statlean.TimeSeries.Stationarity
import Statlean.TimeSeries.Ergodic
import Statlean.TimeSeries.Mixing
import Statlean.TimeSeries.ARMA

-- Moments (moment, central moment, skewness, kurtosis)
import Statlean.Moments.Basic
import Statlean.Moments.Covariance

-- Hypothesis testing
import Statlean.Testing.Basic

-- Confidence sets
import Statlean.Confidence.Basic

-- Sufficiency
import Statlean.Sufficiency.Factorization
import Statlean.Sufficiency.Basu
import Statlean.ExpFamily.Basic
import Statlean.Estimator.Basic
import Statlean.Estimator.Asymptotic
import Statlean.Estimator.UMVUE
import Statlean.Estimator.Bayes
import Statlean.Estimator.Robust
import Statlean.Sufficiency.LehmannScheffe

-- Distributions (chi-squared, t-distribution)
import Statlean.Distribution.TDist

-- Fisher information and Cramér-Rao
import Statlean.Information.Basic
import Statlean.Information.CramerRao
import Statlean.Sufficiency.MinimalSufficiency
import Statlean.LimitTheorems.Slutsky
import Statlean.LimitTheorems.Scheffe
import Statlean.LimitTheorems.CLT
import Statlean.LimitTheorems.LindebergFeller
import Statlean.LimitTheorems.DeltaMethod
import Statlean.LimitTheorems.CramerWold
import Statlean.LimitTheorems.AsymptoticExpectation
import Statlean.Pipeline.Lecture9Handout

-- Semiparametric efficiency / influence-function calculus (DML, Chernozhukov 2018)
import Statlean.Semiparametric.InfluenceFunction

-- Differential privacy (Dwork–Roth framework)
import Statlean.DifferentialPrivacy.Mechanisms

-- Online learning (Zinkevich 2003, Cesa-Bianchi-Lugosi 2006; Auer 2002)
import Statlean.OnlineLearning.Regret
import Statlean.OnlineLearning.Bandits

-- Causal inference (Lin, Kong, Wang 2022)
import Statlean.Causal.Basic
import Statlean.Causal.OptimalTransport
import Statlean.EmpiricalProcess.RiemannSum
import Statlean.EmpiricalProcess.DonskerInfra
import Statlean.EmpiricalProcess.HoeffdingLemma
import Statlean.EmpiricalProcess.Equicontinuity
import Statlean.EmpiricalProcess.DKW
import Statlean.Analysis.CauchySchwarzAbs
import Statlean.Analysis.Norm.NormSubAddBound
import Statlean.Concentration.Talagrand
import Statlean.CoxChangePoint.Auto.approximation_of_smoothed_empirical_processes
import Statlean.CoxChangePoint.Auto.eigenfunction_estimation_L2_rate
import Statlean.CoxChangePoint.Auto.exponential_moment_bound
import Statlean.CoxChangePoint.Auto.smoothed_empirical_process_approximation
import Statlean.CoxChangePoint.Auto.uniform_bound_on_FPC_score_estimation_error
import Statlean.CoxChangePoint.Auto.uniform_convergence_of_Gn
import Statlean.CoxChangePoint.Auto.uniform_convergence_of_empirical_processes
import Statlean.CoxChangePoint.S3CauchySchwarzTail
import Statlean.Decision.Invariance
import Statlean.Decision.Risk
import Statlean.Gaussian.Gordon
import Statlean.MeasureTheory.MeasureInterLeMin
import Statlean.RandomMatrix.MarchenkoPastur

-- Score matching (Hyvärinen 2005)
import Statlean.ScoreMatching.Basic

-- Promoted from Statlean/Web/* sandboxes 2026-04-25:
import Statlean.CoxChangePoint.RemainderTailOp
import Statlean.CoxChangePoint.SupProductSquareIntegrable
import Statlean.CoxChangePoint.UniformProcessOpRate
import Statlean.ExpFamily.Regularity
import Statlean.EmpiricalBayes.JamesStein
import Statlean.DRO.Wasserstein

-- Statlean/Web/* sandboxes were swept 2026-04-25 + 2026-04-27:
--   * 558 transient sandbox dirs deleted in the original sweep.
--   * Substantive results promoted to proper namespaces (the 4 imports
--     above + B-section duplicates merged into existing modules).
--   * 2026-04-27 follow-up: jobmnfrosueh4uz unwrapped from markdown +
--     promoted to Statlean.Decision.Risk; jobmofvoxwsav8y deleted as
--     byte-identical duplicate of Statlean.Regression.Estimability;
--     jobmogms85u2gf6 promoted to Statlean.Regression.NormalLinearModel;
--     v2_consistency_of_RLEs_qwen_* deleted (Rule 3 trivialization,
--     anti-pattern documented in proof_knowledge.yaml); inert
--     scaffolding sandboxes (jobmod*, jobmof7*, jobmofci*, jobmog2*)
--     deleted. Backup tarball: /tmp/statlean_web_backup_2026-04-25.tar.gz.
--   * Going forward: Statlean/Web/ is gitignored (commit 840a575).
import Statlean.Web.jobmobquqqakyyv.Theorem1

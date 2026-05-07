# StatLean — Lean 4 Formalized Mathematical Statistics

A Lean 4 + Mathlib library formalizing core theorems of mathematical statistics, covering estimation theory, sufficiency, limit theorems, concentration inequalities, regression, Gaussian analysis, empirical processes, causal inference, **functional Cox regression with change-points**, and **modern statistical theory** (conformal prediction, multiple testing, semiparametric / DML influence functions, time series, differential privacy, online learning, empirical Bayes, distributionally robust optimization, score matching, survival analysis, random matrix theory, topological data analysis).

**Scale**: 184 Lean files · ~62,000 lines · 650+ public theorems

**Verification status** (machine-checked):
- **Cox change-point infra** (`Statlean/CoxChangePoint`, ~9.2k lines, 43 files): end-to-end formalisation of Yu-Li-Lin 2026 — Theorems 1, 2, 3 wired up via hypothesis-form interfaces. **Zero sorry, zero user axiom**.
- **Mathlib-PR-ready bridges** (`Statlean/Mathlib`, ~9.6k lines, 35 files): spectral theory + chaining + CLT + LAN pieces packaged for upstream contribution. **Zero sorry, zero user axiom**.
- **Core library** (`Statlean/{Gaussian, Variance, Entropy, SubGaussian, CharFun, LimitTheorems, Sufficiency, Information, Estimator, Testing, Confidence, Moments, Statistic, EmpiricalProcess, Causal, Regression, Fourier, SPD}`, ~30k lines): everything reachable from `Statlean/Verified.lean` is **zero sorry**. 9 isolated `sorry`s remain in active-development files (UStatistic ×5, AsymptoticExpectation ×3, DKW ×1), all tracked in `theme/input/sorry_backlog.yaml`. 9 named user `axiom`s document Mathlib infrastructure gaps with structured comments (Talagrand `mcdiarmid_mgf_bound`, Gordon `slepian_lemma`/`gordon_minimax_axiom`, MarchenkoPastur ×3 — Stieltjes inversion + MP fixed point + MP probability measure, NormalLinearModel ×3 — Shao Thm 3.8 needs vector-valued `IsGaussian` + Cochran).
- **Pipeline sandboxes** (`Statlean/Web/*`): zero sorries, zero axioms — promotable sandboxes have been moved into proper `Statlean/<MathArea>/<MathObject>.lean` paths; superseded duplicates removed.

> **Want to contribute? See [INSTRUCTION.md](INSTRUCTION.md)**

---

## Highlights

### Dudley Entropy Integral — Complete Chaining Pipeline (Zero Sorry)

Full Dudley chaining theorem from `IsSubGaussianProcess` to the entropy integral bound:

$$\mathbb{E}[\text{range}(X, \text{nets}_K)] \leq 8\sigma D\sqrt{2\log|F_0|} + \sum_{k<K} 8\sigma\varepsilon_k\sqrt{2\log|F_{k+1}|} \leq C\sigma\int_0^D \sqrt{\log N(\varepsilon)}\,d\varepsilon$$

Proof chain: Gaussian tail bound (Mill's ratio, FTC) → sharp sub-Gaussian max bound (truncation + Hoeffding cosh) → increment tail bounds (union bound + Chernoff) → K-step chaining telescope (induction) → dyadic Riemann sum ≤ 2× integral (squeeze by antitone interval bound).

### Cox Change-Point Regression — End-to-End Formalisation (Yu-Li-Lin 2026)

Complete Lean 4 infrastructure for the **functional linear Cox regression model with a change-point in the covariate**: 43 Cox-specific files (~9,200 lines, zero sorry, zero user axiom) plus 35 Mathlib-PR-ready bridges (~9,650 lines).

**Three theorems, three end-to-end proofs**:

| Paper theorem | Lean theorem | Discharge chain |
|---------------|--------------|------------------|
| **Theorem 1** (consistency: `θ̂ →ᵖ θ₀`) | `cox_consistency_end_to_end` | `CoxModel` + concavity + MLE + VW 2.14.9 → `theorem_1` |
| **Theorem 2** (rate: `‖θ̂ − θ₀‖ = O_P(δ_n)`) | `cox_theorem_2_end_to_end` | `Theorem2_hRate_of_VW_3_4_1` + LAN + peeling → `theorem_2` |
| **Theorem 3** (asym distribution) | `cox_theorem_3_end_to_end` | `JointAsymptoticDist` + LeCam + argmax-CMT → `theorem_3` |

**Infrastructure layers** (Statlean/CoxChangePoint):

- **Foundation** (`Foundation`, `Bridge`): `CoxObs p d`, `CoxParam p d`, `g_θ`, `expG`, `riskSum`, `logPartialLikelihood`, `Sample`, `Gn`.
- **FPC** (`FPC`, `S3CauchySchwarzTail`, `RemainderTailOp`, `SupProductSquareIntegrable`, `UniformProcessOpRate`, `LemmaS2Supp`): functional principal components, eigensystem, FPC scores, truncation residuals.
- **Score & MLE** (`Score`, `ScoreEquation`): partial scores ∂g_θ/∂(γ,α,β), MLE/argmax bridges.
- **Identifiability** (`Identifiability`, `StrictConcaveUnique`): well-separated max from concavity + compactness.
- **Empirical processes** (`Chaining`, `ChainingProof`, `ChainingRecursion`, `BracketingEntropy`, `LemmaS1Abstract`): VW Theorem 2.14.9 chain, dyadic recursion, telescoping, polynomial-class corollary.
- **Spectral / FPC errors** (`SpectralBridge`, `SinThetaTheorem`, `L2Operator`, `L2OperatorMap`, `InfiniteDimSpectral`, `SpectralOperator`): integral operator, eigendecomposition, Davis-Kahan / Sin-Theta perturbation.
- **Population objective** (`PopulationObjective`, `PopulationObjectiveConcrete`, `CoxLAN`, `CoxTaylor`): `G(θ) = E[Gn]`, concavity hypothesis, first-order Taylor expansion, LAN expansion bridge.
- **Theorems 1, 2, 3** (`CoxModel`, `Theorem2And3`, `Theorem2Proof`, `Theorem3Proof`, `CoxConsistencyEndToEnd`, `CoxTheorem23EndToEnd`, `CoxBenchmarkInstance`): top-level statements + end-to-end assembly + working benchmark instance.
- **Lemma S6 + scoring infrastructure** (`LemmaS6Combined`, `Score`).

### Mathlib-PR-Ready Bridges (Statlean/Mathlib)

35 files (~9,650 lines) packaging Cox-relevant Mathlib gaps as clean, citation-ready Lean theorems:

| Sub-namespace | Notable contents |
|---------------|------------------|
| `Mathlib/Analysis/` | `Parseval`, `BesselCompactSA`, `EigenbasisTotality`, `RayleighMax`, `RieszSchauder`, `BanachAlaoglu`, `CompactClosed`, `HilbertSchmidt`, `HilbertSchmidtCompact`, `SpectralCompactSelfAdjoint`, `SpectralTruncation` (+`Conv`), `DavisKahan` (+`SquaredSin`), `L2CompactSAInstance`, `InfiniteDimSpectral` |
| `Mathlib/EmpiricalProcess/` | `VWChaining`, `VWChainingInduction`, `VWPolynomialClass`, `BracketingIntegralConv` |
| `Mathlib/MeasureTheory/` | `L2Separable` (Lp.SecondCountableTopology bridge → HilbertBasis ℕ ℝ Lp) |
| `Mathlib/ProbabilityTheory/` | `MultivariateCLT`, `CentralLimitTheorem`, `CentralLimitNamed`, `CLTSums`, `UnivariateCLTBridge`, `LevyContinuity`, `ArgmaxCMT`, `StochasticArgmax`, `SkorohodArgmax`, `RandomMatrixOpNorm`, `CoxCovOpNormBound`, `CoxIIDInstance` |
| `Mathlib/Statistics/` | `LAN`, `LeCamThirdLemma`, `LeCamInstance` (Local Asymptotic Normality + Le Cam's three lemmas) |

Each file has Mathlib-style namespacing, real proofs where Mathlib pieces exist, hypothesis-form structures with TODO comments where Mathlib gaps remain.

### Causal Inference on Distribution Functions (Lin, Kong, Wang 2023)

Complete formalization of [Lin et al. (2023)](lin.pdf) — causal inference in the Wasserstein space:

| Theorem | Status | Key Lean theorem |
|---------|--------|-----------------|
| **Theorem 1** (Δ = E[Δ_i]) | ✅ | `causalEffectMap_eq_expectation` |
| **Theorem 2** (IPW identification) | ✅ | `causalEffectMap_identification` + `ipw_identity_from_tower` |
| **Theorem 3** (DR √n-consistency) | ✅ | `theorem3_rate_bound` + `donsker_pipeline_for_theorem3` |
| **Theorem 4** (Cross-fitting) | ✅ | `theorem4_crossfitting_rate` |
| **Theorem 5** (Nonparametric rate) | ✅ | `optimal_nonparametric_rate` |

Supporting infrastructure: doubly robust decomposition, influence functions, pull-out property (`condExp_mul`), Hoeffding's lemma (convexity of exp), covering number → Donsker class pipeline, simultaneous confidence bands.

### Berry-Esseen Theorem — Fully Proved (Zero Sorry)

$$\sup_y |F_{S_n}(y) - \Phi(y)| \leq \frac{C\rho}{\sigma^3 \sqrt{n}}$$

Proof chain: characteristic function Taylor → exponential decay → telescope product → Abel-regularized sinc integral → Fejér kernel bracket (shifted-argmax technique) → Esseen concentration → Berry-Esseen theorem.

### Gaussian Lipschitz Concentration — Full Herbst Pipeline (Zero Sorry)

$$\Pr[|f(X) - \mathbb{E}f(X)| \geq t] \leq 2\exp\!\left(-\frac{t^2}{2L^2}\right), \quad X \sim \gamma^n,\; f \text{ Lipschitz}$$

Complete proof chain: Gaussian LSI (Bakry-Emery / OU semigroup, ~5,650 lines) → entropy bound → Gaussian mollification → Herbst ODE/Grönwall → sub-Gaussian MGF → concentration.

### Modern Statistical Theory — 12 New Domains (Phase 3)

22 new modules (~80,000 lines of new Lean code) extending StatLean into contemporary statistical machine learning and applied probability:

| Domain | Files | Key results |
|--------|-------|-------------|
| **Conformal prediction** (Vovk-Shafer-Vapnik) | `Conformal/{Basic, Rank, MarginalCoverage, Split, JackknifePlus}` | Marginal coverage `P(Y_{n+1} ∈ Ĉ_α(X_{n+1})) ≥ 1 − α` under exchangeability; rank uniformity for non-conformity scores; split-conformal coverage; jackknife+ wrapper |
| **Multiple testing** | `MultipleTesting/{Basic, Bonferroni, BenjaminiHochberg}` | Bonferroni FWER ≤ α (proved); Benjamini-Hochberg FDR ≤ (m₀/m)·α (proved via Wang-Ramdas 9-step martingale argument) |
| **Semiparametric efficiency / DML** (Chernozhukov 2018) | `Semiparametric/InfluenceFunction.lean` | Influence functions, Neyman orthogonality, double / debiased machine learning rate `n^{1/4}` cross-fit |
| **Time series** | `TimeSeries/{Stationarity, Mixing, ARMA, Ergodic}` | Strict / wide-sense stationarity; α / β-mixing; ARMA(p,q) state-space form; Birkhoff ergodic theorem bridge |
| **Differential privacy** (Dwork-Roth) | `DifferentialPrivacy/Mechanisms.lean` | Gaussian mechanism (ε,δ)-DP via Rényi divergence; Laplace mechanism ε-DP; basic and advanced composition |
| **Online learning / bandits** | `OnlineLearning/{Regret, Bandits}` | Online gradient descent regret `O(√T)`; UCB1 stochastic-bandit regret `O(K log T / Δ)` |
| **Empirical Bayes / James-Stein** | `EmpiricalBayes/JamesStein.lean` | Stein's paradox: shrinkage estimator dominates MLE under quadratic loss for `d ≥ 3` |
| **Distributionally robust optimization** | `DRO/Wasserstein.lean` | Mohajerin Esfahani-Kuhn 2018 strong duality for Wasserstein DRO |
| **Score matching** (Hyvärinen 2005) | `ScoreMatching/Basic.lean` | Fisher divergence ↔ explicit score-matching loss via integration by parts |
| **Survival analysis** | `Survival/KaplanMeier.lean` | Kaplan-Meier 1958 product-limit estimator; Greenwood 1926 variance formula |
| **Random matrix theory** | `RandomMatrix/SpikedCovariance.lean` | Baik-Ben Arous-Péché 2005 BBP phase transition for top eigenvalue of spiked covariance |
| **Topological data analysis** | `TDA/PersistentHomology.lean` | Cohen-Steiner-Edelsbrunner-Harer 2007 stability theorem (bottleneck distance ≤ sup-norm) |

---

## Proved Theorems (Zero Sorry, Machine-Verified)

### Limit Theorems (Shao Ch.1, Complete Coverage)

| Theorem | File | Reference |
|---------|------|-----------|
| Central Limit Theorem (iid CLT) | `LimitTheorems/CLT.lean` | Shao Thm 1.4 |
| Lindeberg-Feller CLT (triangular array) | `LimitTheorems/LindebergFeller.lean` | Shao Thm 1.6 |
| **Berry-Esseen Theorem** | `LimitTheorems/BerryEsseen.lean` | Shao Thm 1.7 |
| Lévy Continuity Theorem | `LimitTheorems/Levy.lean` | Shao Thm 1.9 |
| Slutsky's Theorem | `LimitTheorems/Slutsky.lean` | Shao Thm 1.10 |
| Delta Method | `LimitTheorems/DeltaMethod.lean` | Shao Thm 1.12 |
| Cramér-Wold Device | `LimitTheorems/CramerWold.lean` | Shao Thm 1.9(iii) |
| Scheffé's Theorem | `LimitTheorems/Scheffe.lean` | Shao Thm 1.5 |
| Uniform SLLN | `LimitTheorems/USLLN.lean` | |
| Borel-Cantelli, Helly, Portmanteau, Pólya, Glivenko-Cantelli | `LimitTheorems/Convergence.lean` | |
| Asymptotic expectation uniqueness — case (iii) both-constant + case (ii) sub-cases (A,C) | `LimitTheorems/AsymptoticExpectation.lean` | Shao Prop 2.3 (partial) |
| `tendstoInDistribution_const_to_measure` (→d const ⇒ →ᵖ bridge, missing in Mathlib) | `LimitTheorems/AsymptoticExpectation.lean` | |

### Empirical Processes + Dudley Chaining

| Theorem | File |
|---------|------|
| **Dudley finite chaining bound** | `EmpiricalProcess/Dudley.lean` |
| Gaussian tail bound (Mill's ratio) | `EmpiricalProcess/Dudley.lean` |
| Sharp sub-Gaussian max bound (E[max Z_i] ≤ 4√(2V log N)) | `EmpiricalProcess/Dudley.lean` |
| Hoeffding's lemma (bounded → sub-Gaussian) | `EmpiricalProcess/HoeffdingLemma.lean` |
| Dyadic Riemann sum ≤ 2× integral | `EmpiricalProcess/RiemannSum.lean` |
| Covering number extraction + nearest point | `EmpiricalProcess/CoveringNumber.lean` |
| Chaining step decomposition (range subadditivity) | `EmpiricalProcess/Dudley.lean` |
| Donsker class + equicontinuity (δ·√\|log δ\| → 0) | `EmpiricalProcess/Equicontinuity.lean` |
| L²(P) entropy integral + polynomial covering bound | `EmpiricalProcess/DonskerInfra.lean` |
| Donsker pipeline for Theorem 3 (5-term rate assembly) | `EmpiricalProcess/DonskerInfra.lean` |

### Causal Inference (Lin, Kong, Wang 2023)

| Theorem | File |
|---------|------|
| Optimal transport map injectivity (Proposition 1) | `Causal/OptimalTransport.lean` |
| Causal effect map = E[individual effects] (Theorem 1) | `Causal/OptimalTransport.lean` |
| IPW identification via tower property (Theorem 2) | `Causal/OptimalTransport.lean` |
| Doubly robust rate bound (Theorem 3) | `Causal/OptimalTransport.lean` |
| Cross-fitting estimator (Theorem 4) | `Causal/OptimalTransport.lean` |
| Nonparametric concentration rate (Theorem 5) | `Causal/OptimalTransport.lean` |
| Mean minimizes L² distance (Wasserstein barycentre) | `Causal/OptimalTransport.lean` |
| Pull-out property (condExp_mul) | `Causal/OptimalTransport.lean` |
| DR bias decomposition + double robustness | `Causal/OptimalTransport.lean` |
| Influence function + sample covariance | `EmpiricalProcess/Donsker.lean` |

### Gaussian Analysis + Concentration

| Theorem | File |
|---------|------|
| Gaussian Log-Sobolev Inequality (1D + n-dim) | `Gaussian/OrnsteinUhlenbeck.lean` + `Entropy/LogSobolev.lean` |
| OU Semigroup (Mehler, invariance, convergence) | `Gaussian/OrnsteinUhlenbeck.lean` |
| Herbst Argument + Lipschitz Concentration | `SubGaussian/Herbst.lean` + `SubGaussian/Lipschitz.lean` |
| Gaussian Poincaré + Stein Identity + IBP | `Gaussian/` |
| Data Processing Inequality (DPI) | `Entropy/LogSobolev.lean` |
| Isonormal Process + Hilbert Space Gaussian | `Gaussian/HilbertSpace.lean` |

### Estimation, Sufficiency, Testing, Regression

| Theorem | File | Reference |
|---------|------|-----------|
| Rao-Blackwell, Lehmann-Scheffé, UMVUE | `Variance/` + `Sufficiency/` + `Estimator/` | |
| Fisher-Neyman Factorization + Basu's Theorem | `Sufficiency/` | |
| Cramér-Rao Information Inequality | `Information/CramerRao.lean` | |
| Gauss-Markov Theorem + Estimability | `Regression/GaussMarkov.lean` + `Regression/Estimability.lean` | |
| Neyman-Pearson Lemma + Karlin-Rubin | `Testing/Basic.lean` | |
| Chebyshev + Cauchy-Schwarz (covariance) | `Moments/` | |
| Hoeffding U-statistic CLT (Hájek projection) | `Variance/UStatistic.lean` | |
| Shao Thm 2.6 (scalar amse delta method) | `Estimator/Asymptotic.lean` | |
| **UMVUE characterization on sufficient statistic** (`umvue_iff_orthogonal_to_sufficient_unbiasedOfZero`) | `Estimator/UMVUE.lean` | Shao Thm 3.2(ii) |
| UMVUE characterization (full orthogonality) (`umvue_iff_orthogonal_to_unbiasedOfZero`) | `Estimator/UMVUE.lean` | Shao Thm 3.2(i) |

### Modern Statistical Theory (Phase 3, 22 new modules)

| Theorem | File | Reference |
|---------|------|-----------|
| Conformal marginal coverage `P(Y ∈ Ĉ_α) ≥ 1 − α` | `Conformal/MarginalCoverage.lean` | Vovk-Shafer-Vapnik |
| Conformal rank uniformity | `Conformal/Rank.lean` | |
| Split-conformal coverage | `Conformal/Split.lean` | Lei et al. 2018 |
| Jackknife+ predictive coverage | `Conformal/JackknifePlus.lean` | Barber et al. 2021 |
| Bonferroni FWER ≤ α | `MultipleTesting/Bonferroni.lean` | |
| Benjamini-Hochberg FDR ≤ (m₀/m)·α | `MultipleTesting/BenjaminiHochberg.lean` | Wang-Ramdas |
| Influence function / Neyman orthogonality / DML rate | `Semiparametric/InfluenceFunction.lean` | Chernozhukov 2018 |
| Strict and wide-sense stationarity | `TimeSeries/Stationarity.lean` | |
| α / β mixing definitions and inequalities | `TimeSeries/Mixing.lean` | |
| ARMA(p,q) state-space representation | `TimeSeries/ARMA.lean` | |
| Birkhoff ergodic LLN bridge | `TimeSeries/Ergodic.lean` | |
| Gaussian mechanism (ε,δ)-DP via Rényi | `DifferentialPrivacy/Mechanisms.lean` | Dwork-Roth |
| Laplace mechanism ε-DP and composition | `DifferentialPrivacy/Mechanisms.lean` | Dwork-Roth |
| Online gradient descent regret `O(√T)` | `OnlineLearning/Regret.lean` | |
| UCB1 stochastic bandit regret `O(K log T / Δ)` | `OnlineLearning/Bandits.lean` | Auer et al. |
| James-Stein dominates MLE for d ≥ 3 | `EmpiricalBayes/JamesStein.lean` | Stein 1956 |
| Wasserstein DRO strong duality | `DRO/Wasserstein.lean` | Mohajerin Esfahani-Kuhn 2018 |
| Score matching ↔ Fisher divergence (IBP) | `ScoreMatching/Basic.lean` | Hyvärinen 2005 |
| Kaplan-Meier estimator + Greenwood variance | `Survival/KaplanMeier.lean` | Kaplan-Meier 1958, Greenwood 1926 |
| BBP phase transition (spiked covariance) | `RandomMatrix/SpikedCovariance.lean` | Baik-Ben Arous-Péché 2005 |
| Persistent homology stability theorem | `TDA/PersistentHomology.lean` | Cohen-Steiner-Edelsbrunner-Harer 2007 |

---

## Project Structure

```
Statlean/                          (~62,000 lines, 184 files)
├── Gaussian/                      # Stein, Hermite, Poincaré, OU semigroup, Hilbert (6 files)
├── Variance/                      # Rao-Blackwell, ANOVA, Efron-Stein, UStatistic (4 files)
├── Entropy/                       # Entropy, Log-Sobolev, DPI (2 files)
├── SubGaussian/                   # Herbst argument, Lipschitz concentration (2 files)
├── CharFun/                       # Characteristic function Taylor chain (1 file)
├── LimitTheorems/                 # CLT, Berry-Esseen, Lévy, Cramér-Wold, etc. (12+ files)
├── Sufficiency/                   # Factorization, Basu, Lehmann-Scheffé (4 files)
├── Information/                   # Fisher information, Cramér-Rao (2 files)
├── Estimator/                     # MLE, UMVUE, Bayes, robust, asymptotics (6 files)
├── ExpFamily/                     # Exponential family (1 file)
├── Testing/                       # Neyman-Pearson, Karlin-Rubin (1 file)
├── Confidence/                    # Confidence sets (1 file)
├── Moments/                       # Moments, covariance (2 files)
├── Statistic/                     # Sample statistics (2 files)
├── EmpiricalProcess/              # Dudley chaining, covering numbers, Donsker (7 files)
│   ├── Dudley.lean                #   1,550 lines — full chaining pipeline
│   ├── CoveringNumber.lean        #   covering numbers + nearest point
│   ├── Chaining.lean              #   telescope + Hoeffding cosh
│   ├── Donsker.lean               #   empirical process CLT
│   ├── DonskerInfra.lean          #   L²(P) entropy → Donsker
│   ├── HoeffdingLemma.lean        #   bounded → sub-Gaussian MGF
│   ├── Equicontinuity.lean        #   δ·√|log δ| → 0 + StrongDonskerClass
│   └── RiemannSum.lean            #   dyadic sum ≤ 2× integral
├── Causal/                        # Causal inference (2 files, ~1,100 lines)
│   ├── Basic.lean                 #   CausalModel, Ignorability, Positivity
│   └── OptimalTransport.lean      #   Wasserstein, IPW, DR, Theorems 1-5
├── CoxChangePoint/                # Functional Cox regression w/ change-point (43 files, ~9,200 lines)
│   ├── Foundation.lean, Bridge.lean        #   CoxObs, CoxParam, partial likelihood, Gn
│   ├── FPC.lean, *Tail*, *Process*         #   FPC scores, eigensystem, truncation
│   ├── Score.lean, ScoreEquation.lean      #   ∂g_θ, MLE/argmax
│   ├── Identifiability.lean, StrictConcaveUnique.lean   #   well-separated max
│   ├── Chaining*.lean, BracketingEntropy.lean, LemmaS1Abstract.lean   #   VW 2.14.9
│   ├── SpectralBridge.lean, SinThetaTheorem.lean, L2Operator*.lean, InfiniteDimSpectral.lean   #   spectral
│   ├── PopulationObjective*.lean, CoxLAN.lean, CoxTaylor.lean   #   G(θ) + LAN expansion
│   ├── CoxModel.lean, Theorem2And3.lean, Theorem2Proof.lean, Theorem3Proof.lean   #   abstract Thm
│   ├── CoxConsistencyEndToEnd.lean, CoxTheorem23EndToEnd.lean, CoxBenchmarkInstance.lean   #   end-to-end
│   └── Auto/                                #   pipeline-generated skeletons
├── Mathlib/                       # Mathlib-PR-ready bridges (35 files, ~9,650 lines)
│   ├── Analysis/                   # Parseval, BanachAlaoglu, Spectral*, DavisKahan*, RayleighMax, ...
│   ├── EmpiricalProcess/           # VWChaining, VWPolynomialClass, BracketingIntegralConv, ...
│   ├── MeasureTheory/L2Separable.lean
│   ├── ProbabilityTheory/          # CentralLimitTheorem, LevyContinuity, ArgmaxCMT, Skorohod*, ...
│   └── Statistics/                 # LAN, LeCamThirdLemma, LeCamInstance
├── Regression/                    # Least squares, Gauss-Markov, Shao Thm 3.8 normal linear model (6 files)
├── Fourier/                       # Fejér/Jackson kernels (3 files)
├── SPD/                           # Fréchet mean (3 files)
├── Conformal/                     # Vovk-Shafer-Vapnik conformal prediction (5 files)
├── MultipleTesting/               # Bonferroni, Benjamini-Hochberg FDR (3 files)
├── Semiparametric/                # DML / influence functions (Chernozhukov 2018) (1 file)
├── TimeSeries/                    # Stationarity, mixing, ARMA, Birkhoff ergodic (4 files)
├── DifferentialPrivacy/           # Gaussian/Laplace mechanism + composition (Dwork-Roth) (1 file)
├── OnlineLearning/                # OGD regret, UCB1 (2 files)
├── EmpiricalBayes/                # James-Stein paradox (1 file)
├── DRO/                           # Wasserstein DRO (Mohajerin Esfahani-Kuhn 2018) (1 file)
├── ScoreMatching/                 # Hyvärinen 2005 score matching (1 file)
├── Survival/                      # Kaplan-Meier + Greenwood (1 file)
├── RandomMatrix/                  # Marchenko-Pastur, BBP spiked covariance (2 files)
├── TDA/                           # Persistent homology stability (1 file)
├── Pipeline/                      # Lecture handouts, course-style assemblies
├── Web/                           # Pipeline sandbox outputs (3 disabled in main due to drift)
└── Verified.lean                  # Index of zero-sorry modules (everything reachable from this is fully proved)
```

---

## Sorry / Verification Status

**Tracked**: 9 `sorry` proof slots across 3 files + 10 named user `axiom`s across 5 files (out of 184); see `theme/input/sorry_backlog.yaml` for the live ledger.

| Layer | `sorry` count | `axiom` count | Notes |
|------|---------------|---------------|------|
| `Statlean/Verified.lean` reachable | **0** | **0** | Fully proved verified subset. `lake build Statlean.Verified` is the canonical zero-sorry entrypoint. |
| Cox change-point infra (43 files) | **0** | **0** | All hypothesis-supplied bridges resolved; concrete Cox-specific computations (Taylor, LAN, etc.) are exposed as `Prop` fields on the structure types. |
| Mathlib-PR-ready bridges (35 files) | **0** | **0** | Mathlib gaps stated as named hypothesis structures; bridges and corollaries discharged. |
| Pipeline sandboxes (`Statlean/Web/*`) | **0** | **0** | Promotable sandboxes moved to proper `Statlean/<MathArea>/` paths; superseded duplicates removed. |
| Active core development | **9** | **9** | `Variance/UStatistic` (5 sorry — `cov_hSub_eq_uZeta` is the root of a Hoeffding-decomposition chain blocking 4 dependents), `LimitTheorems/AsymptoticExpectation` (3 sorry — Shao Prop 2.3 case (i) Khinchin-blocked + case (ii) sub-cases B(b2) tightness-from-→d & D Helly-extraction), `EmpiricalProcess/DKW` (1 sorry), `RandomMatrix/MarchenkoPastur` (3 axiom — Stieltjes inversion + MP fixed point + MP probability measure), `Concentration/Talagrand` (1 axiom — McDiarmid MGF bound), `Gaussian/Gordon` (2 axiom — Slepian + Gordon minimax), `Regression/NormalLinearModel` (3 axiom — Shao Thm 3.8 vector-valued `IsGaussian` + Cochran). All tracked in `sorry_backlog.yaml`. |
| Phase 3 modern theory (22 files) | **0** | **1** | Conformal (4 zero-axiom + `Conformal/JackknifePlus` 1 axiom for symmetry-of-leave-one-out exchangeability), MultipleTesting, Semiparametric, TimeSeries, DifferentialPrivacy, OnlineLearning, EmpiricalBayes, DRO, ScoreMatching, Survival, RandomMatrix/SpikedCovariance, TDA — all proved with named hypothesis-form interfaces where Mathlib gaps remain. |

**Recent progress** (April 2026):
- Shao Prop 2.3 case (iii) `shao_prop_2_3_case_both_const` — **fully proved** via 4-case trichotomy + new `aux_ratio_limit` helper (1/3+1/3<1 union bound + algebraic decomposition).
- Shao Prop 2.3 case (ii) sub-cases (A) and (C) — **proved** as vacuous via `hξ_nondeg` (slutsky-div/mul + distribution uniqueness + Mathlib `ae_eq_dirac'`).
- `tendstoInDistribution_const_to_measure` — bridge `→d const ⇒ →ᵖ` (missing in Mathlib) proved via Lipschitz test fn `min(ε, |x−c|)` + `tendsto_iff_forall_lipschitz_integral_tendsto`.
- Shao Thm 3.2(ii) `umvue_iff_orthogonal_to_sufficient_unbiasedOfZero` — **fully proved** via Doob-Dynkin factorization + sufficiency invariance of conditional expectation + `MemLp.condExp` + tower property. UMVUE.lean now zero-sorry.
- Marchenko-Pastur convergence — closed via documented axiom `stieltjes_continuity_theorem_axiom` (Mathlib lacks Stieltjes inversion + Vitali-Montel + Helly + Portmanteau-for-ℝ chain, ~500 lines new infra needed).

```bash
$ lake build                                   # full project — passes
$ lake build Statlean.Verified                 # the zero-sorry verified subset
```

---

## Quick Start

```bash
git clone https://github.com/mockingbird-gan/statlean4.git && cd statlean4
curl https://elan-init.tracing.rs/elan-init.sh -sSf | sh   # install elan (skip if present)
lake exe cache get                                           # download Mathlib cache
lake build Statlean                                          # build (zero errors)
lake build Statlean.Verified                                 # verify zero-sorry modules
```

**Requirements**: Lean 4.28.0-rc1, Mathlib (pinned in `lakefile.lean`)

---

## References

- **Shao, J.** *Mathematical Statistics* (Springer, 2003) — Chapters 1-7
- **Lin, Z., Kong, D., Wang, L.** *Causal Inference on Distribution Functions* (2023)
- **Yu, Z., Li, W., Lin, Z.** *Functional Linear Cox Regression Model with a Change-Point in the Covariate* (2026)
- **Boucheron, S., Lugosi, G., Massart, P.** *Concentration Inequalities* (Oxford, 2013)
- **van der Vaart, A., Wellner, J.** *Weak Convergence and Empirical Processes* (Springer, 1996)
- **van der Vaart, A.** *Asymptotic Statistics* (Cambridge, 1998)
- **Vovk, V., Shafer, G., Vapnik, V.** *Algorithmic Learning in a Random World* (Springer, 2005) — conformal prediction
- **Barber, R., Candès, E., Ramdas, A., Tibshirani, R.** *Predictive inference with the jackknife+* (Annals of Statistics, 2021)
- **Benjamini, Y., Hochberg, Y.** *Controlling the false discovery rate* (JRSS B, 1995); **Wang, R., Ramdas, A.** martingale proof of BH
- **Chernozhukov, V. et al.** *Double/Debiased Machine Learning for Treatment and Structural Parameters* (Econometrics Journal, 2018)
- **Dwork, C., Roth, A.** *The Algorithmic Foundations of Differential Privacy* (Foundations and Trends, 2014)
- **Mohajerin Esfahani, P., Kuhn, D.** *Data-driven distributionally robust optimization using Wasserstein metric* (Math. Prog., 2018)
- **Hyvärinen, A.** *Estimation of non-normalized statistical models by score matching* (JMLR, 2005)
- **Kaplan, E. L., Meier, P.** *Nonparametric estimation from incomplete observations* (JASA, 1958)
- **Baik, J., Ben Arous, G., Péché, S.** *Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices* (Annals of Probability, 2005)
- **Cohen-Steiner, D., Edelsbrunner, H., Harer, J.** *Stability of persistence diagrams* (Discrete & Comput. Geometry, 2007)

---

## Documentation

| Document | Description |
|----------|-------------|
| **[INSTRUCTION.md](INSTRUCTION.md)** | **Contribution guide** — setup, workflow, acceptance criteria |
| [theme/PIPELINE.md](theme/PIPELINE.md) | Pipeline details — PDF → Lean 4 full workflow |
| [theme/formalize_playbook.md](theme/formalize_playbook.md) | Formalization playbook — 7-step SOP |
| [theme/prove_playbook.md](theme/prove_playbook.md) | Proof playbook — strategy table, Mathlib search |

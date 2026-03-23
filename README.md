# StatLean — Lean 4 Formalized Mathematical Statistics

A Lean 4 + Mathlib library formalizing core theorems of mathematical statistics, covering estimation theory, sufficiency, limit theorems, concentration inequalities, regression, and Gaussian analysis.

**Scale**: 61+ Lean files · ~32,000 lines · 450+ public theorems · **ZERO sorry — fully machine-verified**

> **Want to contribute? See [INSTRUCTION.md](INSTRUCTION.md)**

---

## Highlights

### Berry-Esseen Theorem — Fully Proved (Zero Sorry)

The complete Berry-Esseen theorem with all 20+ supporting lemmas, forming the deepest proof chain in the library:

$$\sup_y |F_{S_n}(y) - \Phi(y)| \leq \frac{C\rho}{\sigma^3 \sqrt{n}}$$

The proof chain includes: characteristic function Taylor expansion → exponential decay bounds → telescope product bounds → Abel-regularized sinc integral → Fejér kernel bracket inequality (with a novel **shifted-argmax technique** for the hard case) → Esseen concentration inequality → Berry-Esseen theorem.

### Gaussian Lipschitz Concentration — Full Herbst Pipeline (Zero Sorry)

Complete proof chain from Log-Sobolev to concentration: Gaussian LSI → entropy bound for C¹ → Gaussian mollification (Rademacher + Leibniz + Fréchet diff) → Lipschitz limit (DCT) → Herbst ODE/Grönwall → sub-Gaussian MGF → concentration inequality.

$$\Pr[|f(X) - \mathbb{E}f(X)| \geq t] \leq 2\exp\!\left(-\frac{t^2}{2L^2}\right), \quad X \sim \gamma^n,\; f \text{ Lipschitz}$$

### Gaussian Log-Sobolev Inequality — 1D + n-dimensional (Zero Sorry)

Full formalization of the Gaussian LSI via the Bakry-Emery / Ornstein-Uhlenbeck semigroup approach (~5,650 lines):

$$\mathrm{Ent}_{\gamma^n}(f^2) \leq 2 \sum_{i=1}^n \int (\partial_i f)^2 \, d\gamma^n$$

Including a complete OU semigroup theory: Mehler formula, invariance, space interchange, convergence, positivity, entropy dissipation, Fisher information contraction.

---

## Proved Theorems (Zero Sorry, Machine-Verified)

### Limit Theorems (Shao Ch.1, Complete Coverage)

| Theorem | File | Reference |
|---------|------|-----------|
| Central Limit Theorem (iid CLT) | `LimitTheorems/CLT.lean` | Shao Thm 1.4 |
| Lindeberg-Feller CLT (triangular array) | `LimitTheorems/LindebergFeller.lean` | Shao Thm 1.6 |
| **Berry-Esseen Theorem** | `LimitTheorems/BerryEsseen.lean` | Shao Thm 1.7 |
| Lévy Continuity Theorem (forward + reverse) | `LimitTheorems/Levy.lean` | Shao Thm 1.9 |
| Slutsky's Theorem (add / mul / div) | `LimitTheorems/Slutsky.lean` | Shao Thm 1.10 |
| Continuous Mapping Theorem | `LimitTheorems/DeltaMethod.lean` | |
| Delta Method + √n corollary | `LimitTheorems/DeltaMethod.lean` | Shao Thm 1.12 |
| Cramér-Wold Device (multivariate Lévy + projection ⟺ weak convergence) | `LimitTheorems/CramerWold.lean` | Shao Thm 1.9(iii) |
| Scheffé's Theorem (density → L¹ convergence) | `LimitTheorems/Scheffe.lean` | Shao Thm 1.5 |
| Uniform Strong Law of Large Numbers | `LimitTheorems/USLLN.lean` | |
| Convergence implications (a.s.→prob, prob→subseq a.s., complete→a.s.) | `LimitTheorems/Convergence.lean` | |
| Borel-Cantelli Lemma (first + second) | `LimitTheorems/Convergence.lean` | |
| Kolmogorov Zero-One Law | `LimitTheorems/Convergence.lean` | Shao Thm 1.1 |
| Helly's Selection Theorem | `LimitTheorems/Convergence.lean` | |
| Portmanteau Theorem | `LimitTheorems/Convergence.lean` | |
| Pólya's Theorem (continuous limit CDF ⟹ uniform convergence) | `LimitTheorems/Convergence.lean` | |
| Glivenko-Cantelli (empirical CDF uniform convergence) | `LimitTheorems/Convergence.lean` | |
| Kolmogorov's Maximal Inequality | `LimitTheorems/Convergence.lean` | |
| Multivariate CLT (Cramér-Wold + 1D CLT) | `LimitTheorems/Convergence.lean` | |
| Characteristic Function Taylor Chain (charfun → exp decay) | `CharFun/Taylor.lean` | |

### Estimation Theory

| Theorem | File |
|---------|------|
| Rao-Blackwell MSE Theorem | `Variance/RaoBlackwell.lean` |
| MSE = Bias² + Variance | `Estimator/Basic.lean` |
| Lehmann-Scheffé UMVUE | `Sufficiency/LehmannScheffe.lean` |
| UMVUE a.e. uniqueness (parallelogram identity) | `Estimator/UMVUE.lean` |
| Efficient ⇒ UMVUE | `Estimator/UMVUE.lean` |
| Exponential family UMVUE (complete sufficient + Doob-Dynkin) | `Estimator/UMVUE.lean` |
| Cramér-Rao Information Inequality | `Information/CramerRao.lean` |
| Exponential family MLE existence & uniqueness | `ExpFamily/Basic.lean` |
| MLE definition + invariance | `Estimator/Basic.lean` |
| Asymptotic normality + asymptotic MSE + ARE | `Estimator/Asymptotic.lean` |
| Linear model estimability + BLUE/UMVUE | `Regression/Estimability.lean` |
| Bayes estimation + posterior risk | `Estimator/Bayes.lean` |
| Robust estimation (influence function, breakdown point) | `Estimator/Robust.lean` |

### Sufficiency

| Theorem | File |
|---------|------|
| Fisher-Neyman Factorization (both directions) | `Sufficiency/Factorization.lean` |
| Basu's Theorem | `Sufficiency/Basu.lean` |
| Minimal Sufficient Statistic (density ratio criterion) | `Sufficiency/MinimalSufficiency.lean` |

### Regression

| Theorem | File |
|---------|------|
| Gauss-Markov Theorem (BLUE) | `Regression/GaussMarkov.lean` |
| Least Squares + Master Error Bound | `Regression/MasterBound.lean` |
| Estimability: BLUE = UMVUE | `Regression/Estimability.lean` |

### Gaussian Analysis + Concentration

| Theorem | File |
|---------|------|
| Hermite orthogonality + Parseval + IBP | `Gaussian/Hermite.lean` |
| Stein's Identity | `Gaussian/Stein.lean` |
| Gaussian Poincaré Inequality | `Gaussian/Poincare.lean` |
| Ornstein-Uhlenbeck Semigroup (Mehler formula + full theory) | `Gaussian/OrnsteinUhlenbeck.lean` |
| **1D Gaussian Log-Sobolev Inequality** (Bakry-Emery, C²→W^{1,2}) | `Gaussian/OrnsteinUhlenbeck.lean` + `Entropy/LogSobolev.lean` |
| **n-dimensional Gaussian LSI** (tensorization) | `Entropy/LogSobolev.lean` |
| Entropy dissipation (d/dt Ent(P_t g) = -I(P_t g)) | `Gaussian/OrnsteinUhlenbeck.lean` |
| Fisher information contraction (I(P_t g) ≤ e⁻²ᵗ I(g)) | `Gaussian/OrnsteinUhlenbeck.lean` |
| ANOVA Variance Decomposition | `Variance/ANOVA.lean` |
| Efron-Stein Inequality | `Variance/EfronStein.lean` |
| Entropy non-negativity (Jensen) + conditional entropy | `Entropy/Basic.lean` |
| **Data Processing Inequality (DPI)** | `Entropy/LogSobolev.lean` |
| Entropy convexity + sub-additivity | `Entropy/LogSobolev.lean` |
| **Herbst Argument** (sub-Gaussian MGF from LSI) | `SubGaussian/Herbst.lean` |
| **Gaussian Lipschitz Concentration** | `SubGaussian/Lipschitz.lean` |
| **Stein Identity for Lipschitz Functions** (Steklov approximation) | `Gaussian/Stein.lean` |
| **Gaussian Integration by Parts** (n-dim, Fubini + 1D Stein) | `Gaussian/Stein.lean` |

### Hypothesis Testing

| Theorem | File |
|---------|------|
| Neyman-Pearson Lemma | `Testing/Basic.lean` |
| Karlin-Rubin (MLR → UMP) | `Testing/Basic.lean` |

### Foundations

| Definition / Theorem | File |
|----------------------|------|
| Hypothesis testing (test functions, power, UMP, Neyman-Pearson) | `Testing/Basic.lean` |
| Confidence sets (coverage, CI, pivots) | `Confidence/Basic.lean` |
| Sample statistics (sample mean/variance, order statistics, quantiles, median) | `Statistic/Sample.lean` |
| Moments (k-th / central / absolute / truncated moments, skewness, kurtosis, cumulants) | `Moments/Basic.lean` |
| Chebyshev's Inequality | `Moments/Basic.lean` |
| Cauchy-Schwarz (covariance), \|ρ\|≤1, independence ⟹ variance additivity | `Moments/Covariance.lean` |
| Convergence modes (complete, moment, TV, weak) | `LimitTheorems/Convergence.lean` |
| Decision theory (loss, risk, admissibility, minimax, Bayes) | `Estimator/Basic.lean` |
| Covering numbers + Dudley integral | `EmpiricalProcess/` |
| SPD Log-Cholesky Fréchet mean | `SPD/` |
| Isonormal process + Hilbert space Gaussian | `Gaussian/HilbertSpace.lean` |

---

## Berry-Esseen Proof Chain (Zero Sorry)

```
charfun_taylor_third_moment       ← Taylor expansion + third moment bound
    ↓
norm_charFun_le_one_sub           ← single-factor modulus |φ(s)| ≤ 1 - σ²s²/4
    ↓
norm_prod_sub_prod_le_sum_mul_pow ← telescope ‖∏z - ∏w‖ ≤ M^{n-1} · ∑‖z-w‖
    ↓
charfun_diff_exp_bound            ← exp decay ‖φ_S - φ_Φ‖ ≤ Cδ(|t|³+t⁴)e^{-t²/8}
    ↓
charfun_integral_bound            ← integral ∫ ‖φ_S-φ_Φ‖/|t| ≤ Cδ
    ↓
abel_sinc_integral                ← ∫₀^∞ e^{-εt} sin(at)/t dt = arctan(a/ε)
    ↓
esseen_smoothing_ineq             ← ✅ Fejér bracket + shifted-argmax (bilateral regularity)
    ↓
esseen_concentration_universal    ← Esseen inequality + Gaussian density bound
    ↓
berry_esseen_theorem              ← |F_S(y) - Φ(y)| ≤ Cρ/(σ³√n)  ✅
```

---

## CLT Proof Chain (Zero Sorry)

```
iid CLT (Shao Thm 1.4):
  charfun_normalized_sum_bound    ← charfun Taylor + triangular array bound
      ↓
  levy_continuity                 ← Lévy continuity theorem
      ↓
  central_limit_theorem           ← standardized sum ⟹ N(0,1)

Lindeberg-Feller CLT (Shao Thm 1.6):
  lindeberg_implies_max_var_tendsto  ← Lindeberg ⟹ Feller condition
      ↓
  charfun_lindeberg_pointwise        ← charfun pointwise → Gaussian charfun
      ↓
  lindeberg_feller_clt               ← triangular row sums ⟹ N(0,1)

Cramér-Wold Device (Shao Thm 1.9(iii)):
  isTight_of_charFun_tendsto (1D)   ← 1D Lévy tightness
      ↓
  isTight_of_charFun_tendsto_inner  ← multivariate tightness (ONB + Parseval)
      ↓
  cramer_wold_charFun               ← multivariate Lévy continuity
      ↓
  cramer_wold_iff                   ← μₙ →ᵈ μ₀ ⟺ ∀c, ⟨c,·⟩♯μₙ →ᵈ ⟨c,·⟩♯μ₀
```

---

## Project Structure

```
Statlean/
├── Gaussian/           # Standard Gaussian, Stein, Hermite, Poincaré, OU semigroup, Hilbert (6 files)
├── Variance/           # Rao-Blackwell, ANOVA, Efron-Stein (3 files)
├── Entropy/            # Entropy definitions, Log-Sobolev, DPI (2 files)
├── SubGaussian/        # Herbst argument, Lipschitz concentration (2 files)
├── CharFun/            # Characteristic function Taylor chain (1 file)
├── LimitTheorems/      # CLT, Lindeberg-Feller, Lévy, Cramér-Wold, Berry-Esseen,
│                       # USLLN, Slutsky, Delta Method, Scheffé, convergence modes (12 files)
├── Sufficiency/        # Factorization, Basu, minimal sufficiency, Lehmann-Scheffé (4 files)
├── Information/        # Fisher information, Cramér-Rao (2 files)
├── Estimator/          # MSE decomposition, MLE invariance, UMVUE, asymptotics, Bayes, robust (6 files)
├── ExpFamily/          # Exponential family MLE + NatExpFamily (1 file)
├── Testing/            # Hypothesis testing (UMP, Neyman-Pearson, Karlin-Rubin) (1 file)
├── Confidence/         # Confidence sets, pivots (1 file)
├── Moments/            # Moments, skewness, kurtosis, covariance (2 files)
├── Statistic/          # ParametricFamily, sample statistics (2 files)
├── EmpiricalProcess/   # Covering numbers, Dudley integral (2 files)
├── Regression/         # Least squares, Gauss-Markov, estimability (5 files)
├── Fourier/            # Fejér/Jackson kernels, Abel-sinc, sinc² integral (3 files)
├── SPD/                # Log-Cholesky Fréchet mean (3 files)
├── Distribution/       # t-distribution (1 file)
└── Verified.lean       # Index of zero-sorry modules
```

---

## Sorry Status: ZERO

**All theorems are fully machine-verified.** No sorry, no axioms beyond Lean's core + Mathlib.

```
Dependency DAG (all zero sorry ✅):
  BerryEsseen ✅ ── charfun Taylor → exp decay → Fejér bracket → Esseen smoothing
  OrnsteinUhlenbeck ✅ ──→ LogSobolev ✅ ──→ Herbst ✅ ──→ Lipschitz Concentration ✅
  Stein (Lipschitz) ✅ ──→ Gaussian IBP ✅ ──→ Mollification C¹ ✅
```

Key infrastructure for the Herbst argument (built from scratch):
- **Rademacher transfer**: `stdGaussianPi ≪ volume` via piFinSuccAbove induction
- **Leibniz rule**: `hasDerivAt_integral_of_dominated_loc_of_lip` for parametric integrals
- **Fréchet differentiability**: `hasFDerivAt_of_hasLineDerivAt_of_closure` for Gaussian mollification
- **Steklov approximation**: smooth C¹ approximation of Lipschitz functions for Stein identity
- **Gaussian IBP**: n-dimensional integration by parts via Fubini + 1D Stein

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

## Acceptance Criteria

```bash
lake build                       # zero errors, zero sorry warnings
lake build Statlean.Verified     # verified zero-sorry modules
grep -rn '^\s*sorry' Statlean/   # returns nothing
```

Every theorem is fully machine-verified. No sorry anywhere in the codebase.

---

## Documentation

| Document | Description |
|----------|-------------|
| **[INSTRUCTION.md](INSTRUCTION.md)** | **Contribution guide** — setup, workflow, acceptance criteria |
| [theme/PIPELINE.md](theme/PIPELINE.md) | Pipeline details — PDF → Lean 4 full workflow |
| [theme/formalize_playbook.md](theme/formalize_playbook.md) | Formalization playbook — 7-step SOP |
| [theme/prove_playbook.md](theme/prove_playbook.md) | Proof playbook — strategy table, Mathlib search |
| [theme/input/sorry_backlog.yaml](theme/input/sorry_backlog.yaml) | Sorry backlog — priority, blockers, dependencies |
| [theme/mathlib_api_index.md](theme/mathlib_api_index.md) | Mathlib API index — 650+ frequently used APIs |

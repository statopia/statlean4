# StatLean — Lean 4 Formalized Mathematical Statistics

A Lean 4 + Mathlib library formalizing core theorems of mathematical statistics, covering estimation theory, sufficiency, limit theorems, concentration inequalities, regression, Gaussian analysis, empirical processes, and causal inference.

**Scale**: 65+ Lean files · ~35,000 lines · 500+ public theorems · **ZERO sorry — fully machine-verified**

> **Want to contribute? See [INSTRUCTION.md](INSTRUCTION.md)**

---

## Highlights

### Dudley Entropy Integral — Complete Chaining Pipeline (Zero Sorry)

Full Dudley chaining theorem from `IsSubGaussianProcess` to the entropy integral bound:

$$\mathbb{E}[\text{range}(X, \text{nets}_K)] \leq 8\sigma D\sqrt{2\log|F_0|} + \sum_{k<K} 8\sigma\varepsilon_k\sqrt{2\log|F_{k+1}|} \leq C\sigma\int_0^D \sqrt{\log N(\varepsilon)}\,d\varepsilon$$

Proof chain: Gaussian tail bound (Mill's ratio, FTC) → sharp sub-Gaussian max bound (truncation + Hoeffding cosh) → increment tail bounds (union bound + Chernoff) → K-step chaining telescope (induction) → dyadic Riemann sum ≤ 2× integral (squeeze by antitone interval bound).

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

| Theorem | File |
|---------|------|
| Rao-Blackwell, Lehmann-Scheffé, UMVUE | `Variance/` + `Sufficiency/` + `Estimator/` |
| Fisher-Neyman Factorization + Basu's Theorem | `Sufficiency/` |
| Cramér-Rao Information Inequality | `Information/CramerRao.lean` |
| Gauss-Markov Theorem | `Regression/GaussMarkov.lean` |
| Neyman-Pearson Lemma + Karlin-Rubin | `Testing/Basic.lean` |
| Chebyshev + Cauchy-Schwarz (covariance) | `Moments/` |

---

## Project Structure

```
Statlean/                          (~35,000 lines, 65+ files)
├── Gaussian/                      # Stein, Hermite, Poincaré, OU semigroup, Hilbert (6 files)
├── Variance/                      # Rao-Blackwell, ANOVA, Efron-Stein (3 files)
├── Entropy/                       # Entropy, Log-Sobolev, DPI (2 files)
├── SubGaussian/                   # Herbst argument, Lipschitz concentration (2 files)
├── CharFun/                       # Characteristic function Taylor chain (1 file)
├── LimitTheorems/                 # CLT, Berry-Esseen, Lévy, Cramér-Wold, etc. (12 files)
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
├── Regression/                    # Least squares, Gauss-Markov (5 files)
├── Fourier/                       # Fejér/Jackson kernels (3 files)
├── SPD/                           # Fréchet mean (3 files)
└── Verified.lean                  # Index of zero-sorry modules
```

---

## Sorry Status: ZERO

**All theorems are fully machine-verified.** No sorry, no axioms beyond Lean's core + Mathlib.

```bash
$ grep -rn '^\s*sorry' Statlean/ | wc -l
0
$ lake build 2>&1 | grep -c 'sorry'
0
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
- **Lin, Z., Kong, D., Wang, L.** *Causal Inference on Distribution Functions* (2023) — [lin.pdf](lin.pdf)
- **Boucheron, S., Lugosi, G., Massart, P.** *Concentration Inequalities* (Oxford, 2013)
- **van der Vaart, A., Wellner, J.** *Weak Convergence and Empirical Processes* (Springer, 1996)

---

## Documentation

| Document | Description |
|----------|-------------|
| **[INSTRUCTION.md](INSTRUCTION.md)** | **Contribution guide** — setup, workflow, acceptance criteria |
| [theme/PIPELINE.md](theme/PIPELINE.md) | Pipeline details — PDF → Lean 4 full workflow |
| [theme/formalize_playbook.md](theme/formalize_playbook.md) | Formalization playbook — 7-step SOP |
| [theme/prove_playbook.md](theme/prove_playbook.md) | Proof playbook — strategy table, Mathlib search |

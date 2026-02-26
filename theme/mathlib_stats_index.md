# Mathlib Statistics/Probability API Index

Concise reference for promotion deduplication and proof search.
Updated: 2026-02-26, Mathlib v4.28.0-rc1.

## Independence & IID
```
iIndepSets : (ι → Set (Set Ω)) → Measure Ω → Prop
iIndep : (ι → MeasurableSpace Ω) → Measure Ω → Prop
iIndepFun : (ι → Ω → β) → Measure Ω → Prop
IndepFun : (Ω → β) → (Ω → γ) → Measure Ω → Prop
IdentDistrib : (Ω → β) → (Ω → β) → Measure Ω → Measure Ω → Prop
IndepFun.charFun_map_add_eq_mul  -- charfun(X+Y) = charfun(X)·charfun(Y)
iIndepFun_iff_charFun_pi          -- mutual indep via char functions
```

## Moments & MGF
```
moment X p μ : ℝ                           -- E[X^p]
centralMoment X p μ : ℝ                    -- E[(X-E[X])^p]
mgf X μ t : ℝ                              -- E[exp(tX)]
cgf X μ t : ℝ                              -- log(mgf)
variance X μ : ℝ                           -- Var[X]
evariance X μ : ℝ≥0∞                       -- extended variance
variance_le_expectation_sq                  -- Var ≤ E[X²]
variance_nonneg                             -- 0 ≤ Var
variance_eq_sub                             -- Var = E[X²] - (E[X])²
IndepFun.variance_add                       -- Var[X+Y] = Var[X]+Var[Y]
IndepFun.variance_sum                       -- Var of sum = sum of Var (pairwise)
IndepFun.mgf_add / cgf_add                 -- MGF/CGF factorize for indep RVs
analyticOn_mgf                              -- MGF is analytic
hasFPowerSeriesAt_mgf                       -- power series of MGF
iteratedDeriv_mgf                           -- n-th deriv = E[X^n exp(tX)]
```

## Conditional Expectation & Variance
```
condExp m μ f : Ω → E                      -- μ[f|m]
setIntegral_condExp                         -- ∫_s μ[f|m] = ∫_s f
condVar m X μ : Ω → ℝ                      -- Var[X|m]
integral_condVar_add_variance_condExp       -- LAW OF TOTAL VARIANCE
condExp_indep_eq                            -- indep ⟹ condExp = E[f]
condExp_mul_of_stronglyMeasurable_left      -- pull-out property
```

## Distributions
```
gaussianReal m v : Measure ℝ               -- N(m,v)
gaussianReal_isProbabilityMeasure           -- N(m,v) is prob measure (v>0)
charFun_gaussianReal                        -- charfun = exp(itm - vt²/2)
integral_gaussian                           -- ∫ exp(-bx²) = √(π/b)
fourierIntegral_gaussian                    -- FT of Gaussian is Gaussian
IsGaussian                                  -- class: X is Gaussian
HasPDF / pdf                                -- random variable has PDF
```

## CDF
```
cdf μ : StieltjesFunction                  -- CDF of measure
ofReal_cdf                                  -- ENNReal.ofReal(cdf μ x) = μ(Iic x)
measure_cdf                                 -- cdf(μ).measure = μ
```

## Characteristic Functions
```
charFun μ t = ∫ x, exp(⟪x,t⟫ * I) ∂μ     -- char function definition
charFun_norm_le_one                         -- |φ(t)| ≤ 1
charFun_zero                                -- φ(0) = 1
charFun_neg                                 -- φ(-t) = conj(φ(t))
```

## Fourier Analysis
```
fourierIntegral : (V → E) → (W → E)        -- Fourier transform
fourierIntegral_continuous                   -- FT of L¹ is continuous
norm_fourierIntegral_le_integral_norm        -- |FT(f)(w)| ≤ ∫|f|
fourierIntegral_involution                   -- Fourier inversion (pointwise)
fderiv_fourierIntegral                       -- derivative of FT
fourierChar                                  -- standard character
```

## Concentration Inequalities
```
measure_ge_le_exp_cgf                       -- CHERNOFF: P(X≥ε) ≤ exp(-tε+cgf(t))
measure_ge_le_exp_mul_mgf                   -- MGF Chernoff bound
meas_ge_le_variance_div_sq                  -- CHEBYSHEV: P(|X-E[X]|≥c) ≤ Var/c²
HasSubgaussianMGF                           -- sub-Gaussian property
hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero  -- HOEFFDING LEMMA
```

## Lp Spaces & Integrability
```
MemLp f p μ                                -- f ∈ Lp
Integrable f μ                              -- f ∈ L¹
eLpNorm / lpNorm                            -- Lp norms
inner_le_Lp_mul_Lq                          -- HOLDER inequality
memLp_one_iff_integrable                    -- L¹ ↔ Integrable
Lp.denseRange                               -- continuous functions dense in Lp
```

## Integration
```
integral f μ : E                            -- Bochner integral ∫ f ∂μ
integral_add / integral_sub                 -- linearity
integral_const_mul                          -- ∫ c·f = c · ∫ f
integral_mul_deriv_eq_deriv_mul_of_integrable  -- IBP on ℝ
tendsto_integral_of_dominated_convergence   -- Lebesgue DCT
integral_tsum                               -- ∫ Σfᵢ = Σ ∫ fᵢ
average                                     -- ⨍ f = (1/μ univ) ∫ f
```

## Hermite Polynomials
```
hermite : ℕ → Polynomial ℤ                 -- probabilists' Hermite
hermite_succ                                -- recurrence
deriv_gaussian_eq_hermite_mul_gaussian      -- d^n/dx^n exp(-x²/2) = (-1)^n Hₙ exp(-x²/2)
```

## Hilbert Space / L²
```
InnerProductSpace                           -- inner product structure
HilbertBasis                                -- orthonormal basis of Hilbert space
HilbertBasis.repr                           -- isometric to ℓ²
HilbertBasis.hasSum_repr                    -- Parseval: x = Σ ⟨bᵢ,x⟩ bᵢ
exists_hilbertBasis                         -- every Hilbert space has a basis
orthogonal_projection                       -- projection onto closed subspace
```

## Measure Theory Basics
```
IsProbabilityMeasure                        -- μ univ = 1
IsFiniteMeasure                             -- μ univ < ∞
SigmaFinite                                 -- σ-finite
rnDeriv                                     -- Radon-Nikodym derivative
Measure.map                                 -- pushforward measure
```

---

## What Mathlib DOES NOT have (common gaps)

- Berry-Esseen smoothing inequality
- Quantitative char function Taylor remainder with |t|³ E[|X|³] bound
- Esseen/Lévy concentration inequality (charfun → CDF bound)
- Gaussian Poincare inequality (spectral gap proof)
- Log-Sobolev inequality
- Efron-Stein ANOVA key inequality
- Herbst argument / Gronwall for concentration
- LSI tensorization
- Hermite completeness / Parseval in L²(γ)

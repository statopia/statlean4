# Statistics & Probability — Domain APIs

The Mathlib API names you reach for in statistics formalization:
specific distributions, variance, independence, matrix algebra (for
linear models), convergence types, plus the OLS-style escape-valve
pitfall.

For general measure-theoretic patterns (integrability, conditional
expectation, AE) see
[`measure_theory_patterns.md`](./measure_theory_patterns.md). For
parser/typeclass issues see the sibling files.

**API-status legend**: ✓ = verified spelling and signature ⚠ = plausible
but unverified — `check_type` before using.

Sections:
- §A. Random variables — quick reminders (cross-ref)
- §B. Specific distributions
- §C. Variance & independence
- §D. Matrix algebra (linear models, multivariate stats)
- §E. Convergence types
- §F. ⚠ Zero-measure escape — the OLS-style pitfall (cross-ref)
- §G. When this file doesn't help

---

## §A. Random variables — quick reminders

Encoding (full discussion in
[`measure_theory_patterns.md`](./measure_theory_patterns.md) §A'):

```lean
(X : Ω → ℝ) (hX : Measurable X)            -- standard real-valued RV
(X : Ω → ℝ) (hX : AEMeasurable X μ)        -- a.e. measurable
(X : Ω → E) (hX : StronglyMeasurable X)    -- Banach-valued (Bochner)
```

Default to `Measurable` for ℝ-valued RVs.

---

## §B. Specific distributions

| Distribution | Mathlib API | Status | Common wrong guesses |
|---|---|---|---|
| Gaussian (real-valued) | `ProbabilityTheory.gaussianReal (μ : ℝ) (v : ℝ≥0) : Measure ℝ` | ✓ | `gaussianVolume`, `Normal`, `Measure.gaussian` |
| Gaussian PDF (density) | `ProbabilityTheory.gaussianPDFReal` | ✓ | `gaussianPdfReal` (case-sensitive!) |
| Multivariate Gaussian (iid) | `MeasureTheory.Measure.pi (fun _ => gaussianReal 0 v)` | ✓ | `Measure.pi'` (apostrophe — internal version, do not use); jointly correlated requires manual construction |
| Exponential (rate r) | `ProbabilityTheory.expMeasure (r : ℝ) : Measure ℝ` | ✓ | `expDistribution`, `Exp`, `Exponential` |
| Bernoulli (set-valued) | `ProbabilityTheory.setBernoulli : Measure (Set ι)` | ✓ | `PMF.bernoulli`, `bernoulliMeasure` (set-valued only — for `{0, 1}`-valued use `PMF` or construct manually) |
| Uniform on a set | `ProbabilityTheory.uniformOn (s : Set Ω) : Measure Ω` | ✓ | `Measure.uniformOn`, `Measure.uniform` (wrong namespace) |
| Empirical measure | construct manually: `(1/n) • ∑ i, Measure.dirac (X i)` | manual | — |
| Dirac at a point | `Measure.dirac x : Measure α` | ✓ | `δ_x`, `pointMass` |

**Rule**: any time you reach for a distribution, first run
`check_type` or `lean_local_search` on the candidate name. Do NOT
invent plausible-sounding names like `gaussianVolume` — they don't
exist.

### §B.1 Variance parameter convention

`gaussianReal` takes the **variance** as `v : ℝ≥0` (not the standard
deviation, not σ²). When transcribing from `N(μ, σ²)`:

```lean
-- ✓ N(0, σ²) for σ : ℝ, σ ≥ 0
gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩

-- ✓ when σ : ℝ≥0
gaussianReal 0 (σ ^ 2)
```

The `⟨_, sq_nonneg _⟩` builds the `ℝ≥0` from a real and a
non-negativity proof.

### §B.2 Joint Gaussian with covariance matrix Σ

Mathlib does not (yet) have a one-liner. Construct manually:
1. Define a transformation `T : ℝⁿ → ℝⁿ` mapping iid N(0,1) to your
   target (e.g. `T x := μ + Σ.cholesky.mulVec x`).
2. Pushforward: `(Measure.pi (fun _ => gaussianReal 0 1)).map T`.
3. Verify the covariance via `Measure.map_apply` + integration.

For most stats theorems you can avoid joint Gaussian by isolating the
linear functional you actually need (which is itself univariate
Gaussian).

---

## §C. Variance & independence

```lean
variance X μ                                    -- Var(X) under μ  (lowercase 'v')
ProbabilityTheory.IndepFun X Y μ                -- two random variables independent
ProbabilityTheory.iIndepFun (fun i => X i) μ    -- indexed family independent
```

**Common mistakes**:
- Capitalizing `Variance` — Mathlib uses lowercase `variance`.
- Forgetting `open ProbabilityTheory` — then `IndepFun`, `iIndepFun`,
  `condExp`, `gaussianReal` are `unknown identifier`. See
  [`lean_syntax_errors.md`](./lean_syntax_errors.md) §C.9 for the
  full open list.
- For higher moments, there is no general `moment_n` API. Write
  manually:
  ```lean
  ∫ ω, (X ω - ∫ ω', X ω' ∂μ) ^ n ∂μ
  ```

### §C.1 Independence at the σ-algebra level

Independence of generated σ-algebras (sometimes the cleaner
formulation):
```lean
ProbabilityTheory.Indep (mZ : MeasurableSpace Ω) (mW : MeasurableSpace Ω) μ
```
gives `μ (A ∩ B) = μ A * μ B` for `A ∈ mZ`, `B ∈ mW`.

`IndepFun X Y μ` desugars to `Indep (comap X _) (comap Y _) μ` —
useful when you need to manipulate the underlying σ-algebras.

---

## §D. Matrix algebra (for linear models, multivariate stats)

```lean
(X : Matrix (Fin n) (Fin p) ℝ)    -- n × p design matrix
Xᵀ                                 -- transpose (or X.transpose)
X * Y                              -- matrix-matrix product
M.mulVec v                         -- matrix × vector  (NOT M * v)
M⁻¹                                -- inverse  (requires `IsUnit M` or `[Invertible M]`)
M.trace                            -- trace
M.det                              -- determinant
Matrix.IsSymm M                    -- symmetric
Matrix.PosSemidef M                -- positive semidefinite
Matrix.PosDef M                    -- positive definite
```

**Common mistakes**:
- `M * v` for matrix × vector → use `M.mulVec v`.
- `M⁻¹.mulVec v` (parens needed): `((M⁻¹).mulVec v)` or store via
  `let`:
  ```lean
  let GramInv : Matrix (Fin p) (Fin p) ℝ := (Xᵀ * X)⁻¹
  ...  GramInv.mulVec (Xᵀ.mulVec y)
  ```
- Expressing "X has full column rank" as `Matrix.rank X = p` —
  `Matrix.rank` exists ✓ but invertibility of the Gram matrix is
  usually cleaner:
  ```lean
  (X : Matrix (Fin n) (Fin p) ℝ) (hX : IsUnit (Xᵀ * X))
  ```

### §D.1 OLS skeleton template (use as a copy-paste seed)

```lean
-- Inputs
(n p : ℕ) (hn : 0 < n) (hpn : p < n)
(X : Matrix (Fin n) (Fin p) ℝ) (hX : IsUnit (Xᵀ * X))
(beta_0 : Fin p → ℝ)
(sigma : ℝ) (h_sigma : 0 < sigma)

-- Noise distribution: bound, not existential (see §F)
let mu : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 ⟨sigma ^ 2, sq_nonneg sigma⟩)

-- OLS estimator (function of the noise sample)
let beta_hat (eps : Fin n → ℝ) : Fin p → ℝ :=
  beta_0 + ((Xᵀ * X)⁻¹ * Xᵀ).mulVec eps

-- Conclusion: probability bound (not vacuous)
∃ c : ℝ, c > 0 ∧
  mu {eps | ‖beta_hat eps - beta_0‖ ^ 2 ≤ c * (sigma ^ 2 / n) * (Xᵀ * X)⁻¹.trace}
    ≥ 1 - alpha
```

### §D.2 Norm choice

For statistical bounds, pick:
- `‖v‖` (Euclidean / `EuclideanSpace`) — standard.
- `‖v‖₊` (NNReal-valued norm) — for measure-bound RHS.
- `(‖v‖ ^ 2)` — manually expand to `∑ i, v i ^ 2` if you need the
  inner-product form for Gram-matrix arguments.

Avoid ad-hoc max-of-coordinates without first reading
[`typeclass_errors.md`](./typeclass_errors.md) §A.1 (OrderBot ℝ
trap).

### §D.3 `n` vs `p` dimension confusion (noise ≠ parameters)

**Symptom**: `failed to synthesize instance ... HAdd (Fin n → ℝ) (Fin p → ℝ)`

In linear models there are two distinct index types:

| Index | Size | Used for |
|---|---|---|
| `Fin n` | observations | design rows, noise vector `ε`, response `y` |
| `Fin p` | parameters | design columns, coefficient vector `β` |

The noise vector **must** be `ε : Fin n → ℝ` (one noise per observation).
Using `Fin p → ℝ` for noise is always wrong.

```lean
-- ✗ WRONG — noise has parameter dimension
(eps : Fin p → ℝ)    -- triggers HAdd (Fin n → ℝ) (Fin p → ℝ) error

-- ✓ CORRECT — noise has observation dimension
(eps : Fin n → ℝ)    -- same dimension as y : Fin n → ℝ
```

**Rule**: whenever you write `beta_0 + ...`, both sides must have the
same type. `beta_0 : Fin p → ℝ`, so the RHS must also be `Fin p → ℝ`.
In OLS, `β̂ = β₀ + (XᵀX)⁻¹ Xᵀ ε` maps `ε : Fin n → ℝ` to `Fin p → ℝ`
via `((Xᵀ * X)⁻¹ * Xᵀ).mulVec eps`, which has the correct type.

---

## §E. Convergence

| Type | Mathlib |
|---|---|
| Topological / pointwise | `Tendsto f atTop (𝓝 L)` ✓ |
| Diverges to ∞ | `Tendsto f atTop atTop` ✓ |
| Almost surely | `∀ᵐ ω ∂μ, Tendsto (fun n => Xₙ ω) atTop (𝓝 (X ω))` |
| In probability | manual: `∀ ε > 0, Tendsto (fun n => μ {ω | ‖Xₙ ω - X ω‖ ≥ ε}) atTop (𝓝 0)` |
| In Lᵖ | `Tendsto (fun n => snorm (Xₙ - X) p μ) atTop (𝓝 0)` |
| In distribution | requires `ProbabilityMeasure` topology — advanced |

**Required**: `open Filter Topology` (for `atTop`, `𝓝`).

**Common mistake**: `unknown identifier 'Tendsto' / 'atTop'` — missing
`open Filter`. Add the canonical stats-file open at the top:
```lean
open Filter Topology MeasureTheory ProbabilityTheory ENNReal
```

### §E.1 LLN / CLT — what's in Mathlib

| Theorem | Mathlib name | Status |
|---|---|---|
| Strong law of large numbers (iid, L¹) | `ProbabilityTheory.strong_law_ae` | ✓ |
| Weak LLN | derive from SLLN or use `tendsto_average_of_iid` ⚠ | ⚠ |
| Central limit theorem (univariate) | `ProbabilityTheory.central_limit` ⚠ | ⚠ — confirm before relying |
| Kolmogorov 0-1 law | `MeasureTheory.kolmogorov_zero_one` ⚠ | ⚠ |

When using SLLN, the standard signature requires:
- `iIndepFun` (independence of the family)
- pairwise identical distributions
- `Integrable X₀ μ` (L¹)

If your problem needs L² (variance bound) but only L¹ in the
hypothesis, you usually need to manually construct the L² version.

---

## §F. ⚠ Zero-measure escape — the OLS-style pitfall

If `μ` is **existentially quantified** rather than bound, the prover
can pick `μ := (0 : Measure α)` (the zero measure) and trivialize:

```lean
-- The OLS bug:
∃ (μ : Measure Ω), ∀ᵐ ω ∂μ, P ω
-- Prover writes:  refine ⟨0, _⟩; simp [MeasureTheory.ae_zero]
-- → vacuously closed regardless of P
```

**Fix**: bind the measure as a parameter (see
[`measure_theory_patterns.md`](./measure_theory_patterns.md) §0). Or,
if you genuinely need an existential, **constrain it** with
`[IsProbabilityMeasure μ]` (forces μ total mass = 1, so μ ≠ 0).

The integrity-verifier (Layer 2) should catch this when comparing to
the original PDF/YAML, but the safest practice is to never write the
existential-measure pattern in the first place.

---

## §G. When this file doesn't help

1. **Verify the API exists**: `lean_local_search query="<name>"` then
   `check_type name="<name>"` for top hits. Do NOT guess a plausible
   name.
2. **Read the error column carefully**: parser errors like
   `unexpected token` are almost always
   [`lean_syntax_errors.md`](./lean_syntax_errors.md) §A — check that
   file before searching for APIs.
3. **For sub-σ-algebra trouble**: the problem is almost never
   "missing API" — it's
   [`instance_pollution.md`](./instance_pollution.md).
4. **Read Mathlib source**: when stuck, `read_file` on the actual
   Mathlib file containing the lemma you want, to see the exact
   signature.
5. **Statlean reference guide**: `theme/shao_reference_guide.md` and
   `theme/mathlib_stats_index.md` (in the statlean repo) catalog
   stats theorems by topic — useful when you don't even know the
   name.

# Measure Theory Patterns

Battle-tested templates for the measure-theoretic proofs we hit most
often in statistics formalization: probability-measure encoding,
random-variable measurability, integrability, conditional expectation,
almost-everywhere reasoning, σ-algebra plumbing, indicator rewriting,
NNReal bounds.

**Read first**: [`instance_pollution.md`](./instance_pollution.md) —
every CE proof depends on it.

For naming conventions and promotion-grade style see
[`mathlib_style.md`](./mathlib_style.md).

Sections:
- §0. Probability measure encoding (Measure α + IsProbabilityMeasure)
- §A. Integrability (the bounded + measurable + finite-measure recipe)
- §A'. Random-variable measurability (Measurable / AEMeasurable / StronglyMeasurable)
- §B. Conditional expectation: signature template (`condExpWith`)
- §C. Conditional expectation: equality via 3-condition uniqueness
- §D. Set-integral projection (the everyday workhorse)
- §E. Almost-everywhere — `ae_of_all`, `filter_upwards`, transitivity, zero-measure pitfall
- §F. σ-algebra ready-to-paste relations
- §G. Indicator rewriting (avoiding fragile product measurability)
- §H. Bounding CE pointwise (NNReal friction-free)
- §I. Common API-name pitfalls (E[X], variance, condExp)
- §J. Escalation order

---

## §0. Probability measure encoding

Two distinct types in Mathlib serve "the measure on Ω":

| Type | When to use |
|---|---|
| `Measure α` with `[IsProbabilityMeasure μ]` ✓ | **Default for stating probability theorems.** Same type as general measures, so all `MeasureTheory` lemmas apply directly. |
| `ProbabilityMeasure α` ✓ | Wrapper subtype. Use only when the *space of probability measures* itself has a topology (weak convergence, distribution-level arguments). |

### Recommended encoding

```lean
(μ : Measure Ω) [IsProbabilityMeasure μ]
```

### ❌ Anti-pattern: existential measure

```lean
-- WRONG: prover can pick μ = 0 (the zero measure) → vacuously true
∃ (μ : Measure Ω), ∀ᵐ ω ∂μ, P ω
```

When the source mathematics specifies a noise distribution (e.g.
"ε ~ N(0, σ²I)"), **bind the measure as a parameter or construct it
explicitly**; do not hide it behind `∃`. Reason: the zero measure
satisfies `∀ᵐ x ∂0, _` for any predicate (via
`MeasureTheory.ae_zero`), so an existential measure is an escape hatch
the prover will exploit. See §E for the symmetric statement on
almost-sure claims.

### Constructing product distributions

For iid-style noise (e.g. ε ∈ ℝⁿ with components ~ N(0, σ²)):

```lean
let μ : Measure (Fin n → ℝ) := Measure.pi (fun _ => gaussianReal 0 σ²)
```

`Measure.pi` ✓ takes a *function* `(i : ι) → Measure (α i)`. **Do not
pass `Fin.univ`** — it's not a `Set`, it's an indexed family.

For statistics-specific distributions (gaussianReal, uniformOn,
expMeasure, setBernoulli, empirical) see
[`statistics_domain.md`](./statistics_domain.md) §B.

---

## §A. Integrability

**Golden rule**: bounded + measurable + finite measure ⇒ integrable.

```lean
lemma integrable_of_bounded
    [IsFiniteMeasure μ] {f : X → ℝ}
    (h_meas  : Measurable f)
    (h_bound : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    Integrable f μ := by
  obtain ⟨C, hC⟩ := h_bound
  exact Integrable.of_bound h_meas.aestronglyMeasurable C (ae_of_all _ hC)
```

**Variants**:
```lean
-- AE bound (more common when f comes from a CE)
have h_aebound : ∀ᵐ x ∂μ, ‖f x‖ ≤ C := ...
exact Integrable.of_bound h_meas.aestronglyMeasurable C h_aebound

-- Restriction to a set
have hf_S : Integrable (Set.indicator S f) μ := hf.indicator hS

-- Integrable iff Integrable.norm
have : Integrable f μ ↔ Integrable (fun x => ‖f x‖) μ :=
  integrable_norm_iff h_meas.aestronglyMeasurable
```

**`AEMeasurable` ↛ `AEStronglyMeasurable` conversion** (integration
APIs need the stronger one):
```lean
have hf_meas : AEMeasurable f μ := ...
have hf_sm   : AEStronglyMeasurable f μ := hf_meas.aestronglyMeasurable
-- (works because ℝ is second-countable)
```

---

## §A'. Random-variable measurability

```lean
(X : Ω → ℝ) (hX : Measurable X)            -- standard real-valued RV
(X : Ω → ℝ) (hX : AEMeasurable X μ)        -- a.e. measurable (weaker, w.r.t. specific μ)
(X : Ω → E) (hX : StronglyMeasurable X)    -- Banach-valued; needed for Bochner integration
```

| Use | When |
|---|---|
| `Measurable` ✓ | Default for ℝ-valued RVs. `Measurable.const`, `.add`, `.mul`, `.comp`, `.prod_mk` etc. work compositionally. |
| `AEMeasurable` ✓ | After a.e. equality manipulation (e.g. `f =ᵐ[μ] g` and `g` measurable ⇒ `AEMeasurable f μ`). |
| `StronglyMeasurable` ✓ | Bochner-integral target spaces. Implies `Measurable` for separable codomains (so for ℝ it's the same). |

**Common mistake**: defining `(X : Ω → ℝ)` without ANY measurability
hypothesis, then trying to use `variance`, `condExp`, `Integrable`,
etc. These require `Measurable`/`AEMeasurable` upstream. Add the
hypothesis; don't expect Lean to infer it.

**Building measurable functions compositionally**:
```lean
-- f, g measurable ⇒ (f, g) : Ω → β × γ measurable
hX.prod_mk hY                       -- ✓

-- π_i ∘ measurable ⇒ measurable
hX.fst                              -- (Z, W) → first coordinate
hX.snd                              -- (Z, W) → second coordinate

-- continuous ∘ measurable ⇒ measurable
Continuous.measurable hf

-- Measurability of an indicator
(hS : MeasurableSet S) ⇒ Measurable (S.indicator (1 : Ω → ℝ))
```

---

## §B. Conditional expectation — signature template (`condExpWith`)

The canonical lemma signature for any CE statement with a sub-σ-algebra:

```lean
lemma my_condexp_lemma
    {Ω : Type*} {m₀ : MeasurableSpace Ω}    -- ✓ explicit ambient
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀)   -- ✓ explicit relation
    {f : Ω → ℝ} (hf : Integrable f μ) :
    -- conclusion involving μ[f|m]
    ... := by
  -- provide instances on the trimmed measure before calling Mathlib
  haveI : IsFiniteMeasure μ                  := inferInstance
  haveI : IsFiniteMeasure (μ.trim hm)        := isFiniteMeasure_trim μ hm
  haveI : SigmaFinite     (μ.trim hm)        := sigmaFinite_trim     μ hm
  ...
```

**The four non-negotiable elements**:
1. `{m₀ : MeasurableSpace Ω}` — explicit ambient (NEVER `‹_›` here).
2. `(hm : m ≤ m₀)` — explicit relation, named.
3. **All `[Instance]` parameters before any plain `(name : T)`
   parameters.** See §B.1 below.
4. `haveI` for trimmed-measure instances at the start of the proof,
   before any Mathlib CE call.

### §B.1 Binder order — instances first, then plain parameters

```lean
-- ❌ WRONG: m before instances
lemma bad {Ω : Type*} [MeasurableSpace Ω]
    (m : MeasurableSpace Ω)              -- plain param too early
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : m ≤ ‹MeasurableSpace Ω›) : Goal := by
  sorry  -- ‹MeasurableSpace Ω› resolves to m, gives `hm : m ≤ m`!

-- ✓ CORRECT: ALL instances first, then plain params
lemma good {Ω : Type*} [inst : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]   -- all instances
    (m : MeasurableSpace Ω)                    -- plain param after
    (hm : m ≤ inst) : Goal := by
  sorry  -- instance resolution works
```

When `m` appears before `[MeasurableSpace Ω]`, the bracketed lookup
`‹MeasurableSpace Ω›` in subsequent positions can resolve to `m`
instead of the genuinely-ambient instance — the bug shows up later as
`hm : m ≤ m`, which is true but useless.

This is the same root-cause as the binder-ordering pitfall in
[`lean_syntax_errors.md`](./lean_syntax_errors.md) §A.4.

---

## §C. Conditional expectation equality — 3-condition uniqueness

**Use this whenever you need `μ[f|m] = g` (a.e.).** Don't try to prove
it pointwise; Mathlib's uniqueness theorem reduces it to integral
equalities, which are usually tractable.

```lean
lemma condExp_eq_of_integral_eq
    {Ω : Type*} {m₀ m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {μ : Measure Ω} [SigmaFinite (μ.trim hm)]
    {f g : Ω → ℝ}
    (hf       : Integrable f μ)
    (hg_meas  : @Measurable Ω _ m _ g)         -- (1) g is m-measurable
    (hg_int   : Integrable g μ)                -- (2) g is integrable
    (h_setEq  : ∀ s, MeasurableSet[m] s →
                ∫ x in s, g x ∂μ = ∫ x in s, f x ∂μ) :   -- (3) integrals match on m
    μ[f | m] =ᵐ[μ] g := by
  symm
  exact ae_eq_condExp_of_forall_setIntegral_eq (μ := μ) (m := m) hm
    hf hg_meas hg_int h_setEq
```

**Why this is better than proving idempotence**: `μ[g|m] = g` a.e.
requires showing measurability under `m` plus an a.e. equality, which
typically loops back into typeclass synthesis. The 3-condition
uniqueness gives you three small obligations that are usually
one-liners each.

---

## §D. Set-integral projection (the everyday workhorse)

For `s ∈ m` and `Integrable g`, projection of CE onto a sub-σ-algebra
set integral:

```lean
have h : ∫ x in s, μ[g|m] x ∂μ = ∫ x in s, g x ∂μ :=
  set_integral_condexp (μ := μ) (m := m) (hm := hm) (hs := hs) (hf := hg)
```

**Wrapper to avoid parameter drift in long proofs**:
```lean
lemma setIntegral_condExp_eq (μ : Measure Ω) (m : MeasurableSpace Ω)
    (hm : m ≤ ‹_›) {s : Set Ω} (hs : MeasurableSet[m] s)
    {g : Ω → ℝ} (hg : Integrable g μ) :
    ∫ x in s, μ[g|m] x ∂μ = ∫ x in s, g x ∂μ := by
  simpa using set_integral_condexp (μ := μ) (m := m) (hm := hm) (hs := hs) (hf := hg)
```

**Use this** instead of attacking `μ[g|m] =ᵐ[μ] g` directly whenever
your downstream goal is an integral equation.

---

## §E. Almost-everywhere — three operations you'll need every proof

### §E.1 Universal → a.e.
```lean
have h : ∀ x, P x := ...
have h_ae : ∀ᵐ x ∂μ, P x := ae_of_all _ h
```

### §E.2 Combine multiple a.e. facts
```lean
filter_upwards [h1, h2, h3] with x hP hQ hR
-- now have: P x, Q x, R x simultaneously, prove the goal
```

### §E.3 Transitivity, congruence, and substitution under integrals
```lean
-- a.e. transitivity
h1.trans h2     -- f =ᵐ[μ] g, g =ᵐ[μ] h ⊢ f =ᵐ[μ] h

-- substitute via a.e. equality (preserves Integrable)
hf.congr hfg    -- Integrable f μ, f =ᵐ[μ] g ⊢ Integrable g μ

-- pass under ∫
integral_congr_ae hfg  -- f =ᵐ[μ] g ⊢ ∫ x, f x ∂μ = ∫ x, g x ∂μ
```

### §E.4 Pointwise vs `filter_upwards` — when to use which

- Goal is `∀ᵐ x ∂μ, P x` and you can prove `∀ x, P x`: use `ae_of_all`.
- Goal is `∀ᵐ x ∂μ, P x` and you have other a.e. hypotheses you need to
  combine: use `filter_upwards`.
- Don't `intro x` directly on `∀ᵐ` goals — that's `Filter.Eventually`,
  not a quantifier.

### §E.5 ⚠ Zero-measure escape (the OLS-style pitfall)

If `μ` is **existentially quantified** rather than bound, the prover
can pick `μ := (0 : Measure α)` and trivialize:

```lean
-- The OLS bug:
∃ (μ : Measure Ω), ∀ᵐ ω ∂μ, P ω
-- Prover writes:  refine ⟨0, _⟩; simp [MeasureTheory.ae_zero]
-- → vacuously closed regardless of P
```

**Fix**: bind the measure as a parameter (§0). Or, if you genuinely
need an existential, **constrain it** with `[IsProbabilityMeasure μ]`
(forces `μ Set.univ = 1`, so `μ ≠ 0`).

This is the single most common "structural" trivialization the prover
finds; the integrity-verifier (Layer 2) is supposed to catch it but
only when the skeleton has the corresponding flag set.

---

## §F. σ-algebra relations (ready-to-paste)

For random variables `Z, W : Ω → β` with `hZ, hW` measurable:

```lean
-- σ(W) ≤ ambient
have hmW_le  : MeasurableSpace.comap W ‹MeasurableSpace β› ≤ ‹MeasurableSpace Ω› :=
  hW.comap_le

-- σ(Z, W) ≤ ambient
have hmZW_le : MeasurableSpace.comap (fun ω => (Z ω, W ω)) ‹MeasurableSpace _› ≤ ‹MeasurableSpace Ω› :=
  (hZ.prod_mk hW).comap_le

-- σ(W) ≤ σ(Z, W)  (W is determined by (Z, W) via second projection)
have hmW_le_mZW :
    MeasurableSpace.comap W ‹MeasurableSpace β›
    ≤ MeasurableSpace.comap (fun ω => (Z ω, W ω)) ‹MeasurableSpace _› :=
  (measurable_snd.comp (hZ.prod_mk hW)).comap_le

-- Lift "measurable under sub-σ-algebra" to "measurable under ambient"
have hsm_ce_amb : StronglyMeasurable (μ[f|mW]) :=
  (stronglyMeasurable_condexp : StronglyMeasurable[mW] _).mono hmW_le
```

These pasteable patterns are the dominant content of any proof that
mixes σ(W), σ(Z, W), and the ambient σ-algebra. Keep them inline; do
NOT bind sub-σ-algebras with `let` until you've pinned the ambient
(see [`instance_pollution.md`](./instance_pollution.md) §B.2).

---

## §G. Indicator rewriting — avoid fragile product measurability

Goal: `∫ ω in S, f ω * (Z⁻¹ B).indicator 1 ω ∂μ`.

Don't try to show `(fun ω => f ω * (Z⁻¹ B).indicator 1 ω)` is
measurable directly — Mathlib doesn't always cooperate. Rewrite to a
plain indicator first:

```lean
have h_rewrite :
    (fun ω => f ω * (Z ⁻¹' B).indicator 1 ω)
    = (Z ⁻¹' B).indicator f := by
  funext ω
  by_cases hω : ω ∈ Z ⁻¹' B
  · simp [hω, Set.indicator_of_mem, mul_one]
  · simp [hω, Set.indicator_of_notMem, mul_zero]

-- Now Integrable / measurability come from indicator + base function
have h_int : Integrable (fun ω => f ω * (Z ⁻¹' B).indicator 1 ω) μ := by
  simpa [h_rewrite] using hf.indicator (hB.preimage hZ)

-- Restricted integral simplifies to S ∩ preimage
-- ∫_{S} (Z⁻¹ B).indicator h = ∫_{S ∩ Z⁻¹ B} h
```

**Pattern**: whenever a product `f * g` makes measurability painful
and one of the factors is a 0/1 indicator, rewrite to `Set.indicator`.

---

## §H. Bounding CE pointwise (NNReal friction-free)

```lean
-- Goal: ∀ᵐ ω ∂μ, ‖μ[f|m] ω‖ ≤ R from ∀ᵐ ω ∂μ, |f ω| ≤ R
have hbdd_f  : ∀ᵐ ω ∂μ, |f ω| ≤ (1 : ℝ) := ...
have hbdd_f' : ∀ᵐ ω ∂μ, |f ω| ≤ ((1 : ℝ≥0) : ℝ) :=
  hbdd_f.mono (fun ω h => by simpa [NNReal.coe_one] using h)
have : ∀ᵐ ω ∂μ, ‖μ[f|m] ω‖ ≤ (1 : ℝ) := by
  simpa [Real.norm_eq_abs, NNReal.coe_one] using
    ae_bdd_condExp_of_ae_bdd (μ := μ) (m := m) (R := (1 : ℝ≥0)) (f := f) hbdd_f'
```

`ae_bdd_condExp_of_ae_bdd` requires the bound as `ℝ≥0` — the small
NNReal ↔ ℝ dance above is unavoidable but routine.

---

## §I. Common API-name pitfalls

The following names are **NOT** in Mathlib — they are plausible
guesses that don't exist:

| Plausible guess | Real Mathlib spelling |
|---|---|
| `expectation X μ` | `∫ ω, X ω ∂μ` ✓ |
| `E[X]` (notation) | not defined globally; use `∫ ω, X ω ∂μ` |
| `Variance X μ` (capital V) | `variance X μ` ✓ (lowercase) |
| `gaussianVolume`, `Normal`, `Measure.gaussian` | `ProbabilityTheory.gaussianReal` ✓ |
| `expDistribution`, `Exp` | `ProbabilityTheory.expMeasure` ✓ |
| `condExp m μ X` (positional) | `μ[X | m]` (notation) or `condExp m μ X` ✓ — both exist |

**Rule**: any time you reach for a distribution / operator name, first
run `check_type` or `lean_local_search` on the candidate. Do NOT
invent plausible-sounding names. See
[`statistics_domain.md`](./statistics_domain.md) §B for the full
distribution catalog.

**Common mistakes**:
- Forgetting `Integrable X μ` hypothesis when using `condExp` — the
  result is junk (zero) on non-integrable inputs.
- Using `X` instead of `fun ω => X ω` inside `∫` — both work, but
  `simp` lemmas often only fire on the lambda form.

---

## §J. When in doubt — escalation order

1. **Look up the exact API** — `lean_local_search` or `check_type` on
   the closest Mathlib name you can guess. Most CE / integrability
   lemmas exist; you just need the spelling.
2. **Check
   [`instance_pollution.md`](./instance_pollution.md)** if you see
   `synthesized vs inferred` or 500k heartbeats.
3. **Re-read this file's §B.1 (binder order)** if instance synthesis
   complains about `‹_›`.
4. **Switch to kernel form** (`condExpKernel μ m ω`) if scalar
   `μ[f|m]` keeps hitting instance ambiguity in a long proof — kernel
   form takes `μ` and `m` as **explicit** parameters, no instance
   dance.
5. **Last resort**: leave the obligation as `sorry` with a comment
   `-- blocker: <one-line summary>`. Don't fight the elaborator for
   30+ minutes on a single sub-claim.

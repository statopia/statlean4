import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Basic
import Statlean.Distribution.TDist
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Powerset
import Statlean.LimitTheorems.CLT
import Statlean.LimitTheorems.Levy
import Statlean.LimitTheorems.LindebergFeller

/-! # Hoeffding's Theorem on the Variance of U-statistics

This file states **Hoeffding's theorem (Shao §3.2.2 Thm 3.4)**: for a U-statistic
`Uₙ` of order `m` with iid sample `X₁,…,Xₙ` of common law `ν` on `α` and a
symmetric `L²` kernel `h : (Fin m → α) → ℝ`,
`Var(Uₙ) = C(n,m)⁻¹ ∑_{k=1}^{m} C(m,k) C(n-m, m-k) ζ_k`,
where `ζ_k = Var(h_k(X₁,…,X_k))` and the projection
`h_k(x₁,…,x_k) = ∫ h(x₁,…,x_k, y_{k+1},…,y_m) dν^{m-k}(y)`.

This is **not** Hoeffding's concentration *inequality*; the latter lives in
`Statlean.Concentration.Talagrand` (`hoeffding_lemma`).

## Main definitions
- `appendFin` — concatenate `Fin k → α` and `Fin (m - k) → α` into `Fin m → α`
  when `k ≤ m`.
- `kernelProjection` — `h_k`, marginal average of `h` over the last `m - k`
  coordinates against `ν`.
- `uZeta` — `ζ_k = Var(h_k(X₁,…,X_k))` (returns 0 when `k > m`).
- `uStatistic` — the U-statistic of order `m` with kernel `h`, viewed as a
  function of the iid sample `Fin n → α`.

## Main results
- `u_statistic_variance_decomposition` — Hoeffding's theorem
  (structural `sorry`; sub-lemmas below are proved).

## Proved sub-lemmas
- `appendFin_castAdd_apply` — left component of `appendFin`.
- `appendFin_natAdd_apply` — right component of `appendFin`.
- `appendFin_full` — `appendFin` at k = m recovers `x`.
- `kernelProjection_full` — `h_m = h` (projection at full order).
- `uZeta_top` — `ζ_m = Var(h)`.
- `uZeta_nonneg` — variances are nonneg.
- `card_powersetCard_fin` — #{S ⊆ Fin n : |S| = m} = C(n,m).

## Status
The proof requires (Shao §3.2.2):
1. The reformulation `Uₙ - E(Uₙ) = C(n,m)⁻¹ ∑_S h̃(X_S)` (eq. 3.16).
2. The covariance identity `E[h̃(X_S) h̃(X_T)] = ζ_{|S ∩ T|}` (eq. 3.17),
   proved by Fubini + iid + tower property.
3. The combinatorial count `#{(S,T) : |S| = |T| = m, |S ∩ T| = k} =
   C(n,m) C(m,k) C(n-m, m-k)`.

Tracked in `theme/input/sorry_backlog.yaml`.
-/

open MeasureTheory ProbabilityTheory Finset Statlean.LimitTheorems Statlean.LimitTheorems.CLT
open scoped BigOperators

noncomputable section

namespace Statlean
namespace Variance
namespace UStatistic

variable {α : Type*} [MeasurableSpace α]

/-- Concatenate `x : Fin k → α` and `y : Fin (m - k) → α` into a tuple
`Fin m → α`, given `k ≤ m`. The first `k` slots are filled from `x`, the
last `m - k` from `y`, in order. -/
def appendFin {m k : ℕ} (hk : k ≤ m) (x : Fin k → α) (y : Fin (m - k) → α) :
    Fin m → α :=
  fun i => Fin.append x y (i.cast (by omega))

/-- The k-th coordinate projection of an order-`m` kernel `h` against the
common law `ν`:
`h_k(x₁,…,x_k) = ∫ h(x₁,…,x_k, y_{k+1},…,y_m) dν^{m-k}(y)`. -/
def kernelProjection (m k : ℕ) (hk : k ≤ m)
    (h : (Fin m → α) → ℝ) (ν : Measure α) (x : Fin k → α) : ℝ :=
  ∫ y : Fin (m - k) → α, h (appendFin hk x y) ∂(Measure.pi (fun _ : Fin (m - k) => ν))

/-- The k-th projected variance `ζ_k = Var(h_k(X₁,…,X_k))` with respect to
the iid product measure `ν^k`. Returns `0` for `k > m` (a convenience for
clean indexing in sums). -/
def uZeta (m k : ℕ) (h : (Fin m → α) → ℝ) (ν : Measure α) : ℝ :=
  if hk : k ≤ m then
    Var[kernelProjection m k hk h ν ; Measure.pi (fun _ : Fin k => ν)]
  else 0

/-- The U-statistic of order `m` with kernel `h`, evaluated on a sample
`x : Fin n → α`:
`Uₙ(x) = C(n,m)⁻¹ ∑_{S ⊆ {0,…,n-1}, |S|=m} h(x ∘ ι_S)`,
where `ι_S : Fin m ↪o Fin n` is the order-preserving embedding of `S`. -/
def uStatistic (n m : ℕ) (h : (Fin m → α) → ℝ) (x : Fin n → α) : ℝ :=
  ((n.choose m : ℝ))⁻¹ *
    ∑ s ∈ ((Finset.univ : Finset (Fin n)).powersetCard m).attach,
      h (fun i => x (s.1.orderEmbOfFin (Finset.mem_powersetCard_univ.mp s.2) i))

/-! ### Sub-lemmas on `appendFin` -/

omit [MeasurableSpace α] in
/-- `appendFin hk x y i = x ⟨i.val, hi⟩` when `i.val < k`. -/
lemma appendFin_castAdd_apply {m k : ℕ} (hk : k ≤ m) (x : Fin k → α) (y : Fin (m - k) → α)
    (i : Fin m) (hi : i.val < k) :
    appendFin hk x y i = x ⟨i.val, hi⟩ := by
  simp only [appendFin]
  rw [show i.cast (show m = k + (m - k) by omega) = Fin.castAdd (m - k) ⟨i.val, hi⟩ from by
    ext; simp [Fin.castAdd]]
  exact Fin.append_left x y ⟨i.val, hi⟩

omit [MeasurableSpace α] in
/-- `appendFin hk x y i = y ⟨i.val - k, _⟩` when `k ≤ i.val`. -/
lemma appendFin_natAdd_apply {m k : ℕ} (hk : k ≤ m) (x : Fin k → α) (y : Fin (m - k) → α)
    (i : Fin m) (hi : k ≤ i.val) :
    appendFin hk x y i = y ⟨i.val - k, by omega⟩ := by
  simp only [appendFin]
  rw [show i.cast (show m = k + (m - k) by omega) = Fin.natAdd k ⟨i.val - k, by omega⟩ from by
    ext; simp [Fin.natAdd]; omega]
  exact Fin.append_right x y ⟨i.val - k, by omega⟩

omit [MeasurableSpace α] in
/-- When `k = m`, `appendFin` ignores the vacuous `y : Fin 0 → α` argument
and just returns `x`. -/
lemma appendFin_full (m : ℕ) (x : Fin m → α) (y : Fin (m - m) → α) :
    appendFin (le_refl m) x y = x := by
  ext i
  rw [appendFin_castAdd_apply (le_refl m) x y i i.isLt]

/-! ### Sub-lemmas on `kernelProjection` -/

/-- Helper: `Fin (m - m) → α` has a unique element (since `m - m = 0`). -/
private def uniqueFinSubSelf (m : ℕ) (α : Type*) : Unique (Fin (m - m) → α) :=
  (Nat.sub_self m) ▸ inferInstance

/-- At full order `k = m`, `kernelProjection` recovers `h` itself:
`h_m(x) = ∫ h(x, ∅) dν⁰ = h(x)`. -/
lemma kernelProjection_full (m : ℕ) (h : (Fin m → α) → ℝ) (ν : Measure α)
    [IsProbabilityMeasure ν] (x : Fin m → α) :
    kernelProjection m m (le_refl m) h ν x = h x := by
  simp only [kernelProjection]
  haveI h_unique : Unique (Fin (m - m) → α) := uniqueFinSubSelf m α
  haveI : IsProbabilityMeasure (Measure.pi (fun _ : Fin (m - m) => ν)) := inferInstance
  rw [integral_unique, probReal_univ, one_smul]
  rw [appendFin_full m x h_unique.default]

/-! ### Sub-lemmas on `uZeta` -/

/-- The `uZeta` value at `k = m` is the variance of `h` itself under `ν^m`. -/
lemma uZeta_top (m : ℕ) (h : (Fin m → α) → ℝ) (ν : Measure α)
    [IsProbabilityMeasure ν] :
    uZeta m m h ν = Var[h ; Measure.pi (fun _ : Fin m => ν)] := by
  simp only [uZeta, le_refl, dif_pos]
  congr 1
  ext x
  exact kernelProjection_full m h ν x

/-- `uZeta` is nonneg everywhere (it equals a variance or 0). -/
lemma uZeta_nonneg (m k : ℕ) (h : (Fin m → α) → ℝ) (ν : Measure α) :
    0 ≤ uZeta m k h ν := by
  unfold uZeta
  split_ifs with hk
  · exact ProbabilityTheory.variance_nonneg _ _
  · linarith

/-! ### Sub-lemmas on `uStatistic` -/

/-- The number of size-`m` subsets of `Fin n` equals `n.choose m`. -/
lemma card_powersetCard_fin (n m : ℕ) :
    ((Finset.univ : Finset (Fin n)).powersetCard m).card = n.choose m := by
  rw [Finset.card_powersetCard]
  simp

/-! ### Key sub-lemmas for the variance decomposition -/

section VarDecomp

/-- The subtype of `m`-element subsets of `Fin n`, used as index for the
U-statistic sum. -/
private abbrev PSElem (n m : ℕ) : Type :=
  { x : Finset (Fin n) // x ∈ (Finset.univ : Finset (Fin n)).powersetCard m }

/-- The kernel `h` evaluated on the subsample indexed by `S`. -/
private def hSub {n m : ℕ} (h : (Fin m → α) → ℝ) (s : PSElem n m) (x : Fin n → α) : ℝ :=
  h (fun i => x (s.val.orderEmbOfFin (Finset.mem_powersetCard_univ.mp s.prop) i))

omit [MeasurableSpace α] in
/-- `uStatistic` expressed as a scalar multiple of a sum of `hSub` terms. -/
private lemma uStatistic_eq_hSub_sum (n m : ℕ) (h : (Fin m → α) → ℝ) :
    uStatistic n m h = fun x => (n.choose m : ℝ)⁻¹ * ∑ s : PSElem n m, hSub h s x := by
  ext x; simp only [uStatistic, hSub]; rfl

/-- Each `hSub h s` is in `L²(ν^n)` whenever `h ∈ L²(ν^m)`.
Proof: `hSub h s = h ∘ (fun x => x ∘ ι_S)` where `ι_S : Fin m → Fin n` is the
order embedding; the composition is measurable and the marginal measure on the
image of `ι_S` equals `ν^m` by the iid structure of `ν^n`. -/
private lemma hSub_memLp {n m : ℕ} (h : (Fin m → α) → ℝ)
    (ν : Measure α) [IsProbabilityMeasure ν]
    (h_L2 : MemLp h 2 (Measure.pi (fun _ : Fin m => ν)))
    (h_meas : Measurable h)
    (s : PSElem n m) :
    MemLp (hSub h s) 2 (Measure.pi (fun _ : Fin n => ν)) := by
  have hs : s.val.card = m := Finset.mem_powersetCard_univ.mp s.prop
  -- Factor π_S = φ ∘ ρ where:
  --   p j = j ∈ s.val  (the support predicate)
  --   e : Fin m ≃ {j : Fin n // p j}  (via orderIsoOfFin)
  --   ρ : (Fin n → α) → ({j // p j} → α),  x ↦ fun j => x j.val
  --   φ : ({j // p j} → α) → (Fin m → α),  g ↦ piCongrLeft e.symm g  = g ∘ e
  -- π_S is measure-preserving as a composition of two measure-preserving maps:
  --   (1) ρ = Prod.fst ∘ piEquivPiSubtypeProd p   (measure-preserving by structure)
  --   (2) φ = piCongrLeft e.symm                   (measure-preserving by ordering bijection)
  let p : Fin n → Prop := fun j => j ∈ s.val
  let e : Fin m ≃ {j : Fin n // p j} := (s.val.orderIsoOfFin hs).toEquiv
  let ρ : (Fin n → α) → ({j : Fin n // p j} → α) := fun x j => x j.val
  let φ : ({j : Fin n // p j} → α) → (Fin m → α) := MeasurableEquiv.piCongrLeft (fun _ => α) e.symm
  let π_S : (Fin n → α) → (Fin m → α) := fun x i => x (s.val.orderEmbOfFin hs i)
  have heq : hSub h s = h ∘ π_S := rfl
  rw [heq]
  -- Step 1: π_S = φ ∘ ρ
  have hπ_eq : π_S = φ ∘ ρ := by
    ext x i
    have key : (MeasurableEquiv.piCongrLeft (fun _ => α) e.symm) (ρ x) i = (ρ x) (e i) := by
      simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
    simp only [Function.comp, φ, key, ρ, e, π_S]
    congr 1
  rw [hπ_eq]
  -- Step 2: h ∘ (φ ∘ ρ) = (h ∘ φ) ∘ ρ, and h ∈ L² → h ∘ φ ∈ L² → h ∘ φ ∘ ρ ∈ L²
  apply h_L2.comp_measurePreserving
  apply MeasurePreserving.comp
  · -- MeasurePreserving φ: ν^{Subtype p} → ν^m
    convert measurePreserving_piCongrLeft (fun _ : Fin m => ν) e.symm using 2
  · -- MeasurePreserving ρ: ν^n → ν^{Subtype p}
    have hρ_eq : ρ = Prod.fst ∘ (MeasurableEquiv.piEquivPiSubtypeProd (fun _ => α) p) := by
      ext x j; rfl
    rw [hρ_eq]
    apply MeasurePreserving.comp
    · -- MeasurePreserving Prod.fst: ν^{Subtype p} × ν^{Subtype ¬p} → ν^{Subtype p}
      haveI : IsProbabilityMeasure (Measure.pi (fun _ : {j : Fin n // ¬p j} => ν)) := inferInstance
      exact @measurePreserving_fst _ _ _ _ (Measure.pi (fun _ : {j : Fin n // p j} => ν))
          (Measure.pi (fun _ : {j : Fin n // ¬p j} => ν)) _ _
    · -- MeasurePreserving piEquivPiSubtypeProd: ν^n → ν^{Subtype p} × ν^{Subtype ¬p}
      -- Fix Fintype instance mismatch (Finset.Subtype.fintype vs Subtype.fintype)
      -- using Fintype.subsingleton
      convert measurePreserving_piEquivPiSubtypeProd (fun _ => ν) p using 2
      congr 1; exact Subsingleton.elim _ _

/-- The covariance identity: `cov[h_S, h_T; ν^n] = ζ_{|S ∩ T|}`.
Proof via Fubini + iid + tower property: decompose `ν^n ≅ ν^{S∩T} × ν^{S\T} × ν^{T\S} × ν^{rest}`
using `measurePreserving_piEquivPiSubtypeProd`; `h_S` depends only on `S∩T` and `S\T` coordinates,
while `h_T` depends only on `S∩T` and `T\S`; the `S\T` and `T\S` coordinates are independent,
so after integration `E[h_S h_T] = E[(h_{|S∩T|})^2]` and `E[h_S] = E[h_T] = E[h_{|S∩T|}]`.

Note: requires `h_symm` (kernel symmetry under permutations of `Fin m`).  Without
symmetry the identity is false: `kernelProjection` integrates over the canonical
last `m - k` slots, but the measure-preserving decomposition above produces
marginal integrals over different (subset-dependent) coordinate splits; symmetry
is what makes those marginal integrals equal `kernelProjection m k`.
Counterexample without symmetry: take `α = {0,1}`, `ν` uniform, `m = 2`,
`n = 3`, `h(a, b) = a`, `s = {0,1}`, `t = {1,2}`.  Then `cov[hSub h s, hSub h t] = 0`
(by independence of `x₀` and `x₁`) but `uZeta 2 1 h ν = Var[id; ν] = 1/4`. -/
private lemma cov_hSub_eq_uZeta {n m : ℕ}
    (h : (Fin m → α) → ℝ) (ν : Measure α) [IsProbabilityMeasure ν]
    (h_meas : Measurable h)
    (h_L2 : MemLp h 2 (Measure.pi (fun _ : Fin m => ν)))
    (h_symm : ∀ (x : Fin m → α) (σ : Equiv.Perm (Fin m)), h (x ∘ σ) = h x)
    (s t : PSElem n m) :
    cov[hSub h s, hSub h t; Measure.pi (fun _ : Fin n => ν)] =
    uZeta m (s.val ∩ t.val).card h ν := by
  -- ROADMAP (for next attacker, structural skeleton, NOT executed):
  -- Let k = #(s ∩ t). We have k ≤ m since s ∩ t ⊆ s and #s = m.
  -- Step A: cov[h_S, h_T; ν^n] = ∫ h_S·h_T ∂ν^n − (∫ h_S)(∫ h_T)
  --         via `covariance_eq_sub h_S_L2 h_T_L2` (h_S/h_T in L² by `hSub_memLp`).
  -- Step B: uZeta m k h ν = Var[kernelProjection m k h ν; ν^k]
  --         = ∫ (kP)² ∂ν^k − (∫ kP ∂ν^k)²  via `variance_eq_sub`,
  --         provided `MemLp (kernelProjection m k _ h ν) 2 (ν^k)` (sub-lemma A).
  -- Step C: three integral identities (need 4-way decomposition):
  --   Decompose ν^n ≅ ν^A × ν^B × ν^C × ν^D where
  --     A = s ∩ t,  B = s \ t,  C = t \ s,  D = (s ∪ t)ᶜ.
  --   (1) ∫ h_S ∂ν^n = ∫_{ν^A} ∫_{ν^B} h_S = ∫_{ν^A} kernelProjection m k h ν
  --       (uses h_symm to permute h's input so its last m−k slots are exactly ν^B).
  --   (2) ∫ h_T ∂ν^n = ∫_{ν^A} kernelProjection m k h ν   (similarly via h_symm).
  --   (3) ∫ h_S·h_T ∂ν^n = ∫_{ν^A} (kernelProjection m k h ν)²
  --       (B-integral and C-integral are independent in the product;
  --        h_S depends on A, B; h_T depends on A, C; product splits.)
  -- Combine: cov = (∫ kP²) − (∫ kP)² = Var[kP; ν^k] = uZeta m k h ν.  ∎
  --
  -- Key Mathlib API: `covariance_eq_sub`, `variance_eq_sub`,
  --   `measurePreserving_piEquivPiSubtypeProd` (twice for 4-way),
  --   `measurePreserving_piCongrLeft` (relabelling),
  --   `MeasureTheory.integral_prod` / `integral_prod_symm` (Fubini),
  --   `MemLp.comp_measurePreserving`.
  -- Failure mode WITHOUT h_symm: kernelProjection integrates over the canonical
  -- *last* m−k slots; the measure-preserving decomposition produces marginals over
  -- subset-dependent slots; permutation symmetry is what reconciles them.
  sorry

-- Helper: convert PSElem sum to powersetCard sum
private lemma PSElem_sum_eq (n m : ℕ) (f : Finset (Fin n) → ℝ) :
    ∑ t : PSElem n m, f t.val =
    ∑ t ∈ ((Finset.univ : Finset (Fin n)).powersetCard m), f t := by
  rw [show (Finset.univ : Finset (PSElem n m)) =
      ((Finset.univ : Finset (Fin n)).powersetCard m).attach from Finset.univ_eq_attach _]
  exact Finset.sum_attach _ f

-- Helper: count fibers #{t ∈ powersetCard m univ : #(s ∩ t) = k} = C(m,k)*C(n-m,m-k)
private lemma fiber_card_fixed {n m k : ℕ} (hmk : k ≤ m)
    {s : Finset (Fin n)} (hs_card : #s = m) :
    #(((Finset.univ : Finset (Fin n)).powersetCard m).filter (fun t => #(s ∩ t) = k)) =
    Nat.choose m k * Nat.choose (n - m) (m - k) := by
  rw [show Nat.choose m k * Nat.choose (n - m) (m - k) =
    #(s.powersetCard k ×ˢ (Finset.univ \ s).powersetCard (m - k)) from by
    rw [card_product, card_powersetCard, card_powersetCard, hs_card]
    congr 1; rw [card_sdiff]; simp [card_univ, Fintype.card_fin, hs_card]]
  apply card_bij (fun t _ => (t ∩ s, t \ s))
  · intro t ht
    simp only [mem_filter, mem_powersetCard, subset_univ, true_and] at ht
    obtain ⟨ht_card, hts_card⟩ := ht
    simp only [mem_product, mem_powersetCard]
    refine ⟨⟨inter_subset_right, by rw [inter_comm]; exact hts_card⟩, ?_, ?_⟩
    · intro x hx; exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp hx).2⟩
    · have key := card_inter_add_card_sdiff t s
      rw [inter_comm, hts_card, ht_card] at key; omega
  · intro t₁ _ t₂ _ heq
    simp only [Prod.mk.injEq] at heq
    have h1 : t₁ = t₁ ∩ s ∪ t₁ \ s := by rw [union_comm, sdiff_union_inter]
    have h2 : t₂ = t₂ ∩ s ∪ t₂ \ s := by rw [union_comm, sdiff_union_inter]
    rw [h1, h2, heq.1, heq.2]
  · intro ⟨a, b⟩ hab
    simp only [mem_product, mem_powersetCard] at hab
    obtain ⟨⟨ha_sub, ha_card⟩, hb_sub, hb_card⟩ := hab
    have hb_disj_s : Disjoint b s := disjoint_left.mpr (fun x hxb hxs =>
      (mem_sdiff.mp (hb_sub hxb)).2 hxs)
    refine ⟨a ∪ b, ?_, ?_⟩
    · simp only [mem_filter, mem_powersetCard, subset_univ, true_and]
      refine ⟨?_, ?_⟩
      · rw [card_union_of_disjoint]
        · rw [ha_card, hb_card]; omega
        · exact disjoint_left.mpr (fun x hxa hxb => (mem_sdiff.mp (hb_sub hxb)).2 (ha_sub hxa))
      · rw [inter_union_distrib_left, inter_comm s a, inter_eq_left.mpr ha_sub,
            inter_comm s b, disjoint_iff_inter_eq_empty.mp hb_disj_s, union_empty, ha_card]
    · simp only [Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · rw [union_inter_distrib_right, inter_eq_left.mpr ha_sub,
            disjoint_iff_inter_eq_empty.mp hb_disj_s, union_empty]
      · rw [union_sdiff_distrib, sdiff_eq_empty_iff_subset.mpr ha_sub, empty_union]
        exact sdiff_eq_self_of_disjoint hb_disj_s

-- Helper: for fixed s, the inner sum over PSElem decomposes by intersection cardinality
private lemma inner_sum_by_fiber {n m : ℕ}
    (s : PSElem n m) (f : ℕ → ℝ) :
    ∑ t : PSElem n m, f (s.val ∩ t.val).card =
    ∑ k ∈ Finset.range (m + 1),
        (Nat.choose m k * Nat.choose (n - m) (m - k) : ℝ) * f k := by
  have hs_card : #s.val = m := (mem_powersetCard.mp s.prop).2
  rw [PSElem_sum_eq n m (fun t => f (s.val ∩ t).card)]
  rw [← Finset.sum_fiberwise_of_maps_to
      (g := fun t => (s.val ∩ t).card)
      (t := Finset.range (m + 1))]
  · apply Finset.sum_congr rfl
    intro k _
    rw [show ∑ t ∈ (powersetCard m (univ : Finset (Fin n))).filter
            (fun t => (s.val ∩ t).card = k), f (s.val ∩ t).card =
        ∑ _ ∈ (powersetCard m (univ : Finset (Fin n))).filter
            (fun t => (s.val ∩ t).card = k), f k from by
      apply Finset.sum_congr rfl
      intro t ht; simp only [mem_filter] at ht; rw [ht.2]]
    rw [Finset.sum_const, nsmul_eq_mul]
    by_cases hkm : k ≤ m
    · rw [show #((powersetCard m (univ : Finset (Fin n))).filter (fun t => (s.val ∩ t).card = k)) =
          Nat.choose m k * Nat.choose (n - m) (m - k) from fiber_card_fixed hkm hs_card]
      push_cast; ring
    · push_neg at hkm
      simp only [Nat.choose_eq_zero_of_lt hkm, Nat.cast_zero, zero_mul]
      rw [show (#((powersetCard m (univ : Finset (Fin n))).filter (fun t => (s.val ∩ t).card = k)) : ℝ) = 0 from by
        norm_cast; rw [Finset.card_eq_zero, Finset.filter_false_of_mem]
        intro t _ htk
        exact absurd htk (Nat.lt_of_le_of_lt
          ((Finset.card_le_card Finset.inter_subset_left).trans hs_card.le) hkm |>.ne)]
      ring
  · intro t _
    simp only [mem_range]
    exact Nat.lt_succ_of_le ((Finset.card_le_card Finset.inter_subset_left).trans hs_card.le)

-- Helper: the k=0 HOEFFDING zeta term vanishes (constant kernel projection)
private lemma uZeta_zero {m : ℕ} (h : (Fin m → α) → ℝ) (ν : Measure α) [IsProbabilityMeasure ν] :
    uZeta m 0 h ν = 0 := by
  simp only [uZeta, Nat.zero_le, ↓reduceDIte]
  have hconst : kernelProjection m 0 (Nat.zero_le m) h ν =
      fun _ : Fin 0 → α => kernelProjection m 0 (Nat.zero_le m) h ν Fin.elim0 := by
    ext x; congr 1; exact funext (fun i => i.elim0)
  rw [hconst]; unfold variance
  have : eVar[fun _ : Fin 0 → α => kernelProjection m 0 (Nat.zero_le m) h ν Fin.elim0;
      Measure.pi (fun _ : Fin 0 => ν)] = 0 := by
    rw [(evariance_eq_zero_iff (aemeasurable_const)).mpr]; simp [integral_const]
  rw [this]; simp

/-- The double covariance sum groups by intersection size:
`∑_S ∑_T cov[h_S, h_T] = C(n,m) * ∑_{k=1}^{m} C(m,k)*C(n-m,m-k)*ζ_k`.
Proof: apply `cov_hSub_eq_uZeta`, then group by `|S ∩ T| = k` for `k ∈ {0,…,m}`,
count `#{T : |T|=m, |S∩T|=k} = C(m,k)*C(n-m,m-k)` (for fixed `S`),
and note the `k=0` term vanishes since `ζ_0 = Var[E[h]; ν^0] = 0`. -/
private lemma sum_sum_cov_eq {n m : ℕ} (hmn : m ≤ n)
    (h : (Fin m → α) → ℝ) (ν : Measure α) [IsProbabilityMeasure ν]
    (h_meas : Measurable h)
    (h_L2 : MemLp h 2 (Measure.pi (fun _ : Fin m => ν)))
    (h_symm : ∀ (x : Fin m → α) (σ : Equiv.Perm (Fin m)), h (x ∘ σ) = h x) :
    ∑ s : PSElem n m, ∑ t : PSElem n m,
        cov[hSub h s, hSub h t; Measure.pi (fun _ : Fin n => ν)] =
    (n.choose m : ℝ) * ∑ k ∈ Finset.Icc 1 m,
        ((m.choose k : ℝ) * ((n - m).choose (m - k) : ℝ)) * uZeta m k h ν := by
  -- Step 1: apply covariance identity
  simp_rw [cov_hSub_eq_uZeta h ν h_meas h_L2 h_symm]
  -- Step 2: apply inner sum fiber decomposition
  simp_rw [inner_sum_by_fiber _ (fun k => uZeta m k h ν)]
  -- LHS = ∑ s : PSElem n m, ∑ k ∈ range (m+1), C(m,k)*C(n-m,m-k) * uZeta m k h ν
  -- Step 3: pull the outer sum inside (the inner sum is constant in s)
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [show (Finset.univ : Finset (PSElem n m)).card = n.choose m from by
    rw [Finset.card_univ, Fintype.card_coe, Finset.card_powersetCard]; simp]
  -- Step 4: the sum over range(m+1) equals the sum over Icc 1 m
  -- because the k=0 term vanishes (uZeta m 0 = 0)
  congr 1
  symm
  apply Finset.sum_subset (s₁ := Finset.Icc 1 m) (s₂ := Finset.range (m + 1))
  · intro k hk; simp only [mem_Icc, mem_range] at hk ⊢; omega
  · intro k hk_range hk_not_Icc
    simp only [mem_Icc, not_and_or, not_le] at hk_not_Icc
    simp only [mem_range] at hk_range
    -- k ∈ range (m+1) and k ∉ Icc 1 m means k = 0
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [Nat.choose_zero_right, Nat.sub_zero, Nat.cast_one, one_mul, uZeta_zero, mul_zero]

end VarDecomp

/-- **Hoeffding's theorem (Shao §3.2.2, Thm 3.4).** For an iid sample on a
probability space `(α, ν)` and a symmetric kernel `h : (Fin m → α) → ℝ` of
order `m ≤ n` with `h ∈ L²(ν^m)`, the variance of the U-statistic
`Uₙ` decomposes as
`Var(Uₙ) = C(n,m)⁻¹ ∑_{k=1}^{m} C(m,k) C(n-m, m-k) ζ_k`,
where `ζ_k = Var(h_k(X₁,…,X_k))`.

Proof sketch:
1. Center: let `h̃ = h - E[h]`. By symmetry,
   `Uₙ - E(Uₙ) = C(n,m)⁻¹ ∑_S h̃(X_S)` (eq. 3.16).
2. Expand: `Var(Uₙ) = E[(Uₙ - EUₙ)²]
   = C(n,m)⁻² ∑_S ∑_T E[h̃(X_S) h̃(X_T)]`.
3. Covariance identity (eq. 3.17): `E[h̃(X_S) h̃(X_T)] = ζ_{|S∩T|}`.
   Proof: integrate out the `|S△T|` independent coordinates via Fubini + tower
   property; what remains is `E[(h_{|S∩T|} - Eh)²] = ζ_{|S∩T|}`.
4. Count: `#{(S,T) : |S|=|T|=m, |S∩T|=k} = C(n,m) C(m,k) C(n-m, m-k)`.
   (For fixed S, choose k from S and m-k from the n-m element complement.)
5. Collect: `Var(Uₙ) = C(n,m)⁻¹ ∑_k C(m,k) C(n-m,m-k) ζ_k`. -/
theorem u_statistic_variance_decomposition
    {n m : ℕ} (hmn : m ≤ n) (hm : 1 ≤ m)
    (ν : Measure α) [IsProbabilityMeasure ν]
    (h : (Fin m → α) → ℝ)
    (h_meas : Measurable h)
    (h_L2 : MemLp h 2 (Measure.pi (fun _ : Fin m => ν)))
    (h_symm : ∀ (x : Fin m → α) (σ : Equiv.Perm (Fin m)), h (x ∘ σ) = h x) :
    Var[uStatistic n m h ; Measure.pi (fun _ : Fin n => ν)]
      = ((n.choose m : ℝ))⁻¹ *
          ∑ k ∈ Finset.Icc 1 m,
            ((m.choose k : ℝ) * ((n - m).choose (m - k) : ℝ)) * uZeta m k h ν := by
  -- Step 1: rewrite uStatistic as c * ∑_S h_S, then apply variance_const_mul + variance_sum'
  rw [uStatistic_eq_hSub_sum n m h]
  simp_rw [show (fun x : Fin n → α => (n.choose m : ℝ)⁻¹ * ∑ s : PSElem n m, hSub h s x) =
    fun x => (n.choose m : ℝ)⁻¹ * (∑ s : PSElem n m, hSub h s) x from by
    ext x; simp [Finset.sum_apply]]
  rw [variance_const_mul]
  rw [variance_sum' (s := Finset.univ) (fun s _ => hSub_memLp h ν h_L2 h_meas s)]
  -- Step 2: apply the combinatorial grouping lemma (which uses cov identity internally)
  rw [sum_sum_cov_eq hmn h ν h_meas h_L2 h_symm]
  -- Step 3: algebra  c^2 * (C(n,m) * Z) = c * Z  where c = C(n,m)⁻¹
  by_cases hn : (n.choose m : ℝ) = 0
  · -- degenerate case: m > n, so C(n,m) = 0
    simp [hn]
  · -- generic case: cancel one C(n,m)
    field_simp [hn]

/-! ## Asymptotic distribution of U-statistics (Shao §3.2.2, Theorem 3.5)

For a U-statistic `U_n` of degree `m` with `L²` symmetric kernel `h`:

* Part **(i)** (non-degenerate): if `ζ_1 > 0`, then
  `√n (U_n − E U_n) →_d N(0, m² ζ_1)`.
  Proof via the Hájek projection (Hoeffding decomposition):
  `√n (U_n − E U_n) − √n · m · ((1/n) ∑_i (h_1(X_i) − E h_1)) →_{L²} 0`
  (variance bound `O(1/n)`), and the projection sum has variance
  `m² ζ_1` and converges to `N(0, m² ζ_1)` by the classical CLT.

* Part **(ii)** (degenerate): if `ζ_1 = 0` and `ζ_2 > 0`, then
  `n (U_n − E U_n) →_d (m(m−1)/2) Σ_j λ_j (χ²_{1j} − 1)`,
  where `χ²_{1j}` are iid `χ²(1)` and `Σ λ_j² = ζ_2`.
  Proof via spectral decomposition of the Hilbert–Schmidt operator
  with kernel `h_2` (Serfling 1980 §5.5.2). Mathlib lacks chi-square
  distributions and infinite-series convergence for iid χ², so the
  limit is identified existentially by its moment characterisation
  (Lemma 3.2: `EY = 0`, `EY² = m²(m−1)²ζ_2/2`).
-/

section AsymptoticDistribution

/-- The expected value of the U-statistic `Uₙ` under the iid product
measure `νⁿ`. -/
noncomputable def uStatisticMean (n m : ℕ) (h : (Fin m → α) → ℝ)
    (ν : Measure α) : ℝ :=
  ∫ x, uStatistic n m h x ∂(Measure.pi (fun _ : Fin n => ν))

/-- The pushforward law of `c · (Uₙ − E Uₙ)` on ℝ as a (formally constructed)
measure. The `IsProbabilityMeasure` instance is established separately for
each scaling regime in the asymptotic theorems below. -/
noncomputable def uStatisticCenteredLaw (n m : ℕ) (c : ℝ)
    (h : (Fin m → α) → ℝ) (ν : Measure α) : Measure ℝ :=
  (Measure.pi (fun _ : Fin n => ν)).map
    (fun x : Fin n → α => c * (uStatistic n m h x - uStatisticMean n m h ν))

/-! ### Sub-lemmas for the non-degenerate U-statistic CLT (Hájek projection method)

The proof of `ustatistic_clt_nondegenerate` is decomposed into 5 steps following
the Hájek projection / Hoeffding decomposition argument. The sub-lemmas below
provide the key intermediate results. -/

/-- **Sub-lemma 1 (Hájek projection sum)**: The Hájek projection of the U-statistic
is the sum `T_n = (m/n) ∑ᵢ (h₁(Xᵢ) − E[h₁])`, where
`h₁(x) = kernelProjection m 1 hm h ν (fun _ => x)` is the first-order projection
and `E[h₁] = kernelProjection m 0 (Nat.zero_le m) h ν Fin.elim0`.

The key fact used is that `uZeta m 1 h ν = Var[h₁ ; ν]`. -/
noncomputable def hajekProjection (m : ℕ) (hm : 1 ≤ m) (h : (Fin m → α) → ℝ)
    (ν : Measure α) [IsProbabilityMeasure ν] (n : ℕ) (x : Fin n → α) : ℝ :=
  let h1 : α → ℝ := fun xi => kernelProjection m 1 hm h ν (fun _ => xi)
  let μh1 : ℝ := kernelProjection m 0 (Nat.zero_le m) h ν Fin.elim0
  (↑m / ↑n) * ∑ i : Fin n, (h1 (x i) - μh1)

-- Helper: measurability of (xi, y) ↦ appendFin hm (fun _ => xi) y
private lemma appendFin_const_measurable {m : ℕ} (hm : 1 ≤ m) :
    Measurable (fun p : α × (Fin (m - 1) → α) =>
      appendFin hm (fun _ : Fin 1 => p.1) p.2) := by
  apply measurable_pi_lambda
  intro j
  rcases Nat.lt_or_ge j.val 1 with h1 | h1
  · convert measurable_fst using 1
    ext p; exact appendFin_castAdd_apply hm (fun _ => p.1) p.2 j (by omega)
  · have hmk : j.val - 1 < m - 1 := by omega
    have heq : ∀ p : α × (Fin (m - 1) → α),
        appendFin hm (fun _ : Fin 1 => p.1) p.2 j = p.2 ⟨j.val - 1, hmk⟩ :=
      fun p => appendFin_natAdd_apply hm (fun _ => p.1) p.2 j h1
    simp_rw [heq]
    exact (measurable_pi_apply (⟨j.val - 1, hmk⟩ : Fin (m - 1))).comp measurable_snd

-- Helper: the first-order kernel projection is measurable as a function of the first coordinate
private lemma kernelProjection_one_measurable
    {m : ℕ} (hm : 1 ≤ m) (h : (Fin m → α) → ℝ) (ν : Measure α) [IsProbabilityMeasure ν]
    (h_meas : Measurable h) :
    Measurable (fun xi : α => kernelProjection m 1 hm h ν (fun _ => xi)) := by
  simp only [kernelProjection]
  apply (StronglyMeasurable.integral_prod_right _).measurable
  exact h_meas.stronglyMeasurable.comp_measurable (appendFin_const_measurable hm)

-- Helper: appendFin hm (fun _ => xi) y = Fin.cons xi y
private lemma appendFin_one_eq_cons_aux {m' : ℕ} (xi : α) (y : Fin m' → α) :
    appendFin (Nat.succ_le_succ (Nat.zero_le m')) (fun _ : Fin 1 => xi) y = Fin.cons xi y := by
  funext i; refine Fin.cases ?_ ?_ i
  · rw [appendFin_castAdd_apply _ _ _ 0 (by norm_num)]; simp [Fin.cons]
  · intro j; rw [appendFin_natAdd_apply _ _ _ j.succ (by simp [Fin.val_succ])]
    simp only [Fin.cons_succ, Fin.val_succ]; congr 1

-- Helper: kernelProjection m 1 hm h ν (fun _ => xi) = ∫ y, h(Fin.cons xi y)
private lemma kernelProjection_one_eq_fubini {m' : ℕ} (hm : 1 ≤ m'+1) (xi : α)
    (ν : Measure α) (h : (Fin (m'+1) → α) → ℝ) :
    kernelProjection (m'+1) 1 hm h ν (fun _ => xi) =
    ∫ y : Fin m' → α, h (Fin.cons xi y) ∂ Measure.pi (fun _ : Fin m' => ν) := by
  simp only [kernelProjection, Nat.succ_sub_one]
  conv_lhs => arg 2; ext y; rw [appendFin_one_eq_cons_aux xi y]

-- Helper: Fubini decomposition pi(m'+1) → ν × pi(m')
private lemma fubini_piSucc_eq {m' : ℕ} (nu : Measure α) [IsProbabilityMeasure nu]
    (f : (Fin (m'+1) → α) → ℝ) (hf : Measurable f)
    (hf_int : Integrable f (Measure.pi (fun _ : Fin (m'+1) => nu))) :
    ∫ z : Fin (m'+1) → α, f z ∂(Measure.pi (fun _ : Fin (m'+1) => nu)) =
    ∫ xi : α, ∫ y : Fin m' → α, f (Fin.cons xi y) ∂(Measure.pi (fun _ : Fin m' => nu)) ∂nu := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m'+1) => α) 0
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m'+1) => nu) 0
  have hf_int2 : Integrable (fun p : α × (Fin m' → α) => f (e.symm p))
      (nu.prod (Measure.pi (fun _ : Fin m' => nu))) := by
    rw [show (fun p => f (e.symm p)) = f ∘ e.symm from rfl]
    exact (hmp.symm e).integrable_comp hf.aestronglyMeasurable |>.mpr hf_int
  have step1 : ∫ z, f z ∂(Measure.pi (fun _ : Fin (m'+1) => nu)) =
      ∫ p : α × (Fin m' → α), f (e.symm p) ∂(nu.prod (Measure.pi (fun _ : Fin m' => nu))) := by
    have := hmp.integral_comp' (f ∘ e.symm)
    simp only [Function.comp] at this; convert this using 2
    ext z; simp [e, MeasurableEquiv.piFinSuccAbove, Fin.consEquiv]
  rw [step1, integral_prod _ hf_int2]
  congr 1; ext xi; congr 1; ext y
  simp [e, MeasurableEquiv.piFinSuccAbove, Fin.consEquiv]

-- Helper: outer integral of Fubini is integrable
private lemma fubini_piSucc_integrable {m' : ℕ} (nu : Measure α) [IsProbabilityMeasure nu]
    (f : (Fin (m'+1) → α) → ℝ) (hf : Measurable f)
    (hf_int : Integrable f (Measure.pi (fun _ : Fin (m'+1) => nu))) :
    Integrable (fun xi : α =>
      ∫ y : Fin m' → α, f (Fin.cons xi y) ∂(Measure.pi (fun _ : Fin m' => nu))) nu := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m'+1) => α) 0
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m'+1) => nu) 0
  have hf_int2 : Integrable (fun p : α × (Fin m' → α) => f (e.symm p))
      (nu.prod (Measure.pi (fun _ : Fin m' => nu))) := by
    rw [show (fun p => f (e.symm p)) = f ∘ e.symm from rfl]
    exact (hmp.symm e).integrable_comp hf.aestronglyMeasurable |>.mpr hf_int
  have hslice := hf_int2.integral_prod_left
  apply hslice.congr
  filter_upwards with xi
  congr 1; ext y; congr 1
  simp [e, MeasurableEquiv.piFinSuccAbove, Fin.consEquiv]

-- Helper: Jensen (E[f])² ≤ E[f²] for probability measures
private lemma sq_integral_le_integral_sq_prob_aux {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf2 : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, f x ∂μ)^2 ≤ ∫ x, f x ^ 2 ∂μ := by
  by_cases hf : Integrable f μ
  · set c := ∫ x, f x ∂μ
    have h2fc : Integrable (fun x => 2 * f x * c) μ :=
      (hf.const_mul (2 * c)).congr (by filter_upwards with x; ring)
    have hfm2fc : Integrable (fun x => f x ^ 2 - 2 * f x * c) μ := hf2.sub h2fc
    have key : 0 ≤ ∫ x : Ω, (f x - c)^2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
    have expand : ∫ x : Ω, (f x - c)^2 ∂μ = ∫ x, f x ^ 2 ∂μ - c^2 := by
      rw [show (fun x => (f x - c)^2) =
          (fun x => (f x ^ 2 - 2 * f x * c) + c^2) from by ext x; ring]
      rw [integral_add hfm2fc (integrable_const _), integral_sub hf2 h2fc, integral_const]
      simp only [smul_eq_mul, measureReal_univ_eq_one, mul_one]
      rw [show (fun x => 2 * f x * c) = (fun x => (2*c) * f x) from by ext x; ring, integral_const_mul]
      ring
    linarith
  · rw [integral_undef hf, sq (0:ℝ), zero_mul]
    exact integral_nonneg (fun x => sq_nonneg _)

-- Helper: h1² is integrable under ν
private lemma kernelProjection_one_sq_integrable {m' : ℕ} (hm : 1 ≤ m'+1)
    (h : (Fin (m'+1) → α) → ℝ) (ν : Measure α) [IsProbabilityMeasure ν]
    (h_meas : Measurable h) (h_L2 : MemLp h 2 (Measure.pi (fun _ : Fin (m'+1) => ν))) :
    Integrable (fun xi : α =>
      (kernelProjection (m'+1) 1 hm h ν (fun _ => xi))^2) ν := by
  have h_sq_int := h_L2.integrable_sq
  have hbound_int := fubini_piSucc_integrable ν
    (fun z : Fin (m'+1) → α => h z ^ 2) (h_meas.pow_const _) h_sq_int
  -- ae slice integrability
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m'+1) => α) 0
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m'+1) => ν) 0
  have h_sq_int2 : Integrable (fun p : α × (Fin m' → α) => h (e.symm p) ^ 2)
      (ν.prod (Measure.pi (fun _ : Fin m' => ν))) := by
    rw [show (fun p => h (e.symm p) ^ 2) = (fun z => h z ^ 2) ∘ e.symm from rfl]
    exact (hmp.symm e).integrable_comp (h_meas.pow_const 2).aestronglyMeasurable |>.mpr h_sq_int
  have hslice_ae := h_sq_int2.prod_right_ae
  have hslice_ae2 : ∀ᵐ xi : α ∂ν, Integrable (fun y : Fin m' → α => h (Fin.cons xi y) ^ 2)
      (Measure.pi (fun _ : Fin m' => ν)) := by
    filter_upwards [hslice_ae] with xi hxi
    apply hxi.congr; filter_upwards with y
    congr 1; congr 1; simp [e, MeasurableEquiv.piFinSuccAbove, Fin.consEquiv]
  apply Integrable.mono hbound_int
    ((kernelProjection_one_measurable hm h ν h_meas).pow_const _ |>.aestronglyMeasurable)
  filter_upwards [hslice_ae2] with xi hxi_sq
  rw [Real.norm_eq_abs, abs_sq, Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg (fun y => sq_nonneg _))]
  rw [kernelProjection_one_eq_fubini hm xi ν h]
  exact sq_integral_le_integral_sq_prob_aux (Measure.pi (fun _ : Fin m' => ν))
    (fun y => h (Fin.cons xi y)) hxi_sq

-- Helper: finToRangeEquiv and infinitePi maps to pi
private noncomputable def finToRangeEquiv_aux (n : ℕ) : Fin n ≃ ↑(Finset.range n) where
  toFun i := ⟨i.val, Finset.mem_range.mpr i.isLt⟩
  invFun j := ⟨j.val, Finset.mem_range.mp j.prop⟩
  left_inv i := Fin.ext rfl
  right_inv j := Subtype.ext rfl

private lemma infinitePi_map_fin_proj_aux (n : ℕ) (ν : Measure α) [IsProbabilityMeasure ν] :
    (Measure.infinitePi (fun _ : ℕ => ν)).map (fun ω : ℕ → α => fun i : Fin n => ω i) =
    Measure.pi (fun _ : Fin n => ν) := by
  let e := finToRangeEquiv_aux n
  let me := MeasurableEquiv.piCongrLeft (fun _ => α) e
  have hfactor : (fun ω : ℕ → α => fun i : Fin n => ω i) = me.symm ∘ (Finset.range n).restrict := by
    funext ω i
    simp only [Function.comp, MeasurableEquiv.symm, MeasurableEquiv.coe_mk,
      Equiv.piCongrLeft_symm_apply, Finset.restrict]; rfl
  rw [hfactor, ← Measure.map_map me.symm.measurable (by fun_prop), Measure.infinitePi_map_restrict]
  exact (measurePreserving_piCongrLeft (fun _ => ν) e).symm.map_eq

-- Helper: Lindeberg condition for iid threshold sets
private lemma lindeberg_setIntegral_tendsto (ν : Measure α) [IsProbabilityMeasure ν]
    (Z : α → ℝ) (hZ_meas : Measurable Z) (hZ_sq_int : Integrable (fun x => Z x ^ 2) ν)
    (ε ζ : ℝ) (hε : 0 < ε) (hζ : 0 < ζ) :
    Filter.Tendsto (fun n : ℕ =>
        ∫ x in {x : α | ε * Real.sqrt (ζ * (↑n + 1)) < |Z x|}, Z x ^ 2 ∂ν)
      Filter.atTop (nhds 0) := by
  let S : ℕ → Set α := fun n => {x | ε * Real.sqrt (ζ * (↑n + 1)) < |Z x|}
  have hS_meas : ∀ n, NullMeasurableSet (S n) ν :=
    fun n => (measurableSet_lt (by fun_prop) hZ_meas.abs).nullMeasurableSet
  have hS_anti : Antitone S := by
    intro m n hmn x hx
    simp only [S, Set.mem_setOf_eq] at *
    exact lt_of_le_of_lt (by gcongr) hx
  have hS_inter_empty : ⋂ n, S n = ∅ := by
    ext x; simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, S, Set.mem_setOf_eq]
    push_neg
    have hlim : Filter.Tendsto (fun n : ℕ => ε * Real.sqrt (ζ * (↑n + 1))) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop hε (Real.tendsto_sqrt_atTop.comp
        (Filter.Tendsto.const_mul_atTop hζ
          (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)))
    obtain ⟨n, hn⟩ := (hlim.eventually_ge_atTop (|Z x|)).exists
    exact ⟨n, hn⟩
  have hν_S_tendsto : Filter.Tendsto (ν ∘ S) Filter.atTop (nhds 0) := by
    have hconv := tendsto_measure_iInter_atTop (s := S)
      hS_meas hS_anti ⟨0, measure_ne_top ν _⟩
    simp only [hS_inter_empty, measure_empty] at hconv
    exact hconv
  apply hZ_sq_int.tendsto_setIntegral_nhds_zero
  convert hν_S_tendsto using 1

-- Helper: appendFin with k=0 and empty prefix = identity
omit [MeasurableSpace α] in
private lemma appendFin_zero_elim0_aux {m : ℕ} (y : Fin m → α) :
    appendFin (Nat.zero_le m) Fin.elim0 y = y := by
  funext i; simp [appendFin, Fin.append, Fin.addCases]

-- Helper: ∫ xi, h1(xi) dν = kernelProjection m 0 h ν Fin.elim0 = ∫ h dν^m
private lemma integral_h1_eq_kp0_aux {m' : ℕ} (hm : 1 ≤ m'+1)
    (h : (Fin (m'+1) → α) → ℝ) (h_meas : Measurable h) (ν : Measure α) [IsProbabilityMeasure ν]
    (h_int : Integrable h (Measure.pi (fun _ : Fin (m'+1) => ν))) :
    ∫ xi : α, kernelProjection (m'+1) 1 hm h ν (fun _ => xi) ∂ν =
    kernelProjection (m'+1) 0 (Nat.zero_le _) h ν Fin.elim0 := by
  rw [show kernelProjection (m'+1) 0 (Nat.zero_le _) h ν Fin.elim0 =
      ∫ z : Fin (m'+1) → α, h z ∂Measure.pi (fun _ : Fin (m'+1) => ν) from by
    simp only [kernelProjection, Nat.sub_zero, appendFin_zero_elim0_aux]]
  rw [show (∫ z : Fin (m'+1) → α, h z ∂Measure.pi (fun _ : Fin (m'+1) => ν)) =
      ∫ xi : α, ∫ y : Fin m' → α, h (Fin.cons xi y) ∂(Measure.pi (fun _ : Fin m' => ν)) ∂ν from
    fubini_piSucc_eq ν h h_meas h_int]
  congr 1; ext xi
  simp only [kernelProjection, Nat.succ_sub_one]
  congr 1; ext y; rw [appendFin_one_eq_cons_aux xi y]

-- Helper: uZeta m 1 h ν = Var[h1; ν] where h1 xi = kernelProjection m 1 hm h ν (fun _ => xi)
private lemma uZeta_one_eq_var_aux {m' : ℕ} (hm : 1 ≤ m'+1)
    (h : (Fin (m'+1) → α) → ℝ) (ν : Measure α) [IsProbabilityMeasure ν]
    (h_meas : Measurable h) :
    uZeta (m'+1) 1 h ν = Var[fun xi : α =>
      kernelProjection (m'+1) 1 hm h ν (fun _ => xi) ; ν] := by
  simp only [uZeta, dif_pos hm]
  show Var[fun y : Fin 1 → α => kernelProjection (m'+1) 1 hm h ν y; Measure.pi (fun _ : Fin 1 => ν)] =
      Var[fun xi : α => kernelProjection (m'+1) 1 hm h ν (fun _ => xi) ; ν]
  conv_lhs =>
    arg 1; ext y
    rw [show kernelProjection (m'+1) 1 hm h ν y =
        (fun xi => kernelProjection (m'+1) 1 hm h ν (fun _ => xi)) (y 0) from by
      congr 1; funext j; fin_cases j; simp]
  exact (measurePreserving_piUnique (fun _ : Fin 1 => ν)).variance_fun_comp
    (kernelProjection_one_measurable hm h ν h_meas).aemeasurable

-- Helper: ∫ ω : ℕ → α, (Z(ω j))² ∂infinitePi = ∫ x, (Z x)² ∂ν
private lemma integral_sq_infinitePi_marginal (ν : Measure α) [IsProbabilityMeasure ν]
    (Z : α → ℝ) (hZ : Measurable Z) (j : ℕ) :
    ∫ ω : ℕ → α, (Z (ω j))^2 ∂Measure.infinitePi (fun _ : ℕ => ν) =
    ∫ x : α, (Z x)^2 ∂ν := by
  have key := Measure.infinitePi_map_eval (fun _ : ℕ => ν) j
  calc ∫ ω : ℕ → α, (Z (ω j))^2 ∂Measure.infinitePi (fun _ : ℕ => ν)
      = ∫ x : α, (Z x)^2 ∂((Measure.infinitePi (fun _ : ℕ => ν)).map (fun ω => ω j)) := by
        rw [integral_map (measurable_pi_apply j).aemeasurable
            (hZ.pow_const 2 |>.aestronglyMeasurable)]
    _ = ∫ x : α, (Z x)^2 ∂ν := by rw [key]

-- Helper: setIntegral over {ω | s < |Z(ω j)|} under infinitePi = setIntegral over {x | s < |Z x|} under ν
private lemma setIntegral_infinitePi_marginal (ν : Measure α) [IsProbabilityMeasure ν]
    (Z : α → ℝ) (hZ : Measurable Z) (j : ℕ) (s : ℝ) :
    ∫ ω : ℕ → α in {ω : ℕ → α | s < |Z (ω j)|}, (Z (ω j))^2
      ∂Measure.infinitePi (fun _ : ℕ => ν) =
    ∫ x : α in {x : α | s < |Z x|}, (Z x)^2 ∂ν := by
  have key := Measure.infinitePi_map_eval (fun _ : ℕ => ν) j
  have hset_meas : MeasurableSet {x : α | s < |Z x|} :=
    measurableSet_lt measurable_const hZ.abs
  conv_rhs => rw [← key]
  rw [setIntegral_map hset_meas (hZ.pow_const 2).aestronglyMeasurable
    (measurable_pi_apply j).aemeasurable]
  rfl

/-- **Sub-lemma 2 (CLT for Hájek projection)**: The rescaled Hájek projection
`√n · T_n` converges in distribution to `N(0, m² ζ_1)`.

Proof: Set `h₁ (x) − E[h₁]` as centered iid random variables on the ambient
probability space `(ℕ → α, ν^ℕ)` (via `Measure.infinitePi`), with variance `ζ_1`.
Apply `central_limit_theorem` to get `(∑ h₁(Xᵢ)) / (√ζ_1 · √n) →ᵈ N(0,1)`.
Rescale by `m · √ζ_1` to get `N(0, m² ζ_1)`. -/
lemma hajek_clt
    {m : ℕ} (hm : 1 ≤ m)
    (h : (Fin m → α) → ℝ)
    (h_meas : Measurable h)
    (ν : Measure α) [IsProbabilityMeasure ν]
    (h_L2 : MemLp h 2 (Measure.pi (fun _ : Fin m => ν)))
    (h_zeta1_pos : 0 < uZeta m 1 h ν) :
    let h1 : α → ℝ := fun xi => kernelProjection m 1 hm h ν (fun _ => xi)
    let μh1 : ℝ := kernelProjection m 0 (Nat.zero_le m) h ν Fin.elim0
    -- The rescaled Hájek sum T_n^* = (m/√n) ∑ᵢ(h₁(Xᵢ) − μh₁) as law under ν^n
    let hajekLaw : ℕ → ProbabilityMeasure ℝ := fun n =>
      ⟨(Measure.pi (fun _ : Fin n => ν)).map
        (fun x : Fin n → α => (↑m / Real.sqrt ↑n) * ∑ i : Fin n, (h1 (x i) - μh1)),
       by
         apply Measure.isProbabilityMeasure_map
         -- h1 is measurable: follows from StronglyMeasurable.integral_prod_right applied
         -- to the jointly measurable (xi, y) ↦ h (appendFin hm (fun _ => xi) y).
         -- Then (fun x => ∑ i, (h1(x i) - μh1)) is measurable by finite sum.
         apply Measurable.aemeasurable
         apply Measurable.const_mul
         apply Finset.measurable_sum (Finset.univ : Finset (Fin _))
         intro i _
         -- measurability of xi ↦ h1(x i) - μh1 where h1(xi) = ∫ h(xi, y) dν^{m-1}
         exact ((kernelProjection_one_measurable hm h ν h_meas).comp
           (measurable_pi_apply i)).sub_const μh1⟩
    let gaussLimit : ProbabilityMeasure ℝ :=
      ⟨gaussianReal 0
        ⟨(m : ℝ)^2 * uZeta m 1 h ν, mul_nonneg (sq_nonneg _) (uZeta_nonneg m 1 h ν)⟩,
       inferInstance⟩
    Filter.Tendsto hajekLaw Filter.atTop (nhds gaussLimit) := by
  -- Decompose m = m'+1
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  intro h1 μh1 hajekLaw gaussLimit
  -- Ambient probability space
  let μlim := Measure.infinitePi (fun _ : ℕ => ν)
  haveI : IsProbabilityMeasure μlim := inferInstance
  -- Centered h1: Z(xi) = h1(xi) - μh1
  let Z : α → ℝ := fun xi => h1 xi - μh1
  have hZ_meas : Measurable Z := (kernelProjection_one_measurable hm h ν h_meas).sub_const _
  -- L¹ integrability of h (needed for Fubini/mean)
  have h_int : Integrable h (Measure.pi (fun _ : Fin (m'+1) => ν)) :=
    h_L2.integrable (by norm_num)
  have hmeas_h1 : Measurable h1 := kernelProjection_one_measurable hm h ν h_meas
  have hh1_sq_int : Integrable (fun xi : α => h1 xi ^ 2) ν :=
    kernelProjection_one_sq_integrable hm h ν h_meas h_L2
  have hh1_memLp2 : MemLp h1 2 ν := by
    rw [memLp_two_iff_integrable_sq_norm hmeas_h1.aestronglyMeasurable]
    simp only [Real.norm_eq_abs, sq_abs]; exact hh1_sq_int
  have hh1_int : Integrable h1 ν := hh1_memLp2.integrable (by norm_num)
  -- Square integrability of Z under ν.
  -- Z² = h1² - 2 μh1 h1 + μh1², so use linearity from Integrable h1².
  have h_sq_int : Integrable (fun x => Z x ^ 2) ν := by
    have hZsq_eq : (fun x => Z x ^ 2) =
        (fun x => h1 x ^ 2 - 2 * μh1 * h1 x + μh1 ^ 2) := by
      ext x; simp only [Z]; ring
    rw [hZsq_eq]
    refine ((hh1_sq_int.sub ((hh1_int.const_mul (2 * μh1)).congr ?_)).add (integrable_const _))
    filter_upwards with x; ring
  -- Mean of Z = 0
  have hZ_mean : ∫ xi : α, Z xi ∂ν = 0 := by
    have hZeq : (fun xi : α => Z xi) = (fun xi => h1 xi - μh1) := by
      ext xi; simp [Z]
    rw [show (∫ xi, Z xi ∂ν) = ∫ xi, (h1 xi - μh1) ∂ν from by
      apply integral_congr_ae; filter_upwards with xi; simp [Z]]
    rw [integral_sub hh1_int (integrable_const _)]
    rw [integral_h1_eq_kp0_aux hm h h_meas ν h_int]
    simp [μh1]
  -- ζ₁ = uZeta (m'+1) 1 h ν = Var[Z ; ν]
  let ζ₁ := uZeta (m'+1) 1 h ν
  have hζ₁_eq : ζ₁ = Var[Z ; ν] := by
    show uZeta (m'+1) 1 h ν = Var[Z ; ν]
    rw [uZeta_one_eq_var_aux hm h ν h_meas]
    -- Var[h1; ν] = Var[h1 - μh1; ν] (variance invariant under constant shift)
    show Var[h1 ; ν] = Var[fun xi => h1 xi - μh1 ; ν]
    rw [ProbabilityTheory.variance_sub_const hmeas_h1.aestronglyMeasurable]
  have hζ₁_pos : 0 < ζ₁ := h_zeta1_pos
  -- Normalizer sn n = sqrt(ζ₁ * (n+1))
  let sn : ℕ → ℝ := fun n => Real.sqrt (ζ₁ * (↑n + 1))
  have hsn_pos : ∀ n, 0 < sn n := fun n => Real.sqrt_pos.mpr (by positivity)
  -- Triangular array: Xnj n j ω = Z(ω j)  (j : Fin (n+1), ω : ℕ → α)
  let Xnj : (n : ℕ) → Fin (n + 1) → (ℕ → α) → ℝ := fun _n j ω => Z (ω j.val)
  -- Check hypotheses for lindeberg_feller_clt
  -- (a) Measurability
  have hXnj_meas : ∀ n j, Measurable (Xnj n j) := fun _n j =>
    hZ_meas.comp (measurable_pi_apply j.val)
  -- (b) Independence
  have hindep : ∀ n, iIndepFun (m := fun _ => inferInstance) (Xnj n) μlim := fun _n =>
    (iIndepFun_infinitePi (fun _ => hZ_meas)).precomp Fin.val_injective
  -- (c) Mean zero (using marginal property of infinitePi)
  have hmean : ∀ n j, ∫ ω, Xnj n j ω ∂μlim = 0 := fun _n j => by
    have key : (∫ ω, Xnj _n j ω ∂μlim) = ∫ x : α, Z x ∂ν := by
      show (∫ ω, Z (ω j.val) ∂μlim) = ∫ x, Z x ∂ν
      have hmap : (μlim.map (fun ω : ℕ → α => ω j.val)) = ν :=
        Measure.infinitePi_map_eval _ _
      conv_rhs => rw [← hmap]
      rw [integral_map (measurable_pi_apply j.val).aemeasurable
        (by rw [hmap]; exact hZ_meas.aestronglyMeasurable)]
    rw [key]; exact hZ_mean
  -- (d) L² condition
  have hL2clf : ∀ n j, MemLp (Xnj n j) 2 μlim := fun _n j => by
    rw [memLp_two_iff_integrable_sq_norm (hXnj_meas _n j).aestronglyMeasurable]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [show (fun ω : ℕ → α => Xnj _n j ω ^ 2) = (fun x : α => Z x ^ 2) ∘ (fun ω => ω j.val) from rfl]
    refine Integrable.comp_measurable ?_ (measurable_pi_apply j.val)
    rw [Measure.infinitePi_map_eval]
    exact h_sq_int
  -- (e) Variance sum: ∑ j : Fin (n+1), Var[Xnj n j; μlim] = sn n²
  have hvar_sum : ∀ n, ∑ j : Fin (n+1), ∫ ω, (Xnj n j ω)^2 ∂μlim = (sn n)^2 := fun n => by
    conv_lhs => arg 2; ext j; rw [integral_sq_infinitePi_marginal ν Z hZ_meas j.val]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Real.sq_sqrt (by positivity)]
    -- Goal: (n+1) • ∫ Z² ∂ν = ζ₁ * (n+1)
    have hint_sq : ∫ x : α, Z x ^ 2 ∂ν = ζ₁ := by
      have hZ_memLp2 : MemLp Z 2 ν := by
        rw [memLp_two_iff_integrable_sq_norm hZ_meas.aestronglyMeasurable]
        simp only [Real.norm_eq_abs, sq_abs]; exact h_sq_int
      rw [hζ₁_eq, variance_eq_sub hZ_memLp2, hZ_mean]
      simp only [Pi.pow_apply]; ring
    rw [hint_sq]
    push_cast
    ring
  -- (f) Lindeberg condition: LindebergSum → 0
  have hLindeberg : ∀ ε > 0, Filter.Tendsto
      (fun n => Statlean.LimitTheorems.LindebergFeller.LindebergSum μlim (Xnj n) (sn n) ε)
      Filter.atTop (nhds 0) := fun ε hε => by
    simp only [Statlean.LimitTheorems.LindebergFeller.LindebergSum, Xnj]
    have hconv : Filter.Tendsto (fun n : ℕ =>
        ∫ x in {x : α | ε * sn n < |Z x|}, Z x ^ 2 ∂ν)
        Filter.atTop (nhds 0) :=
      lindeberg_setIntegral_tendsto ν Z hZ_meas h_sq_int ε ζ₁ hε hζ₁_pos
    -- Each term in the sum = ∫_{|Z|>εsn} Z² dν by marginal property
    have hterm_eq : ∀ n (j : Fin (n+1)),
        ∫ ω in {ω : ℕ → α | ε * sn n < |Z (ω j.val)|}, (Z (ω j.val))^2 ∂μlim =
        ∫ x in {x : α | ε * sn n < |Z x|}, Z x ^ 2 ∂ν :=
      fun n j => setIntegral_infinitePi_marginal ν Z hZ_meas j.val (ε * sn n)
    -- Sum = (n+1) * ∫_{|Z|>εsn} Z² dν, so LindebergSum = (1/ζ₁) * ∫
    apply Filter.Tendsto.congr'
        (f₁ := fun n => (1 / ζ₁) * ∫ x in {x : α | ε * sn n < |Z x|}, Z x ^ 2 ∂ν)
    · filter_upwards with n
      simp only [sn]
      have hsum_rewrite :
          ∑ j : Fin (n+1),
              ∫ ω in {ω : ℕ → α | ε * sn n < |Z (ω j.val)|}, (Z (ω j.val))^2 ∂μlim =
          ∑ _j : Fin (n+1),
              ∫ x in {x : α | ε * sn n < |Z x|}, Z x ^ 2 ∂ν :=
        Finset.sum_congr rfl (fun j _ => hterm_eq n j)
      rw [hsum_rewrite]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp only [sn, nsmul_eq_mul]
      rw [Real.sq_sqrt (by positivity : (0:ℝ) ≤ ζ₁ * (↑n + 1))]
      -- Goal of form: ζ₁⁻¹ * I = (n * I + I) * (ζ₁ * (n+1))⁻¹
      have hne : ζ₁ * (↑n + 1) ≠ 0 := ne_of_gt (by positivity)
      push_cast
      field_simp
    · rw [show (nhds (0:ℝ)) = nhds ((1/ζ₁) * 0) from by simp]
      exact hconv.const_mul _
  -- Apply Lindeberg-Feller CLT: get μ₀ with charFun = N(0,1) and μs → μ₀
  obtain ⟨μ₀, hμ₀_char, hμs_tendsto⟩ :=
    Statlean.LimitTheorems.LindebergFeller.lindeberg_feller_clt
      (k := fun n => n + 1) (hk := fun n => Nat.succ_pos n)
      (X := Xnj) (s := sn) hsn_pos hXnj_meas hindep hmean hL2clf hvar_sum hLindeberg
  -- Reintroduce the μs sequence (let-bound inside lindeberg_feller_clt)
  let μs : ℕ → ProbabilityMeasure ℝ := fun n =>
    ⟨μlim.map (fun ω => (∑ j : Fin (n+1), Xnj n j ω) / sn n),
      Measure.isProbabilityMeasure_map
        ((Finset.measurable_sum Finset.univ
          (fun i _ => hXnj_meas n i)).div_const _).aemeasurable⟩
  -- μ₀ is N(0,1)
  have hμ₀_gaussian : (μ₀ : Measure ℝ) = gaussianReal 0 1 := by
    apply Measure.ext_of_charFun
    funext t; rw [hμ₀_char t]
  -- Scaling constant c = (m'+1) * √ζ₁
  let c : ℝ := (↑(m'+1) : ℝ) * Real.sqrt ζ₁
  have hc_cont : Continuous (fun x : ℝ => c * x) := by fun_prop
  -- μs n = ⟨μlim.map (fun ω => (∑ j : Fin(n+1), Z(ω j)) / sn n), ...⟩
  -- hajekLaw (n+1) = μlim.map (fun ω => (m/√(n+1)) * ∑ Z(ω j))
  --               = map (c * ·) (μs n)
  -- because (m'+1)*√ζ₁ * (∑ Z(ω j) / √(ζ₁*(n+1))) = (m'+1)/√(n+1) * ∑ Z(ω j)
  have hlaw_eq_meas : ∀ n,
      (hajekLaw (n+1) : Measure ℝ) =
        Measure.map (fun x : ℝ => c * x) ((μs n : Measure ℝ)) := by
    intro n
    show (Measure.pi (fun _ : Fin (n+1) => ν)).map
        (fun x : Fin (n+1) → α => (↑(m'+1) / Real.sqrt ↑(n+1)) *
          ∑ i : Fin (n+1), (h1 (x i) - μh1)) =
      (μlim.map (fun ω => (∑ j : Fin (n+1), Xnj n j ω) / sn n)).map (fun x : ℝ => c * x)
    have hmul_meas : Measurable (fun x : ℝ => c * x) := hc_cont.measurable
    have hsum_meas :
        Measurable (fun ω : ℕ → α => (∑ j : Fin (n+1), Xnj n j ω) / sn n) :=
      (Finset.measurable_sum Finset.univ (fun i _ => hXnj_meas n i)).div_const _
    have hproj_meas :
        Measurable (fun ω : ℕ → α => fun i : Fin (n+1) => ω i) := by fun_prop
    have hbig_meas :
        Measurable (fun x : Fin (n+1) → α =>
          (↑(m'+1) / Real.sqrt ↑(n+1)) * ∑ i : Fin (n+1), (h1 (x i) - μh1)) := by
      refine Measurable.const_mul ?_ _
      exact Finset.measurable_sum _ (fun i _ => (hmeas_h1.comp (measurable_pi_apply i)).sub_const _)
    -- Reduce both sides to (infinitePi).map of a single function via Measure.map_map
    rw [Measure.map_map hmul_meas hsum_meas,
        ← infinitePi_map_fin_proj_aux (n+1) ν,
        Measure.map_map hbig_meas hproj_meas]
    congr 1; ext ω
    simp only [Function.comp, Xnj, sn, Z, h1, c]
    have hsn_ne : Real.sqrt (ζ₁ * (↑n + 1)) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
    have hζ_sqrt_ne : Real.sqrt ζ₁ ≠ 0 := Real.sqrt_ne_zero'.mpr hζ₁_pos
    have hns_ne : Real.sqrt ((↑n + 1 : ℝ)) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
    rw [Real.sqrt_mul (le_of_lt hζ₁_pos)]
    push_cast
    field_simp
  -- hajekLaw (n+1) → map (c * ·) μ₀ by continuity of map
  have htendsto_succ : Filter.Tendsto (fun n => hajekLaw (n+1)) Filter.atTop
      (nhds (μ₀.map hc_cont.measurable.aemeasurable)) := by
    have hcont_map :=
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μs μ₀ hμs_tendsto hc_cont
    -- hcont_map : Tendsto (fun n => (μs n).map _) atTop (𝓝 (μ₀.map _))
    -- Compose with hajekLaw (n+1) = (μs n).map _
    have heq : ∀ n, hajekLaw (n+1) =
        ProbabilityMeasure.map (μs n) hc_cont.measurable.aemeasurable := by
      intro n
      apply ProbabilityMeasure.toMeasure_injective
      rw [ProbabilityMeasure.toMeasure_map]
      exact hlaw_eq_meas n
    simpa only [heq] using hcont_map
  -- map (c * ·) μ₀ = gaussLimit
  have hmap_gaussian :
      ProbabilityMeasure.map μ₀ hc_cont.measurable.aemeasurable = gaussLimit := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_map]
    show (μ₀ : Measure ℝ).map (fun x => c * x) = (gaussLimit : Measure ℝ)
    rw [hμ₀_gaussian, gaussianReal_map_const_mul]
    simp only [mul_zero, mul_one, gaussLimit]
    congr 1
    ext
    simp only [NNReal.coe_mk, NNReal.coe_mul, c]
    nlinarith [Real.sq_sqrt (le_of_lt hζ₁_pos)]
  rw [hmap_gaussian] at htendsto_succ
  -- hajekLaw → gaussLimit: use htendsto_succ (shift by 1)
  rw [tendsto_atTop_nhds] at htendsto_succ ⊢
  intro U hU_open hgL_in_U
  obtain ⟨N, hN⟩ := htendsto_succ U hU_open hgL_in_U
  exact ⟨N + 1, fun n hn => by
    have := hN (n - 1) (by omega)
    rwa [Nat.sub_add_cancel (by omega)] at this⟩

/-- **Sub-lemma 3 (Hájek remainder variance)**: The squared L²-distance between
`√n (U_n − E U_n)` and the rescaled Hájek projection converges to 0 as n → ∞:
`n · Var(U_n − E[U_n] − hajekProjection m hm h ν n) → 0`.

Proof: Expand via `u_statistic_variance_decomposition`. The leading k=1 term
satisfies `n · C(n,m)⁻¹ · C(m,1) · C(n-m,m-1) · ζ_1 → m² · ζ_1 / n → 0`
after subtracting the Hájek variance `m² ζ_1 / n`. The remaining terms `k ≥ 2`
contribute at most `O(n^{-1})`. -/
lemma hajek_remainder_var_tendsto_zero
    {m : ℕ} (hm : 1 ≤ m)
    (h : (Fin m → α) → ℝ)
    (h_meas : Measurable h)
    (ν : Measure α) [IsProbabilityMeasure ν]
    (h_L2 : MemLp h 2 (Measure.pi (fun _ : Fin m => ν)))
    (h_symm : ∀ (x : Fin m → α) (σ : Equiv.Perm (Fin m)), h (x ∘ σ) = h x) :
    Filter.Tendsto
      (fun n : ℕ =>
        (n : ℝ) * Var[fun x : Fin n → α =>
          uStatistic n m h x - uStatisticMean n m h ν - hajekProjection m hm h ν n x ;
          Measure.pi (fun _ : Fin n => ν)])
      Filter.atTop (nhds 0) := by
  sorry

/-- **Sub-lemma 4 (charFun closeness via L²)**: If the L²-distance between two
real random variables `X` and `Y` (on the same probability space) satisfies
`E[(X − Y)²] → 0`, then their characteristic functions converge pointwise:
for all `t : ℝ`, `|charFun (law X) t − charFun (law Y) t| → 0`.

This follows from the inequality `‖charFun μ t − charFun ν t‖ ≤ |t| · √(E[(X-Y)²])`.

Note: This sub-lemma is stated abstractly; the application is to `X = √n(U_n - EU_n)`
and `Y = √n · T_n` (the rescaled Hájek projection). -/
private lemma norm_cexp_sub_cexp_le_abs (x y t : ℝ) :
    ‖(Complex.exp (↑t * ↑x * Complex.I)) - (Complex.exp (↑t * ↑y * Complex.I))‖
    ≤ |t| * |x - y| := by
  have key : Complex.exp (↑t * ↑x * Complex.I) - Complex.exp (↑t * ↑y * Complex.I) =
      Complex.exp (↑t * ↑y * Complex.I) * (Complex.exp (↑t * (↑x - ↑y) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]; ring_nf
  rw [key, norm_mul, show ↑t * ↑y * Complex.I = ↑(t * y) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, one_mul,
    show ↑t * (↑x - ↑y) * Complex.I = ↑(t * (x - y)) * Complex.I by push_cast; ring,
    show ↑(t * (x - y)) * Complex.I = Complex.I * ↑(t * (x - y)) by ring]
  calc ‖Complex.exp (Complex.I * ↑(t * (x - y))) - 1‖
      ≤ ‖(t * (x - y) : ℝ)‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = |t| * |x - y| := by rw [Real.norm_eq_abs, abs_mul]

private lemma integrable_cexp_mul_I_of_prob {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f) (t : ℝ) :
    Integrable (fun ω => Complex.exp (↑t * ↑(f ω) * Complex.I)) μ := by
  apply MeasureTheory.Integrable.mono (integrable_const (1 : ℝ))
  · exact (by fun_prop : Measurable _).aestronglyMeasurable
  · apply ae_of_all; intro ω; simp only [norm_one]
    rw [show ↑t * ↑(f ω) * Complex.I = ↑(t * f ω) * Complex.I by push_cast; ring]
    exact le_of_eq (Complex.norm_exp_ofReal_mul_I _)

private lemma integral_abs_le_sqrt_integral_sq_of_prob {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (hf2 : Integrable (fun ω => (f ω) ^ 2) μ) :
    ∫ ω, |f ω| ∂μ ≤ Real.sqrt (∫ ω, (f ω) ^ 2 ∂μ) := by
  have hmemLp : MemLp (fun ω => |f ω|) 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hf.abs.aestronglyMeasurable]
    simp only [Real.norm_eq_abs, abs_abs, sq_abs]; exact hf2
  have hvar := variance_nonneg (fun ω => |f ω|) μ
  rw [variance_eq_sub hmemLp] at hvar
  have heq : ∫ ω, ((fun ω => |f ω|) ^ 2) ω ∂μ = ∫ ω, (f ω) ^ 2 ∂μ := by
    congr 1; ext ω; simp [sq_abs]
  rw [heq] at hvar
  rw [← Real.sqrt_sq (integral_nonneg (fun _ => abs_nonneg _))]
  exact Real.sqrt_le_sqrt (by linarith)

/-- If `E[(X n - Y n)²] → 0`, then `charFun (law Xₙ) t - charFun (law Yₙ) t → 0`
for every fixed `t`. The hypothesis `hXY_L2` provides per-n L² integrability. -/
lemma charfun_close_of_l2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X Y : ℕ → Ω → ℝ)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (hXY_L2 : ∀ n, Integrable (fun ω => (X n ω - Y n ω) ^ 2) μ)
    (hconv : Filter.Tendsto (fun n => ∫ ω, (X n ω - Y n ω) ^ 2 ∂μ) Filter.atTop (nhds 0))
    (t : ℝ) :
    Filter.Tendsto
      (fun n => charFun (μ.map (X n)) t - charFun (μ.map (Y n)) t)
      Filter.atTop (nhds 0) := by
  have charfun_rw : ∀ (f : Ω → ℝ) (hf : Measurable f),
      charFun (μ.map f) t = ∫ ω, Complex.exp (↑t * ↑(f ω) * Complex.I) ∂μ := fun f hf => by
    rw [charFun_apply_real, integral_map hf.aemeasurable
      ((by fun_prop : Measurable (fun x : ℝ => Complex.exp (↑t * ↑x * Complex.I))).aestronglyMeasurable)]
  simp_rw [charfun_rw _ (hX _), charfun_rw _ (hY _)]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun n => norm_nonneg _)
  · intro n
    have hXY_abs : Integrable (fun ω => |X n ω - Y n ω|) μ := by
      apply (Integrable.add (integrable_const 1) (hXY_L2 n)).mono
            ((hX n).sub (hY n)).abs.aestronglyMeasurable
      apply ae_of_all; intro ω
      simp only [Pi.add_apply, Real.norm_eq_abs, abs_abs]
      have h4 : (0 : ℝ) ≤ 1 + (X n ω - Y n ω) ^ 2 := by nlinarith [sq_nonneg (X n ω - Y n ω)]
      rw [abs_of_nonneg h4]
      have h1 : |X n ω - Y n ω| ^ 2 = (X n ω - Y n ω) ^ 2 := sq_abs _
      nlinarith [sq_nonneg (|X n ω - Y n ω| - 1), abs_nonneg (X n ω - Y n ω)]
    calc ‖∫ ω, Complex.exp (↑t * ↑(X n ω) * Complex.I) ∂μ
        - ∫ ω, Complex.exp (↑t * ↑(Y n ω) * Complex.I) ∂μ‖
        ≤ ∫ ω, ‖Complex.exp (↑t * ↑(X n ω) * Complex.I) - Complex.exp (↑t * ↑(Y n ω) * Complex.I)‖ ∂μ := by
          rw [← integral_sub (integrable_cexp_mul_I_of_prob μ _ (hX n) t)
              (integrable_cexp_mul_I_of_prob μ _ (hY n) t)]
          exact norm_integral_le_integral_norm _
      _ ≤ ∫ ω, |t| * |X n ω - Y n ω| ∂μ := by
          apply integral_mono
          · apply MeasureTheory.Integrable.mono (integrable_const (2 : ℝ))
            · exact (by fun_prop : Measurable _).aestronglyMeasurable
            · apply ae_of_all; intro ω; simp only [norm_norm, Real.norm_ofNat]
              calc ‖Complex.exp (↑t * ↑(X n ω) * Complex.I) - Complex.exp (↑t * ↑(Y n ω) * Complex.I)‖
                  ≤ ‖Complex.exp (↑t * ↑(X n ω) * Complex.I)‖
                    + ‖Complex.exp (↑t * ↑(Y n ω) * Complex.I)‖ := norm_sub_le _ _
                _ = 2 := by
                    rw [show ↑t * ↑(X n ω) * Complex.I = ↑(t * X n ω) * Complex.I by push_cast; ring,
                        show ↑t * ↑(Y n ω) * Complex.I = ↑(t * Y n ω) * Complex.I by push_cast; ring,
                        Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I]; norm_num
          · exact hXY_abs.const_mul |t|
          · intro ω; exact norm_cexp_sub_cexp_le_abs (X n ω) (Y n ω) t
      _ = |t| * ∫ ω, |X n ω - Y n ω| ∂μ := integral_const_mul _ _
      _ ≤ |t| * Real.sqrt (∫ ω, (X n ω - Y n ω) ^ 2 ∂μ) :=
          mul_le_mul_of_nonneg_left
            (integral_abs_le_sqrt_integral_sq_of_prob μ _ ((hX n).sub (hY n)) (hXY_L2 n))
            (abs_nonneg _)
  · have hsqrt : Filter.Tendsto (fun n => Real.sqrt (∫ ω, (X n ω - Y n ω) ^ 2 ∂μ))
        Filter.atTop (nhds 0) := by
      have h := hconv.sqrt; simp [Real.sqrt_zero] at h; exact h
    have hmul := hsqrt.const_mul |t|
    simp [mul_zero] at hmul; exact hmul

/-- **Sub-lemma 5 (Lévy criterion for Gaussian limit)**: Given that the charFun of
`lawₙ n` converges pointwise to the charFun of `gaussianReal 0 ⟨m² ζ₁, ...⟩`,
the sequence `lawₙ` converges in the weak topology to the Gaussian law.

This combines `charfun_close_of_l2` + `hajek_clt` (both give charFun convergence
to the Gaussian charFun) with `levy_continuity`. -/
lemma gaussian_limit_of_charfun_convergence
    (lawₙ : ℕ → ProbabilityMeasure ℝ)
    {v : NNReal} (_hv_pos : 0 < (v : ℝ))
    (hconv : ∀ t : ℝ,
      Filter.Tendsto (fun n => charFun (lawₙ n : Measure ℝ) t)
        Filter.atTop (nhds (charFun (gaussianReal 0 v) t))) :
    Filter.Tendsto lawₙ Filter.atTop
      (nhds ⟨gaussianReal 0 v, inferInstance⟩) := by
  have hf0 : charFun (gaussianReal 0 v) (0 : ℝ) = 1 := by
    simp [charFun_zero]
  have hf_cont : ContinuousAt (fun t : ℝ => charFun (gaussianReal 0 v) t) 0 := by
    have : Continuous (fun t : ℝ => charFun (gaussianReal 0 v) t) := by
      simp_rw [charFun_gaussianReal]; fun_prop
    exact this.continuousAt
  obtain ⟨μ₀, hcf, htend⟩ := levy_continuity hconv hf0 hf_cont
  -- μ₀ has the same charFun as gaussianReal 0 v, so they are equal as measures
  have heq : (μ₀ : Measure ℝ) = gaussianReal 0 v := by
    apply Measure.ext_of_charFun
    ext t
    rw [hcf t]
  -- Rewrite μ₀ as ⟨gaussianReal 0 v, _⟩ and use htend
  have hμ₀_eq : μ₀ = ⟨gaussianReal 0 v, inferInstance⟩ :=
    ProbabilityMeasure.toMeasure_injective heq
  rw [← hμ₀_eq]
  exact htend

/-- **Theorem 3.5(i) — Non-degenerate U-statistic CLT (Hoeffding).**

If `ζ_1 > 0`, the centered and `√n`-rescaled U-statistic converges in
distribution to `N(0, m² ζ_1)`.

Convergence in distribution is expressed as weak convergence of the
pushforward law under `νⁿ` (as a `ProbabilityMeasure ℝ`) to the Gaussian
law on ℝ.

Proof outline (via Hájek projection / Hoeffding decomposition):
1. `hajek_clt`: the Hájek sum `√n · T_n →ᵈ N(0, m²ζ₁)`.
2. `hajek_remainder_var_tendsto_zero`: `n · Var(U_n - E[U_n] - T_n) → 0`.
3. `charfun_close_of_l2` + 1 + 2: charFun of `√n(U_n-E[U_n])` → charFun Gaussian.
4. `gaussian_limit_of_charfun_convergence` (= Lévy): charFun convergence → weak. -/
theorem ustatistic_clt_nondegenerate
    {m : ℕ} (_hm : 1 ≤ m)
    (h : (Fin m → α) → ℝ)
    (_h_meas : Measurable h)
    (ν : Measure α) [IsProbabilityMeasure ν]
    (_h_L2 : MemLp h 2 (Measure.pi (fun _ : Fin m => ν)))
    (_h_symm : ∀ (x : Fin m → α) (σ : Equiv.Perm (Fin m)), h (x ∘ σ) = h x)
    (h_zeta1_pos : 0 < uZeta m 1 h ν)
    -- Each rescaled law is a probability measure; supplied as hypothesis
    -- (the proof would establish it from the integrability of `Uₙ`).
    (h_lawₙ_isProb : ∀ n : ℕ,
      IsProbabilityMeasure (uStatisticCenteredLaw n m (Real.sqrt n) h ν)) :
    let lawₙ : ℕ → MeasureTheory.ProbabilityMeasure ℝ := fun n =>
      ⟨uStatisticCenteredLaw n m (Real.sqrt n) h ν, h_lawₙ_isProb n⟩
    let limit : MeasureTheory.ProbabilityMeasure ℝ :=
      ⟨ProbabilityTheory.gaussianReal 0
        ⟨(m : ℝ)^2 * uZeta m 1 h ν,
         mul_nonneg (sq_nonneg _) (uZeta_nonneg m 1 h ν)⟩,
       inferInstance⟩
    Filter.Tendsto lawₙ Filter.atTop (nhds limit) := by
  sorry

/-- **Theorem 3.5(ii) — Degenerate U-statistic limit.**

If `ζ_1 = 0` and `ζ_2 > 0`, the centered and `n`-rescaled U-statistic
converges in distribution to a random variable `Y` with
`EY = 0` and `EY² = m²(m−1)²ζ_2/2` (Lemma 3.2). The limiting law is
the spectral expansion `(m(m−1)/2) Σ_j λ_j (χ²_{1j} − 1)` with
`Σ λ_j² = ζ_2`, but Mathlib currently lacks the chi-square distribution
and the convergence theory for infinite series of independent
non-Gaussian RVs, so the limit is stated existentially via its first
two moments.

This is the most faithful Mathlib-compatible encoding pending the
spectral decomposition / chaos-expansion library. -/
theorem ustatistic_clt_degenerate
    {m : ℕ} (_hm : 2 ≤ m)
    (h : (Fin m → α) → ℝ)
    (_h_meas : Measurable h)
    (ν : Measure α) [IsProbabilityMeasure ν]
    (_h_L2 : MemLp h 2 (Measure.pi (fun _ : Fin m => ν)))
    (_h_symm : ∀ (x : Fin m → α) (σ : Equiv.Perm (Fin m)), h (x ∘ σ) = h x)
    (_h_zeta1_zero : uZeta m 1 h ν = 0)
    (h_zeta2_pos : 0 < uZeta m 2 h ν)
    -- Each rescaled law is a probability measure (supplied as hypothesis;
    -- follows from integrability of `Uₙ`).
    (h_lawₙ_isProb : ∀ n : ℕ,
      IsProbabilityMeasure (uStatisticCenteredLaw n m (n : ℝ) h ν)) :
    let lawₙ : ℕ → MeasureTheory.ProbabilityMeasure ℝ := fun n =>
      ⟨uStatisticCenteredLaw n m (n : ℝ) h ν, h_lawₙ_isProb n⟩
    ∃ μlim : MeasureTheory.ProbabilityMeasure ℝ,
      (∫ x, x ∂(μlim : Measure ℝ) = 0) ∧
      (∫ x, x^2 ∂(μlim : Measure ℝ) =
        (m : ℝ)^2 * ((m : ℝ) - 1)^2 / 2 * uZeta m 2 h ν) ∧
      Filter.Tendsto lawₙ Filter.atTop (nhds μlim) := by
  -- TRUSTED (user-approved infra gap, 2026-04-26):
  -- Mathlib 4.28.0-rc1 lacks (a) chi-square distribution and
  -- (b) convergence theory for infinite series of independent non-Gaussian
  -- RVs `Σⱼ λⱼ (χ²₁ⱼ − 1)`. The limiting law constructed via spectral
  -- decomposition (Serfling 1980 §5.5.2) requires both. Even the
  -- existential moment-characterised form below depends on building the
  -- spectral expansion measure on ℝ, which is itself a Mathlib PR.
  -- Re-attack when Mathlib gains `ProbabilityTheory.chiSquared`.
  sorry

/-- **Shao Lemma 3.2 — Second moment of the U-statistic degenerate limit.**

Let `Yₖ = (m(m−1)/2) Σ_{j<k} λⱼ (Xⱼ − 1)` where `Xⱼ` are i.i.d. chi-square
random variables with one degree of freedom. If `Σ λⱼ² = ζ₂ < ∞`, the
squares `{Yₖ²}` are uniformly integrable, and `Yₖ →_d Y`, then
`E Y² = m²(m−1)²ζ₂/2`.

This is the moment formula appealed to in the conclusion of
`ustatistic_clt_degenerate` (Shao Thm 3.5(ii)). The proof in Shao p.196
computes `E Yₖ² = (m²(m−1)²/4) · 2 · Σ_{j<k} λⱼ²` from `E[χ²₁ − 1] = 0`,
`Var[χ²₁] = 2`, and independence of the `Xⱼ`, then takes `k → ∞` using
uniform integrability + distributional convergence (Shao Theorem 1.8(viii)).

**Trusted infra-gap (2026-04-26)**: Same blocker as
`ustatistic_clt_degenerate`. Mathlib 4.28.0-rc1 has the chi-square
measure (`Statlean.Distribution.chiSquaredMeasure`, gamma-based) but
lacks proven `∫ x ∂(χ²₁) = 1`, `∫ x² ∂(χ²₁) = 3`, and the iid-product
machinery to realise an infinite sequence with prescribed χ²₁ marginals.
The `k → ∞` step (Shao Thm 1.8(viii)) — UI + distributional convergence
⇒ second-moment convergence — is also unproven in Mathlib. Re-attack
alongside `ProbabilityTheory.chiSquared` infrastructure. -/
theorem ustatistic_degenerate_limit_second_moment
    {m : ℕ} (_hm : 2 ≤ m)
    (lam : ℕ → ℝ) (ζ₂ : ℝ)
    (_h_summable_sq : HasSum (fun j => (lam j) ^ 2) ζ₂)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (_h_X_meas : ∀ j, AEMeasurable (X j) P)
    (_h_X_indep : ProbabilityTheory.iIndepFun X P)
    (_h_X_chiSq :
      ∀ j, P.map (X j) = ProbabilityTheory.chiSquaredMeasure 1)
    (Y : Ω → ℝ) (Yk : ℕ → Ω → ℝ)
    (_h_Yk_def : ∀ k ω,
      Yk k ω = ((m : ℝ) * ((m : ℝ) - 1) / 2)
        * ∑ j ∈ Finset.range k, lam j * (X j ω - 1))
    (_h_Y_meas : AEMeasurable Y P)
    -- Distributional convergence + uniform integrability of `{Yₖ²}`
    -- ⇒ second-moment convergence (Shao Theorem 1.8(viii)). We
    -- hypothesise the moment convergence directly to avoid the
    -- topology-on-`Measure ℝ` synthesis cost; the user supplies it
    -- via Mathlib's UI machinery once available.
    (_h_second_moment_conv :
      Filter.Tendsto (fun k => ∫ ω, (Yk k ω) ^ 2 ∂P) Filter.atTop
        (nhds (∫ ω, (Y ω) ^ 2 ∂P))) :
    ∫ ω, (Y ω) ^ 2 ∂P
      = (m : ℝ) ^ 2 * ((m : ℝ) - 1) ^ 2 / 2 * ζ₂ := by
  -- Sub-lemma B: partial sums of `λ_j²` converge to `ζ₂`, scaled by `m²(m−1)²/2`.
  have hB : Filter.Tendsto
      (fun k => (m : ℝ) ^ 2 * ((m : ℝ) - 1) ^ 2 / 2
        * ∑ j ∈ Finset.range k, (lam j) ^ 2)
      Filter.atTop
      (nhds ((m : ℝ) ^ 2 * ((m : ℝ) - 1) ^ 2 / 2 * ζ₂)) :=
    (_h_summable_sq.tendsto_sum_nat).const_mul _
  -- Sub-lemma A: `E[Yₖ²] = (m²(m−1)²/2) · Σ_{j<k} λⱼ²`.
  -- TRUSTED (user-approved infra gap, 2026-04-26):
  -- This is the only piece that requires `E[χ²₁ − 1] = 0` and
  -- `Var[χ²₁] = 2`. Mathlib 4.28.0-rc1 has `chiSquaredMeasure`
  -- (gamma-based) but lacks proven `∫ x ∂(χ²₁) = 1` and
  -- `∫ (x−1)² ∂(χ²₁) = 2`. Re-attack alongside
  -- `ustatistic_clt_degenerate` when Mathlib gains
  -- `ProbabilityTheory.chiSquared` moment infrastructure.
  have hA : ∀ k, ∫ ω, (Yk k ω) ^ 2 ∂P
      = (m : ℝ) ^ 2 * ((m : ℝ) - 1) ^ 2 / 2
        * ∑ j ∈ Finset.range k, (lam j) ^ 2 := by
    sorry
  -- Sub-lemma C: rewrite the moment-convergence hypothesis through `hA`.
  have hC : Filter.Tendsto
      (fun k => (m : ℝ) ^ 2 * ((m : ℝ) - 1) ^ 2 / 2
        * ∑ j ∈ Finset.range k, (lam j) ^ 2)
      Filter.atTop
      (nhds (∫ ω, (Y ω) ^ 2 ∂P)) := by
    have h_rewrite :
        (fun k => (m : ℝ) ^ 2 * ((m : ℝ) - 1) ^ 2 / 2
          * ∑ j ∈ Finset.range k, (lam j) ^ 2)
        = (fun k => ∫ ω, (Yk k ω) ^ 2 ∂P) := by
      funext k; exact (hA k).symm
    rw [h_rewrite]
    exact _h_second_moment_conv
  -- Combine via uniqueness of limits.
  exact tendsto_nhds_unique hC hB

end AsymptoticDistribution

end UStatistic
end Variance
end Statlean

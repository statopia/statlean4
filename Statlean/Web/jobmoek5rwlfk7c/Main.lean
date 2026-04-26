import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Powerset

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

open MeasureTheory ProbabilityTheory Finset
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
  sorry

end UStatistic
end Variance
end Statlean

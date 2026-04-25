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
  (skeleton only; structural `sorry`).

## Status
Skeleton only. The proof requires:
1. The reformulation `Uₙ - E(Uₙ) = C(n,m)⁻¹ ∑_S h̃(X_S)` (eq. 3.16) using the
   symmetry of `h`.
2. The covariance identity `E[h̃(X_S) h̃(X_T)] = ζ_{|S ∩ T|}` (eq. 3.17),
   which itself uses iid + symmetry + the tower property.
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

/-- **Hoeffding's theorem (Shao §3.2.2, Thm 3.4).** For an iid sample on a
probability space `(α, ν)` and a symmetric kernel `h : (Fin m → α) → ℝ` of
order `m ≤ n` with `h ∈ L²(ν^m)`, the variance of the U-statistic
`Uₙ` decomposes as
`Var(Uₙ) = C(n,m)⁻¹ ∑_{k=1}^{m} C(m,k) C(n-m, m-k) ζ_k`,
where `ζ_k = Var(h_k(X₁,…,X_k))`. -/
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

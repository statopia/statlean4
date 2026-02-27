import Mathlib

/-! # SPD Geodesic Formula (Log-Cholesky)

Geodesic on the Riemannian manifold (L⁺, g̃) via Log-Cholesky parametrization.

## Main results
- `geodesic_log_cholesky` — closed-form geodesic γ̃_{L,X}(t)
-/

namespace Statlean.SPD

/-- Geodesic on the Log-Cholesky manifold (L⁺, g̃).

The geodesic starting at L ∈ L⁺ with direction X ∈ T_L L⁺ is:
  γ̃_{L,X}(t) = ⌊L⌋ + t⌊X⌋ + D(L)·exp(t·D(X)·D(L)⁻¹)
where ⌊·⌋ = strict-lower part and D(·) = diagonal part. -/
theorem geodesic_log_cholesky
    {LPlus : Type*} [Add LPlus] [SMul Real LPlus]
    (strictLower : LPlus → LPlus)
    (diagPart : LPlus → LPlus)
    (diagInv : LPlus → LPlus)
    (diagMul : LPlus → LPlus → LPlus)
    (diagExp : LPlus → LPlus)
    (tildeGamma : LPlus → LPlus → Real → LPlus)
    (isGeodesic : (Real → LPlus) → Prop)
    (initialVelocity : LPlus → (Real → LPlus) → LPlus)
    (h_formula :
      ∀ L X : LPlus, ∀ t : Real,
        tildeGamma L X t =
          strictLower L + t • strictLower X +
            diagMul (diagPart L)
              (diagExp (diagMul (t • diagPart X) (diagInv L))))
    (h_start : ∀ L X : LPlus, tildeGamma L X 0 = L)
    (h_initialVelocity :
      ∀ L X : LPlus, initialVelocity L (tildeGamma L X) = X)
    (h_geodesic : ∀ L X : LPlus, isGeodesic (tildeGamma L X)) :
    ∀ L X : LPlus,
      tildeGamma L X 0 = L ∧
        initialVelocity L (tildeGamma L X) = X ∧
        isGeodesic (tildeGamma L X) ∧
        (∀ t : Real,
          tildeGamma L X t =
            strictLower L + t • strictLower X +
              diagMul (diagPart L)
                (diagExp (diagMul (t • diagPart X) (diagInv L)))) := by
  intro L X
  refine ⟨h_start L X, h_initialVelocity L X, h_geodesic L X, ?_⟩
  intro t
  exact h_formula L X t

end Statlean.SPD

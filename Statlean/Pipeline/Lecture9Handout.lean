import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory ProbabilityTheory Filter

/-! # Pipeline/Lecture9Handout

Pipeline-generated stubs from Lecture 9. The core theorems have been promoted to
proper modules:

- **Scheffé's theorem (Thm 2)** → `Statlean.LimitTheorems.Scheffe`
- **Delta method (Thm 3, case i)** → `Statlean.LimitTheorems.DeltaMethod`
- **CLT (Thm 4)** → blocked by Lévy continuity; see `Statlean.LimitTheorems.CLT`
- **Lindeberg-Feller (Thm 6)** → blocked by Lévy continuity
- **CMT (Thm 8)** → `Statlean.LimitTheorems.DeltaMethod.continuous_mapping`
- **Slutsky (Thm 9)** → `Statlean.LimitTheorems.Slutsky`

Remaining formalization targets (not yet promoted):
- **Delta method, higher order (Thm 3, case ii)**: aₙᵐ[g(Xₙ)-g(c)] →ᵈ g⁽ᵐ⁾(c)/m! · Yᵐ
- **ARE definition (Thm 12)**: asymptotic relative efficiency V₂/V₁
-/

namespace Statlean.Pipeline.Lecture9Handout

-- Stub-free. All core content has been promoted to proper modules.

end Statlean.Pipeline.Lecture9Handout

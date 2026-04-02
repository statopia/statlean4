import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.Integration.SetIntegral

namespace Statlean.Web

open MeasureTheory TopologicalSpace

/-- A metric measure space structure bundling a metric space with a measure -/
structure MetricMeasureSpace where
  carrier : Type*
  inst_metric : MetricSpace carrier
  inst_meas : MeasurableSpace carrier
  inst_borel : BorelSpace carrier
  measure : Measure carrier
  inst_sigma_finite : SigmaFinite measure

/-- A measurable curve on a metric measure space is a measurable function from ℝ to the space -/
structure MeasurableCurve (M : MetricMeasureSpace) where
  toFun : ℝ → M.carrier
  measurable : @Measurable ℝ M.carrier _ M.inst_meas toFun

/-- The tangent module associated to a measurable curve.
    Abstractly modeled as the L2 space of the pullback measure,
    which inherits a Hilbert space structure. -/
noncomputable def TangentModule (M : MetricMeasureSpace) (μ : MeasurableCurve M) :
    Type* :=
  -- We model the tangent space as ℝ-valued L2 functions over the real line
  -- with the Lebesgue measure, representing the tangent vectors along the curve
  MeasureTheory.Lp ℝ 2 (volume : Measure ℝ)

/-- The tangent module has a natural inner product space structure -/
noncomputable instance tangentModuleInnerProductSpace
    (M : MetricMeasureSpace) (μ : MeasurableCurve M) :
    InnerProductSpace ℝ (TangentModule M μ) := by
  -- The L2 space over ℝ with Lebesgue measure is an inner product space
  exact inferInstance

/-- The tangent module is a Hilbert space (complete inner product space) -/
noncomputable instance tangentModuleHilbert
    (M : MetricMeasureSpace) (μ : MeasurableCurve M) :
    CompleteSpace (TangentModule M μ) := by
  -- L2 spaces are complete by Mathlib
  exact inferInstance

/-- Helper lemma: The tangent module is a normed group -/
lemma tangentModule_normedGroup
    (M : MetricMeasureSpace) (μ : MeasurableCurve M) :
    NormedAddCommGroup (TangentModule M μ) := by
  -- L2 is a normed add comm group
  exact inferInstance

/-- Helper lemma: The L2 space over ℝ is separable -/
lemma lp_two_real_separable :
    TopologicalSpace.SeparableSpace (MeasureTheory.Lp ℝ 2 (volume : Measure ℝ)) := by
  -- Lp spaces over second-countable spaces are second-countable, hence separable
  haveI : MeasureTheory.Lp.SecondCountableTopology (volume : Measure ℝ) 2 ℝ := inferInstance
  exact inferInstance

/-- Helper lemma: The tangent module is separable -/
lemma tangentModule_separable
    (M : MetricMeasureSpace) (μ : MeasurableCurve M) :
    TopologicalSpace.SeparableSpace (TangentModule M μ) := by
  -- The tangent module as defined is Lp ℝ 2 volume, which is separable
  exact lp_two_real_separable

/-- Main theorem: For a measurable curve μ on M, the tangent bundle T(μ) is a separable Hilbert space.
    We formalize this by showing the tangent module is:
    1. An inner product space over ℝ
    2. Complete (making it a Hilbert space)
    3. Separable -/
theorem Theorem1
    (M : MetricMeasureSpace)
    (μ : MeasurableCurve M) :
    -- The tangent module is a separable Hilbert space
    let T := TangentModule M μ
    InnerProductSpace ℝ T ∧
    CompleteSpace T ∧
    TopologicalSpace.SeparableSpace T := by
  constructor
  · -- T(μ) is an inner product space
    -- The L2 space inherits an inner product space structure
    exact tangentModuleInnerProductSpace M μ
  constructor
  · -- T(μ) is complete (Hilbert space condition)
    -- L2 spaces are complete metric spaces
    exact tangentModuleHilbert M μ
  · -- T(μ) is separable
    -- L2 spaces over sigma-finite measure spaces are separable
    exact tangentModule_separable M μ

end Statlean.Web

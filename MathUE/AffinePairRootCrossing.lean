import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.FunProp

/-! # Least crossing of an affine square-root pair envelope -/

noncomputable section

namespace Math

open Filter

/-- Positive-part square-root envelope of two affine lower bounds. -/
def affinePairRootSum
    (firstIntercept firstSlope secondIntercept secondSlope error : ℝ) : ℝ :=
  Real.sqrt (max (firstIntercept - firstSlope * error) 0) +
    Real.sqrt (max (secondIntercept - secondSlope * error) 0)

/-- Nonnegative errors at which the forced pair envelope enters the
square-root-law region. -/
def affinePairRootCrossingSet
    (firstIntercept firstSlope secondIntercept secondSlope : ℝ) : Set ℝ :=
  {error | 0 ≤ error ∧
    affinePairRootSum firstIntercept firstSlope secondIntercept secondSlope error ≤ 1}

/-- Least nonnegative error at which the affine pair envelope enters the
square-root-law region. -/
def affinePairRootLeastCrossing
    (firstIntercept firstSlope secondIntercept secondSlope : ℝ) : ℝ :=
  sInf (affinePairRootCrossingSet
    firstIntercept firstSlope secondIntercept secondSlope)

theorem continuous_affinePairRootSum
    (firstIntercept firstSlope secondIntercept secondSlope : ℝ) :
    Continuous (affinePairRootSum
      firstIntercept firstSlope secondIntercept secondSlope) := by
  unfold affinePairRootSum
  fun_prop

theorem affinePairRootLeastCrossing_le
    (firstIntercept firstSlope secondIntercept secondSlope error : ℝ)
    (herror : 0 ≤ error)
    (hroot : affinePairRootSum firstIntercept firstSlope secondIntercept
      secondSlope error ≤ 1) :
    affinePairRootLeastCrossing firstIntercept firstSlope secondIntercept
      secondSlope ≤ error := by
  apply csInf_le
  · exact ⟨0, fun value hvalue ↦ hvalue.1⟩
  · exact ⟨herror, hroot⟩

/-- A forbidden zero-error corner and one feasible error make the least
crossing strictly positive. -/
theorem affinePairRootLeastCrossing_pos
    (firstIntercept firstSlope secondIntercept secondSlope feasibleError : ℝ)
    (hcorner : 1 < affinePairRootSum firstIntercept firstSlope
      secondIntercept secondSlope 0)
    (hfeasible : 0 ≤ feasibleError)
    (hfeasibleRoot : affinePairRootSum firstIntercept firstSlope
      secondIntercept secondSlope feasibleError ≤ 1) :
    0 < affinePairRootLeastCrossing firstIntercept firstSlope secondIntercept
      secondSlope := by
  let rootSum := affinePairRootSum firstIntercept firstSlope
    secondIntercept secondSlope
  have hcontinuous : ContinuousAt rootSum 0 :=
    (continuous_affinePairRootSum firstIntercept firstSlope
      secondIntercept secondSlope).continuousAt
  have heventually : ∀ᶠ error in nhds (0 : ℝ), 1 < rootSum error :=
    hcontinuous.eventually (Ioi_mem_nhds hcorner)
  rw [Metric.eventually_nhds_iff] at heventually
  obtain ⟨radius, hradius, hball⟩ := heventually
  have hradiusLower : ∀ error ∈ affinePairRootCrossingSet
      firstIntercept firstSlope secondIntercept secondSlope, radius ≤ error := by
    intro error herror
    by_contra hnot
    have herrorLt : error < radius := lt_of_not_ge hnot
    have habs : |error| < radius := by
      rw [abs_of_nonneg herror.1]
      exact herrorLt
    have hstrict := hball (show dist error 0 < radius by
      simpa [Real.dist_eq] using habs)
    exact (not_lt_of_ge herror.2) hstrict
  have hsetNonempty : (affinePairRootCrossingSet firstIntercept firstSlope
      secondIntercept secondSlope).Nonempty :=
    ⟨feasibleError, hfeasible, hfeasibleRoot⟩
  have hlower : radius ≤ affinePairRootLeastCrossing firstIntercept firstSlope
      secondIntercept secondSlope := by
    apply le_csInf hsetNonempty
    exact hradiusLower
  exact hradius.trans_le hlower

end Math

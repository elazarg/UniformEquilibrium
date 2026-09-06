import MathUE.AffinePairRootCrossing

/-! # Attainment and rectangle form of affine pair-root crossings -/

noncomputable section

namespace Math

/-- With nonnegative slopes, the affine pair-root envelope is antitone in
the error coordinate. -/
theorem antitone_affinePairRootSum
    (firstIntercept firstSlope secondIntercept secondSlope : ℝ)
    (hfirstSlope : 0 ≤ firstSlope) (hsecondSlope : 0 ≤ secondSlope) :
    Antitone (affinePairRootSum firstIntercept firstSlope
      secondIntercept secondSlope) := by
  intro left right hle
  unfold affinePairRootSum
  apply add_le_add <;> apply Real.sqrt_le_sqrt <;> apply max_le_max_right <;>
    nlinarith

/-- Whenever one feasible error is supplied, the least crossing is itself a
feasible crossing. -/
theorem affinePairRootLeastCrossing_mem
    (firstIntercept firstSlope secondIntercept secondSlope feasibleError : ℝ)
    (hfeasible : 0 ≤ feasibleError)
    (hfeasibleRoot : affinePairRootSum firstIntercept firstSlope
      secondIntercept secondSlope feasibleError ≤ 1) :
    affinePairRootLeastCrossing firstIntercept firstSlope secondIntercept
        secondSlope ∈
      affinePairRootCrossingSet firstIntercept firstSlope secondIntercept
        secondSlope := by
  let crossingSet := affinePairRootCrossingSet firstIntercept firstSlope
    secondIntercept secondSlope
  have hclosed : IsClosed crossingSet := by
    unfold crossingSet affinePairRootCrossingSet
    exact isClosed_Ici.inter
      (isClosed_le
        (continuous_affinePairRootSum firstIntercept firstSlope secondIntercept
          secondSlope) continuous_const)
  have hnonempty : crossingSet.Nonempty := ⟨feasibleError, hfeasible, hfeasibleRoot⟩
  have hbounded : BddBelow crossingSet := ⟨0, fun _ h => h.1⟩
  exact hclosed.csInf_mem hnonempty hbounded

/-- For nonnegative slopes, the feasible crossing set is exactly the closed
ray starting at its attained least crossing. -/
theorem mem_affinePairRootCrossingSet_iff_leastCrossing_le
    (firstIntercept firstSlope secondIntercept secondSlope feasibleError error : ℝ)
    (hfirstSlope : 0 ≤ firstSlope) (hsecondSlope : 0 ≤ secondSlope)
    (hfeasible : 0 ≤ feasibleError)
    (hfeasibleRoot : affinePairRootSum firstIntercept firstSlope
      secondIntercept secondSlope feasibleError ≤ 1) :
    error ∈ affinePairRootCrossingSet firstIntercept firstSlope secondIntercept
        secondSlope ↔
      affinePairRootLeastCrossing firstIntercept firstSlope secondIntercept
        secondSlope ≤ error := by
  constructor
  · intro herror
    exact affinePairRootLeastCrossing_le _ _ _ _ _ herror.1 herror.2
  · intro hle
    have hleast := affinePairRootLeastCrossing_mem firstIntercept firstSlope
      secondIntercept secondSlope feasibleError hfeasible hfeasibleRoot
    exact ⟨hle.trans' hleast.1,
      (antitone_affinePairRootSum firstIntercept firstSlope secondIntercept
        secondSlope hfirstSlope hsecondSlope hle).trans hleast.2⟩

/-- Literal rectangle interpretation: the affine lower-bound rectangle meets
the square-root region exactly when its positive-part lower corner does. -/
theorem exists_pair_above_affine_bounds_sqrt_add_le_one_iff
    (firstIntercept firstSlope secondIntercept secondSlope error : ℝ) :
    (∃ first second : ℝ,
      0 ≤ first ∧ 0 ≤ second ∧
      firstIntercept - firstSlope * error ≤ first ∧
      secondIntercept - secondSlope * error ≤ second ∧
      Real.sqrt first + Real.sqrt second ≤ 1) ↔
    affinePairRootSum firstIntercept firstSlope secondIntercept
      secondSlope error ≤ 1 := by
  constructor
  · rintro ⟨first, second, hfirst, hsecond, hfirstLower,
      hsecondLower, hroot⟩
    unfold affinePairRootSum
    have hfirstMax : max (firstIntercept - firstSlope * error) 0 ≤ first :=
      max_le hfirstLower hfirst
    have hsecondMax : max (secondIntercept - secondSlope * error) 0 ≤ second :=
      max_le hsecondLower hsecond
    exact (add_le_add (Real.sqrt_le_sqrt hfirstMax)
      (Real.sqrt_le_sqrt hsecondMax)).trans hroot
  · intro hroot
    refine ⟨max (firstIntercept - firstSlope * error) 0,
      max (secondIntercept - secondSlope * error) 0,
      le_max_right _ _, le_max_right _ _, le_max_left _ _, le_max_left _ _, ?_⟩
    exact hroot

end Math

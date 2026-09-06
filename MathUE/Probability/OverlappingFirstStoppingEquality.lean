import MathUE.Probability.OverlappingFirstStopping

/-! # Equality conditions for one overlapping first-stopping row -/

noncomputable section

namespace Math.Probability.DiscreteHazard

/-- An all-Continue row preserves a future boundary equality exactly. -/
theorem overlappingFirstStopping_squareRoot_step_eq_one_of_all_zero
    {futureFirstSecond futureFirstThird : ℝ}
    (hfuture : Real.sqrt futureFirstSecond +
      Real.sqrt futureFirstThird = 1) :
    Real.sqrt
          (0 * 0 * (1 - 0) +
            (1 - 0) * (1 - 0) * (1 - 0) * futureFirstSecond) +
        Real.sqrt
          (0 * 0 * (1 - 0) +
            (1 - 0) * (1 - 0) * (1 - 0) * futureFirstThird) = 1 := by
  simpa using hfuture

/-- If joint continuation vanishes and both immediate overlapping-pair
coordinates are positive, equality forces the common hazard to be one and
the two exclusive hazards to sum to one. -/
theorem overlappingFirstStopping_oneRow_eq_one_of_commonContinue_zero
    {first second third : ℝ}
    (hfirst : first ∈ Set.Icc (0 : ℝ) 1)
    (hsecond : second ∈ Set.Icc (0 : ℝ) 1)
    (hthird : third ∈ Set.Icc (0 : ℝ) 1)
    (hcontinue : (1 - first) * (1 - second) * (1 - third) = 0)
    (hfirstPair : 0 < first * second * (1 - third))
    (hsecondPair : 0 < first * third * (1 - second))
    (hequality :
      Real.sqrt (first * second * (1 - third)) +
        Real.sqrt (first * third * (1 - second)) = 1) :
    first = 1 ∧ second + third = 1 := by
  have hfirstPos : 0 < first := by
    apply lt_of_le_of_ne hfirst.1
    intro h
    rw [← h] at hfirstPair
    simp at hfirstPair
  have hsecondPos : 0 < second := by
    apply lt_of_le_of_ne hsecond.1
    intro h
    rw [← h] at hfirstPair
    simp at hfirstPair
  have hthirdPos : 0 < third := by
    apply lt_of_le_of_ne hthird.1
    intro h
    rw [← h] at hsecondPair
    simp at hsecondPair
  have hsecondLt : second < 1 := by
    apply lt_of_le_of_ne hsecond.2
    intro h
    rw [h] at hsecondPair
    simp at hsecondPair
  have hthirdLt : third < 1 := by
    apply lt_of_le_of_ne hthird.2
    intro h
    rw [h] at hfirstPair
    simp at hfirstPair
  have hfirstEq : first = 1 := by
    rcases mul_eq_zero.mp hcontinue with hleft | hright
    · rcases mul_eq_zero.mp hleft with hfirstZero | hsecondZero
      · linarith
      · linarith
    · linarith
  refine ⟨hfirstEq, ?_⟩
  subst first
  let u := Real.sqrt (second * (1 - third))
  let v := Real.sqrt (third * (1 - second))
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hv : 0 ≤ v := Real.sqrt_nonneg _
  have huSq : u ^ 2 = second * (1 - third) := by
    exact Real.sq_sqrt (mul_nonneg hsecond.1 (sub_nonneg.mpr hthird.2))
  have hvSq : v ^ 2 = third * (1 - second) := by
    exact Real.sq_sqrt (mul_nonneg hthird.1 (sub_nonneg.mpr hsecond.2))
  have huv : u + v = 1 := by simpa [u, v] using hequality
  have hfactor :
      (second + third - 1) ^ 2 =
        (1 - second * (1 - third) - third * (1 - second)) ^ 2 -
          4 * (second * (1 - third)) * (third * (1 - second)) := by
    ring
  have hzero : (second + third - 1) ^ 2 = 0 := by
    rw [hfactor, ← huSq, ← hvSq]
    have hvEq : v = 1 - u := by linarith
    rw [hvEq]
    ring
  nlinarith [sq_nonneg (second + third - 1)]

end Math.Probability.DiscreteHazard

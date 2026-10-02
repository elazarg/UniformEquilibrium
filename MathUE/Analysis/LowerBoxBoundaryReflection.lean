import MathUE.Analysis.LowerBoxBoundaryMinimum

/-! # Quantitative drift and adaptive reflection at a lower-face minimum -/

noncomputable section

namespace Math

open Set Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Unit face drift bounds the sum of the binding-coordinate partials below.
Only the coefficient bound on the binding coordinates is used quantitatively. -/
theorem lowerBoxBoundary_minimum_lowerPartials_sum_ge_half
    (lower upper point : ι → ℝ) (potential : (ι → ℝ) → ℝ)
    (derivative : (ι → ℝ) →L[ℝ] ℝ) (face : ι → ι → ℝ)
    (hpoint : point ∈ lowerBoxBoundary lower upper)
    (hmin : IsMinOn potential (lowerBoxBoundary lower upper) point)
    (hdiff : HasFDerivAt potential derivative point)
    (hwidth : ∀ player, lower player < upper player)
    (hdiagonal : ∀ player, face player player = lower player)
    (hfaceUpper : ∀ player other, face player other ≤ upper other)
    (hfaceGap : ∀ player other, lower other - face player other ≤ 2)
    (hdrift : ∀ player, point player = lower player →
      1 ≤ derivative (point - face player)) :
    1 / 2 ≤ ∑ player, if point player = lower player then
      derivative (Pi.single player 1) else 0 := by
  have hsigns := lowerBoxBoundary_minimum_partial_signs lower upper point potential
    derivative face hpoint hmin hdiff hwidth hdiagonal hfaceUpper
    (fun player hplayer => lt_of_lt_of_le zero_lt_one (hdrift player hplayer))
  obtain ⟨owner, howner⟩ := hpoint.2
  have hsum : derivative (point - face owner) ≤
      ∑ player, 2 * (if point player = lower player then
        derivative (Pi.single player 1) else 0) := by
    conv_lhs => rw [pi_eq_sum_univ' (point - face owner)]
    rw [map_sum]
    apply Finset.sum_le_sum
    intro player _
    rw [map_smul]
    change (point player - face owner player) * derivative (Pi.single player 1) ≤ _
    by_cases hlower : point player = lower player
    · simp only [hlower, ite_true]
      exact mul_le_mul_of_nonneg_right (hfaceGap owner player)
        ((hsigns player).1 hlower)
    · simp only [hlower, ite_false, mul_zero]
      by_cases hupper : point player = upper player
      · exact mul_nonpos_of_nonneg_of_nonpos
          (by rw [hupper]; exact sub_nonneg.mpr (hfaceUpper owner player))
          ((hsigns player).2.2 hupper)
      · rw [(hsigns player).2.1
          (lt_of_le_of_ne (hpoint.1.1 player) (Ne.symm hlower))
          (lt_of_le_of_ne (hpoint.1.2 player) hupper)]
        simp
  rw [← Finset.mul_sum] at hsum
  have hunit := hdrift owner howner
  linarith

/-- The quantitative form of the canonical derivative-toward-target theorem.
The target may bind upper faces; no critical-point hypothesis is imposed. -/
theorem lowerBoxBoundary_minimum_derivative_toward_ge_half_gap
    (lower upper point : ι → ℝ) (potential : (ι → ℝ) → ℝ)
    (derivative : (ι → ℝ) →L[ℝ] ℝ) (face : ι → ι → ℝ)
    (hpoint : point ∈ lowerBoxBoundary lower upper)
    (hmin : IsMinOn potential (lowerBoxBoundary lower upper) point)
    (hdiff : HasFDerivAt potential derivative point)
    (hwidth : ∀ player, lower player < upper player)
    (hdiagonal : ∀ player, face player player = lower player)
    (hfaceUpper : ∀ player other, face player other ≤ upper other)
    (hfaceGap : ∀ player other, lower other - face player other ≤ 2)
    (hdrift : ∀ player, point player = lower player →
      1 ≤ derivative (point - face player))
    (target : ι → ℝ) (gap : ℝ) (hgap : 0 ≤ gap)
    (htargetLower : ∀ player, gap ≤ target player - lower player)
    (htargetUpper : target ≤ upper) :
    gap / 2 ≤ derivative (target - point) := by
  have hsigns := lowerBoxBoundary_minimum_partial_signs lower upper point potential
    derivative face hpoint hmin hdiff hwidth hdiagonal hfaceUpper
    (fun player hplayer => lt_of_lt_of_le zero_lt_one (hdrift player hplayer))
  have hhalf := lowerBoxBoundary_minimum_lowerPartials_sum_ge_half lower upper point
    potential derivative face hpoint hmin hdiff hwidth hdiagonal hfaceUpper hfaceGap hdrift
  have hsum : gap * (∑ player, if point player = lower player then
      derivative (Pi.single player 1) else 0) ≤ derivative (target - point) := by
    rw [Finset.mul_sum]
    conv_rhs => rw [pi_eq_sum_univ' (target - point)]
    rw [map_sum]
    apply Finset.sum_le_sum
    intro player _
    rw [map_smul]
    change gap * (if point player = lower player then
      derivative (Pi.single player 1) else 0) ≤
        (target player - point player) * derivative (Pi.single player 1)
    by_cases hlower : point player = lower player
    · simp only [hlower, ite_true]
      exact mul_le_mul_of_nonneg_right (htargetLower player) ((hsigns player).1 hlower)
    · simp only [hlower, ite_false, mul_zero]
      by_cases hupper : point player = upper player
      · exact mul_nonneg_of_nonpos_of_nonpos
          (by rw [hupper]; exact sub_nonpos.mpr (htargetUpper player))
          ((hsigns player).2.2 hupper)
      · rw [(hsigns player).2.1
          (lt_of_le_of_ne (hpoint.1.1 player) (Ne.symm hlower))
          (lt_of_le_of_ne (hpoint.1.2 player) hupper)]
        simp
  have hmul := mul_le_mul_of_nonneg_left hhalf hgap
  linarith

omit [Fintype ι] [DecidableEq ι] in
/-- The adaptive upper cap is what keeps reflection inside the original box. -/
theorem adaptiveLowerBox_reflection_mem
    (lower target point : ι → ℝ)
    (hlower : ∀ player, 0 ≤ lower player)
    (htarget : target ∈ Set.Icc (fun _ => (0 : ℝ)) (fun _ => 3))
    (hpoint : point ∈ Set.Icc lower (fun player => max (target player) 1)) :
    2 • point - target ∈ Set.Icc (fun _ => (-3 : ℝ)) (fun _ => 3) := by
  constructor <;> intro player
  · simp only [two_nsmul, Pi.add_apply, Pi.sub_apply]
    have hnonneg := (hlower player).trans (hpoint.1 player)
    have hupper := htarget.2 player
    linarith
  · simp only [two_nsmul, Pi.add_apply, Pi.sub_apply]
    have hupper : point player ≤ max (target player) 1 := hpoint.2 player
    have hnonneg : 0 ≤ target player := htarget.1 player
    have hbound : target player ≤ 3 := htarget.2 player
    rcases le_total (target player) 1 with hsmall | hlarge
    · rw [max_eq_right hsmall] at hupper
      linarith
    · rw [max_eq_left hlarge] at hupper
      linarith

omit [Fintype ι] [DecidableEq ι] in
/-- All times up to the reflected endpoint are boxed, including both endpoints. -/
theorem adaptiveLowerBox_segment_mem
    (lower target point : ι → ℝ)
    (hlower : ∀ player, 0 ≤ lower player)
    (htarget : target ∈ Set.Icc (fun _ => (0 : ℝ)) (fun _ => 3))
    (hpoint : point ∈ Set.Icc lower (fun player => max (target player) 1))
    (time : ℝ) (htime : time ∈ Set.Icc (0 : ℝ) 2) :
    target + time • (point - target) ∈
      Set.Icc (fun _ => (-3 : ℝ)) (fun _ => 3) := by
  have hreflection := adaptiveLowerBox_reflection_mem lower target point hlower htarget hpoint
  have htargetBox : target ∈ Set.Icc (fun _ => (-3 : ℝ)) (fun _ => 3) :=
    ⟨fun player => (by norm_num : (-3 : ℝ) ≤ 0).trans (htarget.1 player), htarget.2⟩
  rcases htime with ⟨htimeLower, htimeUpper⟩
  have hconvex := (convex_Icc (fun _ : ι => (-3 : ℝ)) (fun _ => 3))
    htargetBox hreflection (show 0 ≤ 1 - time / 2 by linarith)
    (show 0 ≤ time / 2 by linarith) (show 1 - time / 2 + time / 2 = 1 by ring)
  convert hconvex using 1
  ext player
  simp only [two_nsmul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- A negative derivative at the right endpoint, above the initial value,
forces a maximum strictly above both endpoints at an interior time. -/
theorem exists_interior_maximum_of_endpoint_derivative_neg
    (function : ℝ → ℝ) (slope : ℝ)
    (hcontinuous : ContinuousOn function (Set.Icc (0 : ℝ) 1))
    (hderivative : HasDerivAt function slope 1) (hslope : slope < 0)
    (hendpoint : function 0 ≤ function 1) :
    ∃ time ∈ Set.Ioo (0 : ℝ) 1,
      function 0 < function time ∧ function 1 < function time ∧
      IsMaxOn function (Set.Icc (0 : ℝ) 1) time := by
  obtain ⟨time, htime, hmaximum⟩ := isCompact_Icc.exists_isMaxOn
    (show (Set.Icc (0 : ℝ) 1).Nonempty from ⟨0, by norm_num⟩) hcontinuous
  have hstrict : function 1 < function time := by
    apply lt_of_le_of_ne (hmaximum (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num))
    intro hequal
    have honeMax : IsMaxOn function (Set.Icc (0 : ℝ) 1) 1 := by
      intro value hvalue
      rw [hequal]
      exact hmaximum hvalue
    have hlocal : IsLocalMaxOn function (Set.Icc (0 : ℝ) 1) 1 :=
      Filter.mem_of_superset self_mem_nhdsWithin honeMax
    have hnonpos := hlocal.hasFDerivWithinAt_nonpos
      (hasDerivAt_iff_hasFDerivAt.mp hderivative).hasFDerivWithinAt
      (sub_mem_posTangentConeAt_of_segment_subset
        ((convex_Icc (0 : ℝ) 1).segment_subset
          (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num)
          (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num)))
    have hnonneg : 0 ≤ slope := by
      simpa using hnonpos
    exact (not_lt_of_ge hnonneg) hslope
  have hzero : 0 < time := by
    apply lt_of_le_of_ne htime.1
    intro hequal
    rw [← hequal] at hstrict
    exact (not_lt_of_ge hendpoint) hstrict
  have hone : time < 1 := by
    apply lt_of_le_of_ne htime.2
    intro hequal
    rw [hequal] at hstrict
    exact (lt_irrefl _) hstrict
  exact ⟨time, ⟨hzero, hone⟩, hendpoint.trans_lt hstrict, hstrict, hmaximum⟩

end Math

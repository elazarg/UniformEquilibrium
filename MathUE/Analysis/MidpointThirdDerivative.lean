import Mathlib.Analysis.Calculus.Taylor

/-! # A sharp third-derivative consequence of midpoint reversal

Two Lagrange remainders give the sharp constant without introducing an
additional integral identity. All regularity is local to the closed segment.
-/

noncomputable section

namespace Math

open Set

theorem taylorWithinEval_two_eq
    (function : ℝ → ℝ) (endpoint : ℝ) (hne : (1 : ℝ) ≠ endpoint)
    (hregular : ContDiffAt ℝ 3 function 1) :
    taylorWithinEval function 2 (Set.uIcc 1 endpoint) 1 endpoint =
      function 1 + (endpoint - 1) * deriv function 1 +
        (endpoint - 1) ^ 2 * iteratedDeriv 2 function 1 / 2 := by
  have hwithin : ∀ order : ℕ, order ≤ 3 →
      iteratedDerivWithin order function (Set.uIcc 1 endpoint) 1 =
        iteratedDeriv order function 1 := by
    intro order horder
    exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne)
      (hregular.of_le (by exact_mod_cast horder)) (left_mem_uIcc)
  rw [taylor_within_apply]
  simp only [Finset.sum_range_succ]
  rw [hwithin 0 (by norm_num), hwithin 1 (by norm_num), hwithin 2 (by norm_num)]
  norm_num [iteratedDeriv_zero, iteratedDeriv_one, Nat.factorial]
  ring

/-- A reflected endpoint no lower than the initial endpoint, and a negative
midpoint slope of magnitude at least half the gap, force a third derivative
of at least three times the gap somewhere strictly inside the segment. -/
theorem exists_thirdDerivative_ge_three_gap
    (function : ℝ → ℝ) (gap : ℝ)
    (hregular : ∀ time ∈ Set.Icc (0 : ℝ) 2, ContDiffAt ℝ 3 function time)
    (hendpoints : function 0 ≤ function 2)
    (hslope : deriv function 1 ≤ -gap / 2) :
    ∃ time ∈ Set.Ioo (0 : ℝ) 2, 3 * gap ≤ iteratedDeriv 3 function time := by
  have hleft : ContDiffOn ℝ 3 function (Set.uIcc (1 : ℝ) 0) := by
    intro time htime
    apply (hregular time ?_).contDiffWithinAt
    norm_num [Set.uIcc] at htime
    exact ⟨htime.1, htime.2.trans (by norm_num)⟩
  have hright : ContDiffOn ℝ 3 function (Set.uIcc (1 : ℝ) 2) := by
    intro time htime
    apply (hregular time ?_).contDiffWithinAt
    norm_num [Set.uIcc] at htime
    exact ⟨(by norm_num : (0 : ℝ) ≤ 1).trans htime.1, htime.2⟩
  obtain ⟨left, hleftTime, hleftTaylor⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) (by norm_num : (1 : ℝ) ≠ 0) hleft
  obtain ⟨right, hrightTime, hrightTaylor⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) (by norm_num : (1 : ℝ) ≠ 2) hright
  rw [taylorWithinEval_two_eq function 0 (by norm_num)
    (hregular 1 (by norm_num))] at hleftTaylor
  rw [taylorWithinEval_two_eq function 2 (by norm_num)
    (hregular 1 (by norm_num))] at hrightTaylor
  norm_num [Nat.factorial] at hleftTaylor hrightTaylor
  have hleftMem : left ∈ Set.Ioo (0 : ℝ) 2 := by
    norm_num [Set.uIoo] at hleftTime
    exact ⟨hleftTime.1, hleftTime.2.trans (by norm_num)⟩
  have hrightMem : right ∈ Set.Ioo (0 : ℝ) 2 := by
    norm_num [Set.uIoo] at hrightTime
    exact ⟨(by norm_num : (0 : ℝ) < 1).trans hrightTime.1, hrightTime.2⟩
  by_cases hleftLarge : 3 * gap ≤ iteratedDeriv 3 function left
  · exact ⟨left, hleftMem, hleftLarge⟩
  · refine ⟨right, hrightMem, ?_⟩
    have hleftSmall := lt_of_not_ge hleftLarge
    linarith

/-- The affine-line third derivative is the actual directional third
Fréchet derivative. The ambient function only needs to be C³ on an open
neighborhood of the evaluated point, rather than globally smooth. -/
theorem thirdDerivative_affineLine_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (potential : E → ℝ) (domain : Set E) (hopen : IsOpen domain)
    (hregular : ContDiffOn ℝ 3 potential domain)
    (point direction : E) (time : ℝ) (hpoint : point + time • direction ∈ domain) :
    iteratedDeriv 3 (fun rate : ℝ => potential (point + rate • direction)) time =
      iteratedFDeriv ℝ 3 potential (point + time • direction) (fun _ => direction) := by
  let linear : ℝ →L[ℝ] E := (1 : ℝ →L[ℝ] ℝ).smulRight direction
  let shifted : E → ℝ := fun input => potential (point + input)
  let shiftedDomain : Set E := (fun input => point + input) ⁻¹' domain
  have hshiftOpen : IsOpen shiftedDomain :=
    hopen.preimage (continuous_const.add continuous_id)
  have hshiftRegular : ContDiffOn ℝ 3 shifted shiftedDomain :=
    hregular.comp (contDiff_const.add contDiff_id).contDiffOn (fun _ hmem => hmem)
  have hlinearMem : linear time ∈ shiftedDomain := by
    simpa [linear, shiftedDomain] using hpoint
  have hlineOpen : IsOpen (linear ⁻¹' shiftedDomain) := hshiftOpen.preimage linear.continuous
  have hlineRegular : ContDiffOn ℝ 3 (shifted ∘ linear) (linear ⁻¹' shiftedDomain) :=
    hshiftRegular.comp_continuousLinearMap linear
  have hchain := linear.iteratedFDerivWithin_comp_right hshiftRegular
    hshiftOpen.uniqueDiffOn hlineOpen.uniqueDiffOn hlinearMem (i := 3) (by norm_num)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hlineOpen.uniqueDiffOn
    (hlineRegular.contDiffAt (hlineOpen.mem_nhds hlinearMem)) hlinearMem,
    iteratedFDerivWithin_eq_iteratedFDeriv hshiftOpen.uniqueDiffOn
      (hshiftRegular.contDiffAt (hshiftOpen.mem_nhds hlinearMem)) hlinearMem] at hchain
  change iteratedFDeriv ℝ 3 (shifted ∘ linear) time (fun _ => (1 : ℝ)) = _
  rw [hchain]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hlinearTime : linear time = time • direction := by simp [linear]
  have hlinearOne : linear 1 = direction := by simp [linear]
  rw [hlinearTime, hlinearOne]
  change iteratedFDeriv ℝ 3 (fun input => potential (point + input))
    (time • direction) (fun _ => direction) = _
  rw [iteratedFDeriv_comp_add_left]

end Math

import MathUE.Analysis.MidpointThirdDerivative
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # The exact weighted third-derivative midpoint identity

The integral Taylor remainder gives the exact identity and kernel mass.
Regularity is local to the entire closed segment, including its endpoints.
-/

noncomputable section

namespace Math

open Set

def midpointThirdDerivativeKernel (time : ℝ) : ℝ := (1 - |time - 1|) ^ 2

theorem midpointThirdDerivativeKernel_nonneg (time : ℝ) :
    0 ≤ midpointThirdDerivativeKernel time := sq_nonneg _

theorem integral_midpointThirdDerivativeKernel_mul_eq_split
    (function : ℝ → ℝ) (hcontinuous : ContinuousOn function (Icc (0 : ℝ) 2)) :
    (∫ time in (0 : ℝ)..2, midpointThirdDerivativeKernel time * function time) =
      (∫ time in (0 : ℝ)..1, time ^ 2 * function time) +
        ∫ time in (1 : ℝ)..2, (2 - time) ^ 2 * function time := by
  have hkernel : Continuous midpointThirdDerivativeKernel :=
    (continuous_const.sub (continuous_id.sub continuous_const).abs).pow 2
  have hproduct := hkernel.continuousOn.mul hcontinuous
  have hleft := (hproduct.mono (show Icc (0 : ℝ) 1 ⊆ Icc 0 2 by
    intro time htime; exact ⟨htime.1, htime.2.trans (by norm_num)⟩)).intervalIntegrable_of_Icc
      (μ := MeasureTheory.volume)
      (by norm_num : (0 : ℝ) ≤ 1)
  have hrightContinuous := hproduct.mono (show Icc (1 : ℝ) 2 ⊆ Icc 0 2 by
    intro time htime; exact ⟨(by norm_num : (0 : ℝ) ≤ 1).trans htime.1, htime.2⟩)
  have hright := hrightContinuous.intervalIntegrable_of_Icc
    (μ := MeasureTheory.volume) (by norm_num : (1 : ℝ) ≤ 2)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft hright
  simp only [Pi.mul_apply] at hsplit
  rw [← hsplit]
  congr 1
  · apply intervalIntegral.integral_congr
    intro time htime
    have htime' : time ≤ 1 := (show time ∈ Icc (0 : ℝ) 1 by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using htime).2
    dsimp [midpointThirdDerivativeKernel]
    rw [abs_of_nonpos (sub_nonpos.mpr htime')]
    ring
  · apply intervalIntegral.integral_congr
    intro time htime
    have htime' : 1 ≤ time := (show time ∈ Icc (1 : ℝ) 2 by
      simpa only [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using htime).1
    dsimp [midpointThirdDerivativeKernel]
    rw [abs_of_nonneg (sub_nonneg.mpr htime')]
    ring

/-- The two half-interval identities, with ordinary derivatives. -/
theorem midpoint_thirdDerivative_half_integrals
    (function : ℝ → ℝ)
    (hregular : ∀ time ∈ Icc (0 : ℝ) 2, ContDiffAt ℝ 3 function time) :
    (∫ time in (0 : ℝ)..1, time ^ 2 * iteratedDeriv 3 function time) =
        iteratedDeriv 2 function 1 - 2 * deriv function 1 +
          2 * function 1 - 2 * function 0 ∧
      (∫ time in (1 : ℝ)..2, (2 - time) ^ 2 * iteratedDeriv 3 function time) =
        -iteratedDeriv 2 function 1 - 2 * deriv function 1 +
          2 * function 2 - 2 * function 1 := by
  have hleft : ContDiffOn ℝ 3 function (uIcc (1 : ℝ) 0) := by
    intro time htime
    norm_num [uIcc] at htime
    exact (hregular time ⟨htime.1, htime.2.trans (by norm_num)⟩).contDiffWithinAt
  have hright : ContDiffOn ℝ 3 function (uIcc (1 : ℝ) 2) := by
    intro time htime
    norm_num [uIcc] at htime
    exact (hregular time ⟨(by norm_num : (0 : ℝ) ≤ 1).trans htime.1,
      htime.2⟩).contDiffWithinAt
  have hleftWithin : EqOn (iteratedDerivWithin 3 function (uIcc (1 : ℝ) 0))
      (iteratedDeriv 3 function) (uIcc (1 : ℝ) 0) := by
    intro time htime
    apply iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (by norm_num))
      (hregular time ?_) htime
    norm_num [uIcc] at htime
    exact ⟨htime.1, htime.2.trans (by norm_num)⟩
  have hrightWithin : EqOn (iteratedDerivWithin 3 function (uIcc (1 : ℝ) 2))
      (iteratedDeriv 3 function) (uIcc (1 : ℝ) 2) := by
    intro time htime
    apply iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (by norm_num))
      (hregular time ?_) htime
    norm_num [uIcc] at htime
    exact ⟨(by norm_num : (0 : ℝ) ≤ 1).trans htime.1, htime.2⟩
  have hleftIntegral : (∫ time in (1 : ℝ)..0,
      ((0 - time) ^ 2 / 2) * iteratedDerivWithin 3 function (uIcc (1 : ℝ) 0) time) =
      -(1 / 2) * ∫ time in (0 : ℝ)..1, time ^ 2 * iteratedDeriv 3 function time := by
    rw [intervalIntegral.integral_symm]
    simp only [neg_mul]
    congr 1
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro time htime
    dsimp
    rw [hleftWithin (by simpa only [uIcc_comm] using htime)]
    ring
  have hrightIntegral : (∫ time in (1 : ℝ)..2,
      ((2 - time) ^ 2 / 2) * iteratedDerivWithin 3 function (uIcc (1 : ℝ) 2) time) =
      (1 / 2) * ∫ time in (1 : ℝ)..2, (2 - time) ^ 2 * iteratedDeriv 3 function time := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro time htime
    dsimp
    rw [hrightWithin htime]
    ring
  have hleftTaylor := taylor_integral_remainder (n := 2) hleft
  have hrightTaylor := taylor_integral_remainder (n := 2) hright
  norm_num only [Nat.factorial, Nat.cast_ofNat, smul_eq_mul] at hleftTaylor hrightTaylor
  rw [taylorWithinEval_two_eq function 0 (by norm_num)
    (hregular 1 (by norm_num)), hleftIntegral] at hleftTaylor
  rw [taylorWithinEval_two_eq function 2 (by norm_num)
    (hregular 1 (by norm_num)), hrightIntegral] at hrightTaylor
  norm_num at hleftTaylor hrightTaylor
  constructor <;> linarith

/-- The weighted midpoint identity. -/
theorem midpoint_thirdDerivative_integral_identity
    (function : ℝ → ℝ)
    (hregular : ∀ time ∈ Icc (0 : ℝ) 2, ContDiffAt ℝ 3 function time) :
    (function 2 - function 0) / 2 - deriv function 1 =
      (1 / 4) * ∫ time in (0 : ℝ)..2,
        midpointThirdDerivativeKernel time * iteratedDeriv 3 function time := by
  have hwhole : ContDiffOn ℝ 3 function (Icc (0 : ℝ) 2) :=
    fun time htime => (hregular time htime).contDiffWithinAt
  have hthird : ContinuousOn (iteratedDeriv 3 function) (Icc (0 : ℝ) 2) :=
    (hwhole.continuousOn_iteratedDerivWithin le_rfl
      (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 2))).congr fun time htime =>
        (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
          (hregular time htime) htime).symm
  rw [integral_midpointThirdDerivativeKernel_mul_eq_split _ hthird]
  obtain ⟨hleft, hright⟩ := midpoint_thirdDerivative_half_integrals function hregular
  rw [hleft, hright]
  ring

private theorem integral_square_distance (center first second : ℝ) :
    (∫ time in first..second, (center - time) ^ 2) =
      ((second - center) ^ 3 - (first - center) ^ 3) / 3 := by
  have hderivative : ∀ time ∈ uIcc first second,
      HasDerivAt (fun rate : ℝ => (rate - center) ^ 3 / 3) ((center - time) ^ 2) time := by
    intro time _
    convert (((hasDerivAt_id time).sub_const center).pow 3).div_const 3 using 1
    · funext rate
      dsimp
    · dsimp
      ring
  have hintegrable : IntervalIntegrable (fun time => (center - time) ^ 2)
      MeasureTheory.volume first second :=
    ((continuous_const.sub continuous_id).pow 2).intervalIntegrable first second
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderivative hintegrable
  simpa only [sub_div] using hFTC

/-- Nonnegative weighted kernel has exact mass one sixth. -/
theorem midpointThirdDerivativeKernel_weighted_mass :
    (1 / 4 : ℝ) * (∫ time in (0 : ℝ)..2, midpointThirdDerivativeKernel time) = 1 / 6 := by
  have hsplit := integral_midpointThirdDerivativeKernel_mul_eq_split
    (fun _ => (1 : ℝ)) continuousOn_const
  simp only [mul_one] at hsplit
  have hleft : (∫ time in (0 : ℝ)..1, time ^ 2) = 1 / 3 := by
    simpa using integral_square_distance 0 0 1
  rw [hleft, integral_square_distance 2 1 2] at hsplit
  rw [hsplit]
  norm_num

end Math

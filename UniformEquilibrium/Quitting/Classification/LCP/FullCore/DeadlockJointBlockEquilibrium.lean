/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.FullCore.DeadlockChargedReturn
import UniformEquilibrium.Quitting.Cycles.BlockPeriodicProfile
import Mathlib.Tactic.FunProp

/-!
# A joint-phase equilibrium for the full-core deadlock table

The literal reward table `FullCoreDeadlock.reward` has a three-phase periodic
product profile with supports `{0}`, `{2}`, and `{1, 3}`.  The last row has two
independent active quitters and therefore leaves the reduced singleton-lasso
class.  An exact algebraic certificate proves that its initial value is a
uniform-equilibrium payoff against arbitrary behavioral deviations.

This result is specific to the named completion, whose rewards for coalitions
of cardinality at least two are zero.
-/

noncomputable section

namespace GameTheory
namespace FullCoreDeadlock

open Math.Probability Math.PMFProduct Math.ProbabilityMassFunction

/-! ## The algebraic parameter -/

/-- The degree-eight polynomial selecting the joint-block profile. -/
def jointBlockPolynomial (t : ℝ) : ℝ :=
  -125 + 335 * t + 3056 * t ^ 2 - 908 * t ^ 3 - 24864 * t ^ 4 -
    41392 * t ^ 5 - 19328 * t ^ 6 + 5056 * t ^ 7 + 4352 * t ^ 8

/-- The denominator in the rational elimination parameter. -/
def jointBlockDenominator (t : ℝ) : ℝ :=
  50 + 10 * t - 836 * t ^ 2 - 344 * t ^ 3 + 144 * t ^ 4

/-- The numerator in the rational elimination parameter. -/
def jointBlockNumerator (t : ℝ) : ℝ :=
  30 * t - 148 * t ^ 2 + 88 * t ^ 3 + 112 * t ^ 4

theorem jointBlockPolynomial_leftEndpoint :
    jointBlockPolynomial ((191 : ℝ) / 1000) =
      -1374675715873650310293 / 3906250000000000000000 := by
  norm_num [jointBlockPolynomial]

theorem jointBlockPolynomial_rightEndpoint :
    jointBlockPolynomial ((24 : ℝ) / 125) =
      2923619984558827 / 59604644775390625 := by
  norm_num [jointBlockPolynomial]

/-- The selecting polynomial has a root in a narrow rational interval. -/
theorem exists_jointBlockParameter_mem_isolatingInterval :
    ∃ t : ℝ, t ∈ Set.Ioo ((191 : ℝ) / 1000) (24 / 125) ∧
      jointBlockPolynomial t = 0 := by
  have hleft : jointBlockPolynomial ((191 : ℝ) / 1000) < 0 := by
    rw [jointBlockPolynomial_leftEndpoint]
    norm_num
  have hright : 0 < jointBlockPolynomial ((24 : ℝ) / 125) := by
    rw [jointBlockPolynomial_rightEndpoint]
    norm_num
  have hcontinuous : ContinuousOn jointBlockPolynomial
      (Set.Icc ((191 : ℝ) / 1000) (24 / 125)) := by
    unfold jointBlockPolynomial
    fun_prop
  obtain ⟨t, htIcc, htroot⟩ :=
    intermediate_value_Icc (by norm_num : (191 : ℝ) / 1000 ≤ 24 / 125)
      hcontinuous ⟨hleft.le, hright.le⟩
  refine ⟨t, ⟨?_, ?_⟩, htroot⟩
  · exact lt_of_le_of_ne htIcc.1 fun h ↦ by
      subst t
      linarith
  · exact lt_of_le_of_ne htIcc.2 fun h ↦ by
      subst t
      linarith

/-- A fixed exact root used by the certificate. -/
def jointBlockParameter : ℝ :=
  Classical.choose exists_jointBlockParameter_mem_isolatingInterval

theorem jointBlockParameter_mem :
    jointBlockParameter ∈ Set.Ioo ((191 : ℝ) / 1000) (24 / 125) :=
  (Classical.choose_spec exists_jointBlockParameter_mem_isolatingInterval).1

theorem jointBlockParameter_root :
    jointBlockPolynomial jointBlockParameter = 0 :=
  (Classical.choose_spec exists_jointBlockParameter_mem_isolatingInterval).2

theorem jointBlockParameter_pos : 0 < jointBlockParameter :=
  lt_trans (by norm_num) jointBlockParameter_mem.1

private theorem sq_gt_lower {x : ℝ} (hx : (191 : ℝ) / 1000 < x) :
    ((191 : ℝ) / 1000) ^ 2 < x ^ 2 := by
  nlinarith [mul_pos (sub_pos.mpr hx) (by linarith :
    0 < x + (191 : ℝ) / 1000)]

private theorem cube_gt_lower {x : ℝ} (hx : (191 : ℝ) / 1000 < x) :
    ((191 : ℝ) / 1000) ^ 3 < x ^ 3 := by
  have hxpos : 0 < x := lt_trans (by norm_num) hx
  have hsq := sq_gt_lower hx
  nlinarith [mul_pos (sub_pos.mpr hsq) hxpos,
    mul_pos (by norm_num : 0 < ((191 : ℝ) / 1000) ^ 2) (sub_pos.mpr hx)]

/-- The first comparison polynomial used to bound the rational parameter. -/
def jointBlockLowerComparison (t : ℝ) : ℝ :=
  20 * jointBlockNumerator t - jointBlockDenominator t

theorem jointBlockLowerComparison_pos :
    0 < jointBlockLowerComparison jointBlockParameter := by
  have ht := jointBlockParameter_mem
  have ht2upper : jointBlockParameter ^ 2 < ((24 : ℝ) / 125) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr ht.2)
      (by linarith [jointBlockParameter_pos] :
        0 < (24 : ℝ) / 125 + jointBlockParameter)]
  have ht3lower := cube_gt_lower ht.1
  have ht4lower : ((191 : ℝ) / 1000) ^ 4 < jointBlockParameter ^ 4 := by
    nlinarith [mul_pos (sub_pos.mpr (sq_gt_lower ht.1))
      (by positivity : 0 < ((191 : ℝ) / 1000) ^ 2 + jointBlockParameter ^ 2)]
  unfold jointBlockLowerComparison jointBlockNumerator jointBlockDenominator
  norm_num at ht ht2upper ht3lower ht4lower ⊢
  nlinarith

/-- The second comparison polynomial used to bound the rational parameter. -/
def jointBlockUpperComparison (t : ℝ) : ℝ :=
  3 * jointBlockDenominator t - 50 * jointBlockNumerator t

theorem jointBlockUpperComparison_pos :
    0 < jointBlockUpperComparison jointBlockParameter := by
  have ht := jointBlockParameter_mem
  have ht2lower := sq_gt_lower ht.1
  have ht3upper : jointBlockParameter ^ 3 < ((24 : ℝ) / 125) ^ 3 := by
    have ht2upper : jointBlockParameter ^ 2 < ((24 : ℝ) / 125) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr ht.2)
        (by linarith [jointBlockParameter_pos] :
          0 < (24 : ℝ) / 125 + jointBlockParameter)]
    nlinarith [mul_pos (sub_pos.mpr ht2upper) jointBlockParameter_pos,
      mul_pos (by positivity : 0 < ((24 : ℝ) / 125) ^ 2)
        (sub_pos.mpr ht.2)]
  have ht4upper : jointBlockParameter ^ 4 < ((24 : ℝ) / 125) ^ 4 := by
    have ht2upper : jointBlockParameter ^ 2 < ((24 : ℝ) / 125) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr ht.2)
        (by linarith [jointBlockParameter_pos] :
          0 < (24 : ℝ) / 125 + jointBlockParameter)]
    nlinarith [mul_pos (sub_pos.mpr ht2upper)
      (by positivity : 0 < jointBlockParameter ^ 2 + ((24 : ℝ) / 125) ^ 2)]
  unfold jointBlockUpperComparison jointBlockDenominator jointBlockNumerator
  norm_num at ht ht2lower ht3upper ht4upper ⊢
  nlinarith

/-- The denominator is safely positive throughout the isolating interval. -/
theorem jointBlockDenominator_gt_sixteen :
    16 < jointBlockDenominator jointBlockParameter := by
  have ht := jointBlockParameter_mem
  have ht2 : jointBlockParameter ^ 2 < ((24 : ℝ) / 125) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr ht.2)
      (by nlinarith [jointBlockParameter_pos] :
        0 < (24 : ℝ) / 125 + jointBlockParameter)]
  have ht3 : jointBlockParameter ^ 3 < ((24 : ℝ) / 125) ^ 3 := by
    have hpos : 0 < jointBlockParameter := jointBlockParameter_pos
    nlinarith [mul_pos (sub_pos.mpr ht2) hpos,
      mul_pos (by positivity : 0 < ((24 : ℝ) / 125) ^ 2)
        (sub_pos.mpr ht.2)]
  have ht4 : 0 ≤ jointBlockParameter ^ 4 := by positivity
  unfold jointBlockDenominator
  nlinarith

theorem jointBlockDenominator_pos :
    0 < jointBlockDenominator jointBlockParameter :=
  lt_trans (by norm_num) jointBlockDenominator_gt_sixteen

/-- The secondary elimination coordinate. -/
def jointBlockSecondary : ℝ :=
  jointBlockNumerator jointBlockParameter /
    jointBlockDenominator jointBlockParameter

theorem one_twentieth_lt_jointBlockSecondary :
    (1 : ℝ) / 20 < jointBlockSecondary := by
  unfold jointBlockSecondary
  rw [lt_div_iff₀ jointBlockDenominator_pos]
  have hcomp := jointBlockLowerComparison_pos
  unfold jointBlockLowerComparison at hcomp
  nlinarith

theorem jointBlockSecondary_lt_three_fiftieths :
    jointBlockSecondary < (3 : ℝ) / 50 := by
  unfold jointBlockSecondary
  rw [div_lt_iff₀ jointBlockDenominator_pos]
  have hcomp := jointBlockUpperComparison_pos
  unfold jointBlockUpperComparison at hcomp
  nlinarith

/-! ## Exact hazards and elimination identities -/

/-- Player `1`'s hazard in the joint phase. -/
def jointBlockP1 : ℝ := jointBlockSecondary

/-- Player `0`'s hazard in the first phase. -/
def jointBlockP0 : ℝ :=
  (jointBlockParameter + jointBlockSecondary) / (1 - jointBlockSecondary)

/-- Player `3`'s hazard in the joint phase. -/
def jointBlockP3 : ℝ :=
  2 * jointBlockParameter / (1 + 2 * jointBlockParameter)

/-- The survival probability in the middle phase. -/
def jointBlockQ2 : ℝ :=
  (1 - 4 * jointBlockSecondary - 2 * jointBlockParameter) /
    ((1 - 2 * jointBlockSecondary - jointBlockParameter) *
      (1 + jointBlockSecondary))

/-- Player `2`'s hazard in the middle phase. -/
def jointBlockP2 : ℝ := 1 - jointBlockQ2

/-- The four corresponding survival probabilities. -/
def jointBlockQ0 : ℝ := 1 - jointBlockP0
def jointBlockQ1 : ℝ := 1 - jointBlockP1
def jointBlockQ3 : ℝ := 1 - jointBlockP3

theorem jointBlockP1_bounds :
    (1 : ℝ) / 20 < jointBlockP1 ∧ jointBlockP1 < 3 / 50 :=
  ⟨one_twentieth_lt_jointBlockSecondary,
    jointBlockSecondary_lt_three_fiftieths⟩

theorem jointBlockP0_bounds :
    (1 : ℝ) / 4 < jointBlockP0 ∧ jointBlockP0 < 27 / 100 := by
  have ht := jointBlockParameter_mem
  have hy := jointBlockP1_bounds
  have hden : 0 < 1 - jointBlockSecondary := by
    dsimp [jointBlockP1] at hy
    linarith
  constructor
  · rw [jointBlockP0, lt_div_iff₀ hden]
    dsimp [jointBlockP1] at hy
    norm_num at ht hy ⊢
    nlinarith
  · rw [jointBlockP0, div_lt_iff₀ hden]
    dsimp [jointBlockP1] at hy
    norm_num at ht hy ⊢
    nlinarith

theorem jointBlockP3_bounds :
    (27 : ℝ) / 100 < jointBlockP3 ∧ jointBlockP3 < 28 / 100 := by
  have ht := jointBlockParameter_mem
  have hden : 0 < 1 + 2 * jointBlockParameter := by
    linarith [jointBlockParameter_pos]
  constructor
  · rw [jointBlockP3, lt_div_iff₀ hden]
    norm_num at ht ⊢
    nlinarith
  · rw [jointBlockP3, div_lt_iff₀ hden]
    norm_num at ht ⊢
    nlinarith

private theorem jointBlockQ2_denominator_pos :
    0 < (1 - 2 * jointBlockSecondary - jointBlockParameter) *
      (1 + jointBlockSecondary) := by
  have ht := jointBlockParameter_mem
  have hy := jointBlockP1_bounds
  dsimp [jointBlockP1] at hy
  norm_num at ht hy ⊢
  exact mul_pos (by nlinarith) (by nlinarith)

theorem jointBlockQ2_bounds :
    (1 : ℝ) / 2 < jointBlockQ2 ∧ jointBlockQ2 < 3 / 5 := by
  have ht := jointBlockParameter_mem
  have hy := jointBlockP1_bounds
  dsimp [jointBlockP1] at hy
  have htpos := jointBlockParameter_pos
  have hypos : 0 < jointBlockSecondary := lt_trans (by norm_num) hy.1
  have hy2 : jointBlockSecondary ^ 2 < ((3 : ℝ) / 50) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hy.2)
      (by nlinarith : 0 < (3 : ℝ) / 50 + jointBlockSecondary)]
  have hty : jointBlockParameter * jointBlockSecondary <
      ((24 : ℝ) / 125) * (3 / 50) := by
    nlinarith [mul_pos (sub_pos.mpr ht.2) hypos,
      mul_pos (by norm_num : 0 < (24 : ℝ) / 125)
        (sub_pos.mpr hy.2)]
  constructor
  · rw [jointBlockQ2, lt_div_iff₀ jointBlockQ2_denominator_pos]
    norm_num at ht hy hy2 hty ⊢
    nlinarith [sq_nonneg jointBlockSecondary,
      mul_pos jointBlockParameter_pos hypos]
  · rw [jointBlockQ2, div_lt_iff₀ jointBlockQ2_denominator_pos]
    norm_num at ht hy hy2 hty ⊢
    nlinarith

theorem jointBlockP2_bounds :
    (2 : ℝ) / 5 < jointBlockP2 ∧ jointBlockP2 < 1 / 2 := by
  unfold jointBlockP2
  constructor <;> linarith [jointBlockQ2_bounds.1, jointBlockQ2_bounds.2]

theorem jointBlockQ0_eq :
    jointBlockQ0 * jointBlockQ1 =
      1 - 2 * jointBlockSecondary - jointBlockParameter := by
  have hden : 1 - jointBlockSecondary ≠ 0 := by
    linarith [jointBlockSecondary_lt_three_fiftieths]
  unfold jointBlockQ0 jointBlockP0 jointBlockQ1 jointBlockP1
  field_simp [hden]
  ring

theorem jointBlockQ3_eq :
    jointBlockQ3 = 1 / (1 + 2 * jointBlockParameter) := by
  have hden : 1 + 2 * jointBlockParameter ≠ 0 := by
    linarith [jointBlockParameter_pos]
  unfold jointBlockQ3 jointBlockP3
  field_simp
  ring

/-- The first quadratic generated by denominator clearing. -/
def jointBlockF0 (t y : ℝ) : ℝ :=
  (36 * t - 10) * y ^ 2 + t * (18 * t - 43) * y + t * (5 - 14 * t)

/-- The second quadratic generated by denominator clearing. -/
def jointBlockF1 (t y : ℝ) : ℝ :=
  4 * t * (1 + 2 * t) * y ^ 2 + (5 + 19 * t + 2 * t ^ 2) * y +
    t * (2 * t - 3)

theorem jointBlock_first_elimination (t y : ℝ) :
    (4 * t * (1 + 2 * t)) * jointBlockF0 t y -
        (36 * t - 10) * jointBlockF1 t y =
      jointBlockDenominator t * y - jointBlockNumerator t := by
  unfold jointBlockF0 jointBlockF1 jointBlockDenominator jointBlockNumerator
  ring

theorem jointBlock_second_elimination (t : ℝ)
    (hD : jointBlockDenominator t ≠ 0) :
    jointBlockDenominator t ^ 2 *
        jointBlockF1 t (jointBlockNumerator t / jointBlockDenominator t) =
      40 * t ^ 2 * jointBlockPolynomial t := by
  unfold jointBlockF1
  field_simp [hD]
  unfold jointBlockDenominator jointBlockNumerator jointBlockPolynomial
  ring

theorem jointBlockF1_eq_zero :
    jointBlockF1 jointBlockParameter jointBlockSecondary = 0 := by
  have h := jointBlock_second_elimination jointBlockParameter
    jointBlockDenominator_pos.ne'
  rw [jointBlockParameter_root, mul_zero] at h
  unfold jointBlockSecondary
  have hsq : 0 < jointBlockDenominator jointBlockParameter ^ 2 := by
    exact sq_pos_of_pos jointBlockDenominator_pos
  nlinarith

theorem jointBlockF0_eq_zero :
    jointBlockF0 jointBlockParameter jointBlockSecondary = 0 := by
  have h := jointBlock_first_elimination jointBlockParameter jointBlockSecondary
  rw [jointBlockF1_eq_zero, mul_zero, sub_zero] at h
  have hratio : jointBlockDenominator jointBlockParameter * jointBlockSecondary =
      jointBlockNumerator jointBlockParameter := by
    unfold jointBlockSecondary
    field_simp [jointBlockDenominator_pos.ne']
  rw [hratio, sub_self] at h
  have hfactor : 0 < 4 * jointBlockParameter *
      (1 + 2 * jointBlockParameter) := by
    exact mul_pos (mul_pos (by norm_num) jointBlockParameter_pos)
      (by linarith [jointBlockParameter_pos])
  nlinarith

private theorem jointBlock_E0_algebra (t y : ℝ)
    (hB : (1 - 2 * y - t) * (1 + y) ≠ 0)
    (hC : 1 + 2 * t ≠ 0) (hF : jointBlockF0 t y = 0) :
    ((1 - 4 * y - 2 * t) / ((1 - 2 * y - t) * (1 + y))) *
        (4 * (y * (1 - 2 * t / (1 + 2 * t)) +
          (1 - y) * (2 * t / (1 + 2 * t))) +
          (1 - y) * (1 - 2 * t / (1 + 2 * t))) = 1 := by
  have hq3 : 1 - 2 * t / (1 + 2 * t) = 1 / (1 + 2 * t) := by
    apply (eq_div_iff hC).2
    rw [sub_mul, div_mul_cancel₀ _ hC]
    ring
  have hbracket :
      4 * (y * (1 - 2 * t / (1 + 2 * t)) +
          (1 - y) * (2 * t / (1 + 2 * t))) +
          (1 - y) * (1 - 2 * t / (1 + 2 * t)) =
        (4 * (y + (1 - y) * (2 * t)) + (1 - y)) / (1 + 2 * t) := by
    rw [hq3]
    field_simp [hC]
  rw [hbracket, div_mul_div_comm]
  apply (div_eq_iff (mul_ne_zero hB hC)).2
  calc
    (1 - 4 * y - 2 * t) * (4 * (y + (1 - y) * (2 * t)) + (1 - y)) =
        (1 - 2 * y - t) * (1 + y) * (1 + 2 * t) +
          jointBlockF0 t y := by
      unfold jointBlockF0
      ring
    _ = 1 * ((1 - 2 * y - t) * (1 + y) * (1 + 2 * t)) := by
      rw [hF]
      ring

private theorem jointBlock_E1_algebra (t y : ℝ)
    (hY : 1 - y ≠ 0) (hB : (1 - 2 * y - t) * (1 + y) ≠ 0)
    (hC : 1 + 2 * t ≠ 0) (hF : jointBlockF1 t y = 0) :
    3 * ((t + y) / (1 - y)) +
        (1 - (t + y) / (1 - y)) *
          (2 * (1 - (1 - 4 * y - 2 * t) / ((1 - 2 * y - t) * (1 + y))) +
            ((1 - 4 * y - 2 * t) / ((1 - 2 * y - t) * (1 + y))) *
              (1 - 2 * t / (1 + 2 * t))) =
      1 + 4 * t := by
  have hBC : (1 - 2 * y - t) * (1 + y) * (1 + 2 * t) ≠ 0 :=
    mul_ne_zero hB hC
  have hq0 :
      1 - (t + y) / (1 - y) = (1 - 2 * y - t) / (1 - y) := by
    apply (eq_div_iff hY).2
    rw [sub_mul, div_mul_cancel₀ _ hY]
    ring
  have hp2 :
      1 - (1 - 4 * y - 2 * t) / ((1 - 2 * y - t) * (1 + y)) =
        (((1 - 2 * y - t) * (1 + y)) - (1 - 4 * y - 2 * t)) /
          ((1 - 2 * y - t) * (1 + y)) := by
    apply (eq_div_iff hB).2
    rw [sub_mul, div_mul_cancel₀ _ hB]
    ring
  have hq3 : 1 - 2 * t / (1 + 2 * t) = 1 / (1 + 2 * t) := by
    apply (eq_div_iff hC).2
    rw [sub_mul, div_mul_cancel₀ _ hC]
    ring
  have hfirst :
      2 * ((((1 - 2 * y - t) * (1 + y)) - (1 - 4 * y - 2 * t)) /
          ((1 - 2 * y - t) * (1 + y))) =
        (2 * (((1 - 2 * y - t) * (1 + y)) - (1 - 4 * y - 2 * t)) *
            (1 + 2 * t)) /
          (((1 - 2 * y - t) * (1 + y)) * (1 + 2 * t)) := by
    rw [mul_div]
    exact (mul_div_mul_right
      (2 * (((1 - 2 * y - t) * (1 + y)) - (1 - 4 * y - 2 * t)))
      ((1 - 2 * y - t) * (1 + y)) hC).symm
  have hsecond :
      ((1 - 4 * y - 2 * t) / ((1 - 2 * y - t) * (1 + y))) *
          (1 / (1 + 2 * t)) =
        (1 - 4 * y - 2 * t) /
          (((1 - 2 * y - t) * (1 + y)) * (1 + 2 * t)) := by
    rw [div_mul_div_comm]
    ring
  have hinner :
      2 * (1 - (1 - 4 * y - 2 * t) / ((1 - 2 * y - t) * (1 + y))) +
          ((1 - 4 * y - 2 * t) / ((1 - 2 * y - t) * (1 + y))) *
            (1 - 2 * t / (1 + 2 * t)) =
        (2 * (((1 - 2 * y - t) * (1 + y)) - (1 - 4 * y - 2 * t)) *
            (1 + 2 * t) + (1 - 4 * y - 2 * t)) /
          (((1 - 2 * y - t) * (1 + y)) * (1 + 2 * t)) := by
    rw [hp2, hq3, hfirst, hsecond, ← add_div]
  rw [hq0, hinner]
  have hphase0 :
      3 * ((t + y) / (1 - y)) =
        ((3 * (t + y)) *
            (((1 - 2 * y - t) * (1 + y)) * (1 + 2 * t))) /
          ((1 - y) *
            (((1 - 2 * y - t) * (1 + y)) * (1 + 2 * t))) := by
    rw [mul_div]
    exact (mul_div_mul_right (3 * (t + y)) (1 - y) hBC).symm
  rw [hphase0, div_mul_div_comm, ← add_div]
  apply (div_eq_iff (mul_ne_zero hY hBC)).2
  calc
    (3 * (t + y)) *
          (((1 - 2 * y - t) * (1 + y)) * (1 + 2 * t)) +
        (1 - 2 * y - t) *
          (2 * (((1 - 2 * y - t) * (1 + y)) - (1 - 4 * y - 2 * t)) *
            (1 + 2 * t) + (1 - 4 * y - 2 * t)) =
      (1 + 4 * t) *
          ((1 - y) * (((1 - 2 * y - t) * (1 + y)) * (1 + 2 * t))) +
        (1 - 2 * y - t) * jointBlockF1 t y := by
      unfold jointBlockF1
      ring
    _ = (1 + 4 * t) *
        ((1 - y) * (((1 - 2 * y - t) * (1 + y)) * (1 + 2 * t))) := by
      rw [hF, mul_zero, add_zero]

private theorem jointBlock_E2_algebra (t y : ℝ)
    (hY : 1 - y ≠ 0) (hC : 1 + 2 * t ≠ 0) :
    (1 - 2 * t / (1 + 2 * t)) *
        (1 + 2 * (((t + y) / (1 - y)) * (1 - y) - y)) = 1 := by
  have hp0q1 : ((t + y) / (1 - y)) * (1 - y) - y = t := by
    rw [div_mul_cancel₀ _ hY]
    ring
  have hq3 : 1 - 2 * t / (1 + 2 * t) = 1 / (1 + 2 * t) := by
    apply (eq_div_iff hC).2
    rw [sub_mul, div_mul_cancel₀ _ hC]
    ring
  rw [hp0q1, hq3]
  exact div_mul_cancel₀ 1 hC

private theorem jointBlock_E3_algebra (t y : ℝ)
    (hY : 1 - y ≠ 0) (hB : (1 - 2 * y - t) * (1 + y) ≠ 0) :
    (1 - (t + y) / (1 - y)) * (1 - y) *
        (2 * (1 - (1 - 4 * y - 2 * t) / ((1 - 2 * y - t) * (1 + y))) +
          ((1 - 4 * y - 2 * t) / ((1 - 2 * y - t) * (1 + y))) * (1 - y)) =
      1 := by
  have hq0q1 :
      (1 - (t + y) / (1 - y)) * (1 - y) = 1 - 2 * y - t := by
    rw [sub_mul, div_mul_cancel₀ _ hY]
    ring
  have hp2 :
      1 - (1 - 4 * y - 2 * t) / ((1 - 2 * y - t) * (1 + y)) =
        (((1 - 2 * y - t) * (1 + y)) - (1 - 4 * y - 2 * t)) /
          ((1 - 2 * y - t) * (1 + y)) := by
    apply (eq_div_iff hB).2
    rw [sub_mul, div_mul_cancel₀ _ hB]
    ring
  rw [hq0q1, hp2]
  have hinner :
      2 * ((((1 - 2 * y - t) * (1 + y)) - (1 - 4 * y - 2 * t)) /
          ((1 - 2 * y - t) * (1 + y))) +
          ((1 - 4 * y - 2 * t) / ((1 - 2 * y - t) * (1 + y))) * (1 - y) =
        (2 * (((1 - 2 * y - t) * (1 + y)) - (1 - 4 * y - 2 * t)) +
            (1 - 4 * y - 2 * t) * (1 - y)) /
          ((1 - 2 * y - t) * (1 + y)) := by
    rw [mul_div, div_mul_eq_mul_div, ← add_div]
  rw [hinner, mul_div]
  apply (div_eq_iff hB).2
  ring

/-- The inactive-player recursion identity in the joint phase. -/
theorem jointBlock_identity_E0 :
    jointBlockQ2 *
        (4 * (jointBlockP1 * jointBlockQ3 +
          jointBlockQ1 * jointBlockP3) + jointBlockQ1 * jointBlockQ3) = 1 := by
  have hD := jointBlockQ2_denominator_pos.ne'
  have hQ3 : 1 + 2 * jointBlockParameter ≠ 0 := by
    linarith [jointBlockParameter_pos]
  simpa [jointBlockQ2, jointBlockQ3, jointBlockP3, jointBlockQ1,
    jointBlockP1] using jointBlock_E0_algebra jointBlockParameter
      jointBlockSecondary hD hQ3 jointBlockF0_eq_zero

/-- The player-`1` endpoint identity. -/
theorem jointBlock_identity_E1 :
    3 * jointBlockP0 + jointBlockQ0 *
        (2 * jointBlockP2 + jointBlockQ2 * jointBlockQ3) =
      1 + 4 * jointBlockParameter := by
  have hP0 : 1 - jointBlockSecondary ≠ 0 := by
    linarith [jointBlockSecondary_lt_three_fiftieths]
  have hQ2 := jointBlockQ2_denominator_pos.ne'
  have hQ3 : 1 + 2 * jointBlockParameter ≠ 0 := by
    linarith [jointBlockParameter_pos]
  simpa [jointBlockP0, jointBlockQ0, jointBlockP2, jointBlockQ2,
    jointBlockQ3, jointBlockP3] using
      jointBlock_E1_algebra jointBlockParameter jointBlockSecondary
        hP0 hQ2 hQ3 jointBlockF1_eq_zero

/-- The player-`3` endpoint identity. -/
theorem jointBlock_identity_E2 :
    jointBlockQ3 *
        (1 + 2 * (jointBlockP0 * jointBlockQ1 - jointBlockP1)) = 1 := by
  have hP0 : 1 - jointBlockSecondary ≠ 0 := by
    linarith [jointBlockSecondary_lt_three_fiftieths]
  have hQ3 : 1 + 2 * jointBlockParameter ≠ 0 := by
    linarith [jointBlockParameter_pos]
  simpa [jointBlockQ3, jointBlockP3, jointBlockP0, jointBlockQ1,
    jointBlockP1] using
      jointBlock_E2_algebra jointBlockParameter jointBlockSecondary hP0 hQ3

/-- The phase-closure identity at player `3`. -/
theorem jointBlock_identity_E3 :
    jointBlockQ0 * jointBlockQ1 *
        (2 * jointBlockP2 + jointBlockQ2 * jointBlockQ1) = 1 := by
  have hY : 1 - jointBlockSecondary ≠ 0 := by
    linarith [jointBlockSecondary_lt_three_fiftieths]
  have hB := jointBlockQ2_denominator_pos.ne'
  simpa [jointBlockQ0, jointBlockP0, jointBlockQ1, jointBlockP1,
    jointBlockP2, jointBlockQ2] using
      jointBlock_E3_algebra jointBlockParameter jointBlockSecondary hY hB

/-! ## The three-phase product block -/

/-- The hazards of the solo-`0`, solo-`2`, and joint-`{1,3}` phases. -/
def jointBlockHazard : Fin 3 → Player → ℝ :=
  ![![jointBlockP0, 0, 0, 0],
    ![0, 0, jointBlockP2, 0],
    ![0, jointBlockP1, 0, jointBlockP3]]

theorem jointBlockHazard_nonneg :
    ∀ k who, 0 ≤ jointBlockHazard k who := by
  intro k who
  fin_cases k <;> fin_cases who <;> simp [jointBlockHazard] <;>
    linarith [jointBlockP0_bounds.1, jointBlockP1_bounds.1,
      jointBlockP2_bounds.1, jointBlockP3_bounds.1]

theorem jointBlockHazard_le_one :
    ∀ k who, jointBlockHazard k who ≤ 1 := by
  intro k who
  fin_cases k <;> fin_cases who <;> simp [jointBlockHazard] <;>
    linarith [jointBlockP0_bounds.2, jointBlockP1_bounds.2,
      jointBlockP2_bounds.2, jointBlockP3_bounds.2]

/-- The value displayed at the joint phase. -/
def jointBlockJointValue : Payoff Player :=
  ![1 / jointBlockQ2, jointBlockQ3, 1, jointBlockQ1]

/-- The value displayed at the solo-`2` phase. -/
def jointBlockMiddleValue : Payoff Player :=
  fun who ↦ jointBlockP2 * reward (quittingSingletonTerminal 2) who +
    jointBlockQ2 * jointBlockJointValue who

/-- The uniform-equilibrium payoff, displayed at the solo-`0` phase. -/
def jointBlockValue : Payoff Player :=
  fun who ↦ jointBlockP0 * reward (quittingSingletonTerminal 0) who +
    jointBlockQ0 * jointBlockMiddleValue who

/-- The closed four-row value path of the three-phase profile. -/
def jointBlockValuePath : Fin 4 → Payoff Player :=
  ![jointBlockValue, jointBlockMiddleValue, jointBlockJointValue, jointBlockValue]

@[simp] theorem jointBlockMiddleValue_zero : jointBlockMiddleValue 0 = 1 := by
  have hq2 : jointBlockQ2 ≠ 0 := by
    linarith [jointBlockQ2_bounds.1]
  simp [jointBlockMiddleValue, jointBlockJointValue, jointBlockP2,
    reward_quittingSingleton, deadlockMatrix]
  field_simp [hq2]

@[simp] theorem jointBlockMiddleValue_two : jointBlockMiddleValue 2 = 1 := by
  simp [jointBlockMiddleValue, jointBlockJointValue, jointBlockP2,
    reward_quittingSingleton, deadlockMatrix]

@[simp] theorem jointBlockMiddleValue_one :
    jointBlockMiddleValue 1 = 2 * jointBlockP2 + jointBlockQ2 * jointBlockQ3 := by
  simp [jointBlockMiddleValue, jointBlockJointValue, reward_quittingSingleton,
    deadlockMatrix]
  ring

@[simp] theorem jointBlockMiddleValue_three :
    jointBlockMiddleValue 3 = 2 * jointBlockP2 + jointBlockQ2 * jointBlockQ1 := by
  simp [jointBlockMiddleValue, jointBlockJointValue, reward_quittingSingleton,
    deadlockMatrix]
  ring

@[simp] theorem jointBlockValue_zero : jointBlockValue 0 = 1 := by
  simp [jointBlockValue, jointBlockQ0, reward_quittingSingleton, deadlockMatrix]

@[simp] theorem jointBlockValue_two :
    jointBlockValue 2 = 1 + 2 * jointBlockP0 := by
  simp [jointBlockValue, jointBlockQ0, reward_quittingSingleton, deadlockMatrix]
  ring

@[simp] theorem jointBlockValue_one :
    jointBlockValue 1 = 1 + 4 * jointBlockParameter := by
  simp [jointBlockValue, reward_quittingSingleton, deadlockMatrix]
  convert jointBlock_identity_E1 using 1
  all_goals ring

@[simp] theorem jointBlockValue_three :
    jointBlockValue 3 = 1 / jointBlockQ1 := by
  have hq1 : jointBlockQ1 ≠ 0 := by
    unfold jointBlockQ1 jointBlockP1
    linarith [jointBlockSecondary_lt_three_fiftieths]
  simp [jointBlockValue, reward_quittingSingleton, deadlockMatrix]
  apply eq_inv_of_mul_eq_one_left
  calc
    jointBlockQ0 * (2 * jointBlockP2 + jointBlockQ2 * jointBlockQ1) *
        jointBlockQ1 =
      jointBlockQ0 * jointBlockQ1 *
        (2 * jointBlockP2 + jointBlockQ2 * jointBlockQ1) := by ring
    _ = 1 := jointBlock_identity_E3

theorem jointBlockValue_coordinates :
    jointBlockValue =
      ![1, 1 + 4 * jointBlockParameter, 1 + 2 * jointBlockP0,
        1 / jointBlockQ1] := by
  funext who
  fin_cases who <;> simp

/-- All displayed values are nonnegative and at most three. -/
theorem jointBlockValuePath_mem_threeBox (stage : Fin 4) (who : Player) :
    0 ≤ jointBlockValuePath stage who ∧ jointBlockValuePath stage who ≤ 3 := by
  have ht := jointBlockParameter_mem
  have hp0 := jointBlockP0_bounds
  have hp1 := jointBlockP1_bounds
  have hp2 := jointBlockP2_bounds
  have hp3 := jointBlockP3_bounds
  have hq2bounds := jointBlockQ2_bounds
  norm_num at ht hp0 hp1 hp2 hp3 hq2bounds
  have hq1 : 0 < jointBlockQ1 := by
    unfold jointBlockQ1
    linarith
  have hq2 : 0 < jointBlockQ2 := lt_trans (by norm_num) jointBlockQ2_bounds.1
  have hq3 : 0 < jointBlockQ3 := by
    unfold jointBlockQ3
    linarith
  have hq1le : jointBlockQ1 ≤ 1 := by
    unfold jointBlockQ1
    linarith
  have hq3le : jointBlockQ3 ≤ 1 := by
    unfold jointBlockQ3
    linarith
  have hq2q1nonneg : 0 ≤ jointBlockQ2 * jointBlockQ1 :=
    mul_nonneg hq2.le hq1.le
  have hq2q3nonneg : 0 ≤ jointBlockQ2 * jointBlockQ3 :=
    mul_nonneg hq2.le hq3.le
  have hq2q1le : jointBlockQ2 * jointBlockQ1 ≤ jointBlockQ2 :=
    mul_le_of_le_one_right hq2.le hq1le
  have hq2q3le : jointBlockQ2 * jointBlockQ3 ≤ jointBlockQ2 :=
    mul_le_of_le_one_right hq2.le hq3le
  have hinvQ1nonneg : 0 ≤ jointBlockQ1⁻¹ := inv_nonneg.mpr hq1.le
  have hinvQ1le : jointBlockQ1⁻¹ ≤ 3 := by
    rw [inv_le_comm₀ hq1 (by norm_num : (0 : ℝ) < 3)]
    norm_num
    unfold jointBlockQ1
    nlinarith
  have hinvQ2nonneg : 0 ≤ jointBlockQ2⁻¹ := inv_nonneg.mpr hq2.le
  have hinvQ2le : jointBlockQ2⁻¹ ≤ 3 := by
    rw [inv_le_comm₀ hq2 (by norm_num : (0 : ℝ) < 3)]
    norm_num
    nlinarith [jointBlockQ2_bounds.1]
  have hvalue : ∀ player : Player,
      0 ≤ jointBlockValue player ∧ jointBlockValue player ≤ 3 := by
    intro player
    fin_cases player <;> simp <;> constructor <;> nlinarith
  have hmiddle : ∀ player : Player,
      0 ≤ jointBlockMiddleValue player ∧ jointBlockMiddleValue player ≤ 3 := by
    intro player
    fin_cases player <;> simp <;> constructor <;> nlinarith
  have hjoint : ∀ player : Player,
      0 ≤ jointBlockJointValue player ∧ jointBlockJointValue player ≤ 3 := by
    intro player
    fin_cases player <;> simp [jointBlockJointValue] <;>
      constructor <;> nlinarith
  fin_cases stage
  · simpa [jointBlockValuePath] using hvalue who
  · simpa [jointBlockValuePath] using hmiddle who
  · simpa [jointBlockValuePath] using hjoint who
  · simpa [jointBlockValuePath] using hvalue who

theorem four_le_quittingRewardBound_reward :
    (4 : ℝ) ≤ quittingRewardBound reward := by
  have h := abs_reward_le_quittingRewardBound reward
    (quittingSingletonTerminal 1) 0
  norm_num [reward_quittingSingleton, deadlockMatrix] at h ⊢
  exact h

theorem jointBlockValuePath_box (stage : Fin 4) (who : Player) :
    |jointBlockValuePath stage who| ≤ quittingRewardBound reward := by
  rw [abs_of_nonneg (jointBlockValuePath_mem_threeBox stage who).1]
  exact le_trans (jointBlockValuePath_mem_threeBox stage who).2
    (le_trans (by norm_num) four_le_quittingRewardBound_reward)

/-! ## Exact Bellman and endpoint equations -/

@[simp] private theorem expect_jointBlockCoin
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : Bool → ℝ) :
    expect (quittingHazardCoin p hp0 hp1) f =
      (1 - p) * f false + p * f true := by
  rw [expect_eq_sum, Fintype.sum_bool]
  simp
  ring

private theorem literalSingletonTerminal_eq (owner : Player) :
    (⟨{owner}, Finset.singleton_nonempty owner⟩ :
      {S : Finset Player // S.Nonempty}) = quittingSingletonTerminal owner := by
  apply Subtype.ext
  rfl

private theorem jointBlockRoot_zero_active :
    IsQuittingActiveRoot {0}
      (quittingBlockCycle jointBlockHazard jointBlockHazard_nonneg
        jointBlockHazard_le_one 0) := by
  intro who hwho
  fin_cases who <;>
    simp [quittingBlockCycle, rootOfHazard, jointBlockHazard] at hwho ⊢
  all_goals exact quittingHazardCoin_zero _ _

private theorem jointBlockRoot_two_active :
    IsQuittingActiveRoot {2}
      (quittingBlockCycle jointBlockHazard jointBlockHazard_nonneg
        jointBlockHazard_le_one 1) := by
  intro who hwho
  fin_cases who <;>
    simp [quittingBlockCycle, rootOfHazard, jointBlockHazard] at hwho ⊢
  all_goals exact quittingHazardCoin_zero _ _

private theorem jointBlockRoot_joint_active :
    IsQuittingActiveRoot {1, 3}
      (quittingBlockCycle jointBlockHazard jointBlockHazard_nonneg
        jointBlockHazard_le_one 2) := by
  intro who hwho
  fin_cases who <;>
    simp [quittingBlockCycle, rootOfHazard, jointBlockHazard] at hwho ⊢
  all_goals exact quittingHazardCoin_zero _ _

@[simp] private theorem reward_pair_one_three (who : Player) :
    reward (⟨{1, 3}, by simp⟩ : {S : Finset Player // S.Nonempty}) who = 0 := by
  simp [FullCoreDeadlock.reward]

@[simp] private theorem quitters_only_zero :
    {who : Player | ![true, false, false, false] who = true} = {0} := by
  ext who
  fin_cases who <;> simp

@[simp] private theorem quitters_only_one :
    {who : Player | ![false, true, false, false] who = true} = {1} := by
  ext who
  fin_cases who <;> simp

@[simp] private theorem quitters_only_two :
    {who : Player | ![false, false, true, false] who = true} = {2} := by
  ext who
  fin_cases who <;> simp

@[simp] private theorem quitters_only_three :
    {who : Player | ![false, false, false, true] who = true} = {3} := by
  ext who
  fin_cases who <;> simp

@[simp] private theorem quitters_one_three :
    {who : Player | ![false, true, false, true] who = true} = {1, 3} := by
  ext who
  fin_cases who <;> simp

@[simp] private theorem sum_only_zero (f : Player → ℝ) :
    (∑ who with ![true, false, false, false] who = true, f who) = f 0 := by
  classical
  change (∑ who ∈ Finset.univ.filter
    (fun who : Player ↦ ![true, false, false, false] who = true), f who) = f 0
  rw [show Finset.univ.filter
    (fun who : Player ↦ ![true, false, false, false] who = true) = {0} by
      ext who; fin_cases who <;> simp]
  simp

@[simp] private theorem sum_only_one (f : Player → ℝ) :
    (∑ who with ![false, true, false, false] who = true, f who) = f 1 := by
  classical
  change (∑ who ∈ Finset.univ.filter
    (fun who : Player ↦ ![false, true, false, false] who = true), f who) = f 1
  rw [show Finset.univ.filter
    (fun who : Player ↦ ![false, true, false, false] who = true) = {1} by
      ext who; fin_cases who <;> simp]
  simp

@[simp] private theorem sum_only_two (f : Player → ℝ) :
    (∑ who with ![false, false, true, false] who = true, f who) = f 2 := by
  classical
  change (∑ who ∈ Finset.univ.filter
    (fun who : Player ↦ ![false, false, true, false] who = true), f who) = f 2
  rw [show Finset.univ.filter
    (fun who : Player ↦ ![false, false, true, false] who = true) = {2} by
      ext who; fin_cases who <;> simp]
  simp

@[simp] private theorem sum_only_three (f : Player → ℝ) :
    (∑ who with ![false, false, false, true] who = true, f who) = f 3 := by
  classical
  change (∑ who ∈ Finset.univ.filter
    (fun who : Player ↦ ![false, false, false, true] who = true), f who) = f 3
  rw [show Finset.univ.filter
    (fun who : Player ↦ ![false, false, false, true] who = true) = {3} by
      ext who; fin_cases who <;> simp]
  simp

theorem jointBlockRoot_zero_successor :
    quittingRootSuccessorPayoff reward jointBlockMiddleValue
        (quittingBlockCycle jointBlockHazard jointBlockHazard_nonneg
          jointBlockHazard_le_one 0) =
      jointBlockValue := by
  funext who
  change quittingRootExpectedPayoff reward jointBlockMiddleValue
    (quittingBlockCycle jointBlockHazard jointBlockHazard_nonneg
      jointBlockHazard_le_one 0) who = _
  rw [quittingRootExpectedPayoff_singleton_active reward jointBlockMiddleValue _
    0 who jointBlockRoot_zero_active]
  rw [hazardOfRoot_quittingBlockCycle, literalSingletonTerminal_eq]
  simp [jointBlockHazard, jointBlockValue, jointBlockQ0]
  ring

theorem jointBlockRoot_two_successor :
    quittingRootSuccessorPayoff reward jointBlockJointValue
        (quittingBlockCycle jointBlockHazard jointBlockHazard_nonneg
          jointBlockHazard_le_one 1) =
      jointBlockMiddleValue := by
  funext who
  change quittingRootExpectedPayoff reward jointBlockJointValue
    (quittingBlockCycle jointBlockHazard jointBlockHazard_nonneg
      jointBlockHazard_le_one 1) who = _
  rw [quittingRootExpectedPayoff_singleton_active reward jointBlockJointValue _
    2 who jointBlockRoot_two_active]
  rw [hazardOfRoot_quittingBlockCycle, literalSingletonTerminal_eq]
  simp [jointBlockHazard, jointBlockMiddleValue, jointBlockP2]
  ring

theorem jointBlockRoot_joint_successor :
    quittingRootSuccessorPayoff reward jointBlockValue
        (quittingBlockCycle jointBlockHazard jointBlockHazard_nonneg
          jointBlockHazard_le_one 2) =
      jointBlockJointValue := by
  funext who
  change quittingRootExpectedPayoff reward jointBlockValue
    (quittingBlockCycle jointBlockHazard jointBlockHazard_nonneg
      jointBlockHazard_le_one 2) who = _
  rw [quittingRootExpectedPayoff_pair_active reward jointBlockValue _ 1 3 who
    (by decide) jointBlockRoot_joint_active]
  simp only [hazardOfRoot_quittingBlockCycle]
  fin_cases who <;>
    simp [jointBlockHazard, literalSingletonTerminal_eq,
      reward_quittingSingleton, deadlockMatrix, jointBlockJointValue]
  · have hq2 : jointBlockQ2 ≠ 0 := by
      linarith [jointBlockQ2_bounds.1]
    convert eq_inv_of_mul_eq_one_right jointBlock_identity_E0 using 1
    all_goals simp [jointBlockQ1, jointBlockQ3]
    all_goals ring
  · have hden : 1 + 2 * jointBlockParameter ≠ 0 := by
      linarith [jointBlockParameter_pos]
    unfold jointBlockQ3
    unfold jointBlockP3
    field_simp [hden]
    ring
  · convert jointBlock_identity_E2 using 1
    all_goals simp [jointBlockQ1, jointBlockQ3]
    all_goals ring
  · have hq1 : jointBlockQ1 ≠ 0 := by
      unfold jointBlockQ1
      linarith [jointBlockP1_bounds.2]
    field_simp [hq1]
    unfold jointBlockQ1
    ring

theorem jointBlockRoot_zero_endpointDifference (who : Player) :
    quittingRootEndpointDifference reward jointBlockMiddleValue
        (quittingBlockCycle jointBlockHazard jointBlockHazard_nonneg
          jointBlockHazard_le_one 0) who =
      ![0,
        jointBlockQ0 - (1 + 4 * jointBlockParameter),
        jointBlockQ0 - (1 + 2 * jointBlockP0),
        jointBlockQ0 - 1 / jointBlockQ1] who := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4,
    Math.PMFProduct.expect_pmfPi_fin4]
  fin_cases who <;>
    simp +decide [quittingBlockCycle, rootOfHazard, jointBlockHazard,
      quittingRootPayoff, quittingQuitters, FullCoreDeadlock.reward,
      deadlockMatrix, jointBlockQ0]
  · convert jointBlock_identity_E1 using 1
    all_goals simp [jointBlockQ0]
    all_goals ring
  · ring
  · have hq1 : jointBlockQ1 ≠ 0 := by
      unfold jointBlockQ1 jointBlockP1
      linarith [jointBlockSecondary_lt_three_fiftieths]
    apply eq_inv_of_mul_eq_one_left
    calc
      (1 - jointBlockP0) *
          (2 * jointBlockP2 + jointBlockQ2 * jointBlockQ1) * jointBlockQ1 =
        jointBlockQ0 * jointBlockQ1 *
          (2 * jointBlockP2 + jointBlockQ2 * jointBlockQ1) := by
            unfold jointBlockQ0
            ring
      _ = 1 := jointBlock_identity_E3

theorem jointBlockRoot_two_endpointDifference (who : Player) :
    quittingRootEndpointDifference reward jointBlockJointValue
        (quittingBlockCycle jointBlockHazard jointBlockHazard_nonneg
          jointBlockHazard_le_one 1) who =
      ![jointBlockQ2 - 1,
        jointBlockQ2 - (2 * jointBlockP2 + jointBlockQ2 * jointBlockQ3),
        0,
        jointBlockQ2 - (2 * jointBlockP2 + jointBlockQ2 * jointBlockQ1)] who := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4,
    Math.PMFProduct.expect_pmfPi_fin4]
  fin_cases who <;>
    simp +decide [quittingBlockCycle, rootOfHazard, jointBlockHazard,
      quittingRootPayoff, quittingQuitters, FullCoreDeadlock.reward,
      deadlockMatrix, jointBlockJointValue]
  · have hq2 : jointBlockQ2 ≠ 0 := by
      linarith [jointBlockQ2_bounds.1]
    field_simp [hq2]
    unfold jointBlockP2
    ring
  · unfold jointBlockP2
    ring
  · unfold jointBlockP2
    ring

theorem jointBlockRoot_joint_endpointDifference (who : Player) :
    quittingRootEndpointDifference reward jointBlockValue
        (quittingBlockCycle jointBlockHazard jointBlockHazard_nonneg
          jointBlockHazard_le_one 2) who =
      ![jointBlockQ1 * jointBlockQ3 - 1 / jointBlockQ2,
        0,
        jointBlockQ1 * jointBlockQ3 - 1,
        0] who := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4,
    Math.PMFProduct.expect_pmfPi_fin4]
  fin_cases who <;>
    simp +decide [quittingBlockCycle, rootOfHazard, jointBlockHazard,
      quittingRootPayoff, quittingQuitters, FullCoreDeadlock.reward,
      deadlockMatrix]
  · have hcont := eq_inv_of_mul_eq_one_right jointBlock_identity_E0
    unfold jointBlockQ1 jointBlockQ3 at hcont ⊢
    linear_combination -1 * hcont
  · have hden : 1 + 2 * jointBlockParameter ≠ 0 := by
      linarith [jointBlockParameter_pos]
    unfold jointBlockP3
    field_simp [hden]
    ring
  · have hcont := jointBlock_identity_E2
    unfold jointBlockQ1 jointBlockQ3 at hcont ⊢
    linear_combination -1 * hcont
  · have hq1 : jointBlockQ1 ≠ 0 := by
      unfold jointBlockQ1 jointBlockP1
      linarith [jointBlockSecondary_lt_three_fiftieths]
    field_simp [hq1]
    unfold jointBlockQ1
    ring

theorem jointBlockRoot_zero_isZeroEndpointNash :
    IsεQuittingRootEndpointNash reward jointBlockMiddleValue 0
      (quittingBlockCycle jointBlockHazard jointBlockHazard_nonneg
        jointBlockHazard_le_one 0) := by
  intro who
  rw [jointBlockRoot_zero_endpointDifference]
  have ht := jointBlockParameter_pos
  have hp0 := jointBlockP0_bounds
  have hp1 := jointBlockP1_bounds
  have hq0 : jointBlockQ0 < 1 := by
    unfold jointBlockQ0
    linarith
  have hq1 : 0 < jointBlockQ1 := by
    unfold jointBlockQ1
    linarith
  have hinv : 1 < 1 / jointBlockQ1 := by
    rw [lt_div_iff₀ hq1]
    unfold jointBlockQ1
    linarith
  have hinv' : 1 < jointBlockQ1⁻¹ := by
    simpa [one_div] using hinv
  fin_cases who <;> simp [jointBlockHazard] <;> nlinarith

theorem jointBlockRoot_two_isZeroEndpointNash :
    IsεQuittingRootEndpointNash reward jointBlockJointValue 0
      (quittingBlockCycle jointBlockHazard jointBlockHazard_nonneg
        jointBlockHazard_le_one 1) := by
  intro who
  rw [jointBlockRoot_two_endpointDifference]
  have hp2 := jointBlockP2_bounds
  have hq2 := jointBlockQ2_bounds
  have hq1 : 0 ≤ jointBlockQ1 := by
    unfold jointBlockQ1
    linarith [jointBlockP1_bounds.2]
  have hq3 : 0 ≤ jointBlockQ3 := by
    unfold jointBlockQ3
    linarith [jointBlockP3_bounds.2]
  fin_cases who <;> simp [jointBlockHazard] <;> nlinarith

theorem jointBlockRoot_joint_isZeroEndpointNash :
    IsεQuittingRootEndpointNash reward jointBlockValue 0
      (quittingBlockCycle jointBlockHazard jointBlockHazard_nonneg
        jointBlockHazard_le_one 2) := by
  intro who
  rw [jointBlockRoot_joint_endpointDifference]
  have hp1 := jointBlockP1_bounds
  have hp3 := jointBlockP3_bounds
  have hq1 : 0 < jointBlockQ1 := by
    unfold jointBlockQ1
    linarith
  have hq2 := jointBlockQ2_bounds
  have hq3 : 0 < jointBlockQ3 := by
    unfold jointBlockQ3
    linarith
  have hprod : jointBlockQ1 * jointBlockQ3 < 1 := by
    have hq1lt : jointBlockQ1 < 1 := by
      unfold jointBlockQ1
      linarith
    have hq3le : jointBlockQ3 ≤ 1 := by
      unfold jointBlockQ3
      linarith
    exact lt_of_lt_of_le (mul_lt_of_lt_one_left hq3 hq1lt) hq3le
  have hinv : 1 < 1 / jointBlockQ2 := by
    rw [lt_div_iff₀ (lt_trans (by norm_num) hq2.1)]
    linarith
  have hinv' : 1 < jointBlockQ2⁻¹ := by
    simpa [one_div] using hinv
  fin_cases who <;> simp [jointBlockHazard] <;> nlinarith

/-! ## Certificate and semantic conclusion -/

/-- The displayed three-phase profile is an exact block certificate for the
literal full-core deadlock reward table. -/
theorem jointBlock_isQuittingBlockCertificate :
    IsQuittingBlockCertificate (m := 2) reward jointBlockHazard
      jointBlockValuePath := by
  refine isQuittingBlockCertificate_of_root jointBlockHazard_nonneg
    jointBlockHazard_le_one jointBlockValuePath_box rfl ?_ ?_ ?_ ?_
  · intro k
    fin_cases k
    · exact jointBlockRoot_zero_successor.symm
    · exact jointBlockRoot_two_successor.symm
    · exact jointBlockRoot_joint_successor.symm
  · intro k
    fin_cases k
    · exact jointBlockRoot_zero_isZeroEndpointNash
    · exact jointBlockRoot_two_isZeroEndpointNash
    · exact jointBlockRoot_joint_isZeroEndpointNash
  · refine ⟨0, ?_⟩
    simp [continueMass, jointBlockHazard, Fin.prod_univ_succ]
    linarith [jointBlockP0_bounds.1]
  · intro who
    right
    fin_cases who <;>
      simp [FullCoreDeadlock.reward, deadlockMatrix, quittingSingletonTerminal]

/-- **The named full-core deadlock table has a uniform-equilibrium payoff.**
The fixed payoff is the initial value of the exact three-phase product block,
and unilateral deviations range over arbitrary behavioral strategies. -/
theorem reward_isUniformEquilibriumPayoff_jointBlock :
    (quittingGame reward).IsUniformEquilibriumPayoff none jointBlockValue :=
  isUniformEquilibriumPayoff_of_isQuittingBlockCertificate
    jointBlock_isQuittingBlockCertificate

/-- An existential form exposing only the existence of some fixed payoff. -/
theorem exists_uniformEquilibriumPayoff_reward :
    ∃ x : Payoff Player,
      (quittingGame reward).IsUniformEquilibriumPayoff none x :=
  ⟨jointBlockValue, reward_isUniformEquilibriumPayoff_jointBlock⟩

end FullCoreDeadlock
end GameTheory

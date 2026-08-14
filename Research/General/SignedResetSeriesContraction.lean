/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Circulation.SingletonFaceCirculation

/-!
# Series contraction of affine reset phases

Two consecutive reset phases are again one reset phase.  The effective
target is a canonical convex combination of the two original targets.  This
is the exact algebra needed to eliminate an intermediate phase of a signed
owner--outsider walk.

Common pinned coordinates and common lower floors survive the contraction.
A coordinate pinned in only one of the two phases need not survive; this is
the precise algebraic location of the stationarization/calibration problem.
-/

noncomputable section

namespace GameTheory

variable {ι : Type*}

/-- One affine contraction phase towards `target`. -/
def affineResetPhase (ratio : ℝ) (target state : ι → ℝ) : ι → ℝ :=
  fun who => ratio * state who + (1 - ratio) * target who

/-- Contraction ratio of two phases in chronological series. -/
def resetSeriesRatio (firstRatio secondRatio : ℝ) : ℝ :=
  firstRatio * secondRatio

/-- Weight of the first target in the effective series target. -/
def resetSeriesFirstWeight (firstRatio secondRatio : ℝ) : ℝ :=
  secondRatio * (1 - firstRatio) /
    (1 - firstRatio * secondRatio)

/-- Weight of the second target in the effective series target. -/
def resetSeriesSecondWeight (firstRatio secondRatio : ℝ) : ℝ :=
  (1 - secondRatio) / (1 - firstRatio * secondRatio)

/-- Canonical effective target of two consecutive phases. -/
def resetSeriesEffectiveTarget
    (firstRatio secondRatio : ℝ)
    (firstTarget secondTarget : ι → ℝ) : ι → ℝ :=
  fun who =>
    resetSeriesFirstWeight firstRatio secondRatio * firstTarget who +
      resetSeriesSecondWeight firstRatio secondRatio * secondTarget who

theorem resetSeries_denominator_pos
    {firstRatio secondRatio : ℝ}
    (_hfirst0 : 0 ≤ firstRatio) (hfirst1 : firstRatio < 1)
    (hsecond0 : 0 ≤ secondRatio) (hsecond1 : secondRatio < 1) :
    0 < 1 - firstRatio * secondRatio := by
  have hfirstGap : 0 ≤ (1 - firstRatio) * secondRatio :=
    mul_nonneg (by linarith) hsecond0
  have hsecondGap : 0 < 1 - secondRatio := by linarith
  nlinarith

theorem resetSeriesWeights_nonneg_sum_one
    {firstRatio secondRatio : ℝ}
    (hfirst0 : 0 ≤ firstRatio) (hfirst1 : firstRatio < 1)
    (hsecond0 : 0 ≤ secondRatio) (hsecond1 : secondRatio < 1) :
    0 ≤ resetSeriesFirstWeight firstRatio secondRatio ∧
      0 ≤ resetSeriesSecondWeight firstRatio secondRatio ∧
      resetSeriesFirstWeight firstRatio secondRatio +
        resetSeriesSecondWeight firstRatio secondRatio = 1 := by
  have hden := resetSeries_denominator_pos
    hfirst0 hfirst1 hsecond0 hsecond1
  have hfirstNumerator : 0 ≤ secondRatio * (1 - firstRatio) :=
    mul_nonneg hsecond0 (by linarith)
  have hsecondNumerator : 0 ≤ 1 - secondRatio := by linarith
  constructor
  · exact div_nonneg hfirstNumerator hden.le
  constructor
  · exact div_nonneg hsecondNumerator hden.le
  · unfold resetSeriesFirstWeight resetSeriesSecondWeight
    rw [← add_div]
    have hnumerator :
        secondRatio * (1 - firstRatio) + (1 - secondRatio) =
          1 - firstRatio * secondRatio := by ring
    rw [hnumerator]
    exact div_self (ne_of_gt hden)

/-- Under strict positive contractions, both original phase targets remain
visible with positive weight in the effective target. -/
theorem resetSeriesWeights_pos
    {firstRatio secondRatio : ℝ}
    (hfirst0 : 0 < firstRatio) (hfirst1 : firstRatio < 1)
    (hsecond0 : 0 < secondRatio) (hsecond1 : secondRatio < 1) :
    0 < resetSeriesFirstWeight firstRatio secondRatio ∧
      0 < resetSeriesSecondWeight firstRatio secondRatio := by
  have hden := resetSeries_denominator_pos
    hfirst0.le hfirst1 hsecond0.le hsecond1
  exact ⟨div_pos (mul_pos hsecond0 (by linarith)) hden,
    div_pos (by linarith) hden⟩

/-- **Exact series law.** Applying `first`, then `second`, is one affine
phase with product ratio and the canonical effective target. -/
theorem affineResetPhase_series
    {firstRatio secondRatio : ℝ}
    (hden : 1 - firstRatio * secondRatio ≠ 0)
    (firstTarget secondTarget state : ι → ℝ) :
    affineResetPhase secondRatio secondTarget
        (affineResetPhase firstRatio firstTarget state) =
      affineResetPhase (resetSeriesRatio firstRatio secondRatio)
        (resetSeriesEffectiveTarget firstRatio secondRatio
          firstTarget secondTarget) state := by
  have hw1 : (1 - firstRatio * secondRatio) *
      resetSeriesFirstWeight firstRatio secondRatio =
        secondRatio * (1 - firstRatio) := by
    unfold resetSeriesFirstWeight
    exact mul_div_cancel₀ _ hden
  have hw2 : (1 - firstRatio * secondRatio) *
      resetSeriesSecondWeight firstRatio secondRatio =
        1 - secondRatio := by
    unfold resetSeriesSecondWeight
    exact mul_div_cancel₀ _ hden
  funext who
  have heffective : (1 - firstRatio * secondRatio) *
      resetSeriesEffectiveTarget firstRatio secondRatio
        firstTarget secondTarget who =
      secondRatio * (1 - firstRatio) * firstTarget who +
        (1 - secondRatio) * secondTarget who := by
    unfold resetSeriesEffectiveTarget
    rw [mul_add]
    rw [← mul_assoc, hw1, ← mul_assoc, hw2]
  unfold affineResetPhase resetSeriesRatio
  rw [heffective]
  ring

/-- The product of two strict contraction ratios is again a strict
contraction ratio. -/
theorem resetSeriesRatio_mem_unitInterval
    {firstRatio secondRatio : ℝ}
    (hfirst0 : 0 ≤ firstRatio) (hfirst1 : firstRatio < 1)
    (hsecond0 : 0 ≤ secondRatio) (hsecond1 : secondRatio < 1) :
    0 ≤ resetSeriesRatio firstRatio secondRatio ∧
      resetSeriesRatio firstRatio secondRatio < 1 := by
  exact ⟨mul_nonneg hfirst0 hsecond0,
    sub_pos.mp (resetSeries_denominator_pos
      hfirst0 hfirst1 hsecond0 hsecond1)⟩

/-- Every coordinate pinned to the same value by both phases remains pinned
after series contraction. -/
theorem resetSeriesEffectiveTarget_eq_of_common_pin
    {firstRatio secondRatio : ℝ}
    (hfirst0 : 0 ≤ firstRatio) (hfirst1 : firstRatio < 1)
    (hsecond0 : 0 ≤ secondRatio) (hsecond1 : secondRatio < 1)
    (firstTarget secondTarget : ι → ℝ) (who : ι) (pinned : ℝ)
    (hfirst : firstTarget who = pinned)
    (hsecond : secondTarget who = pinned) :
    resetSeriesEffectiveTarget firstRatio secondRatio
      firstTarget secondTarget who = pinned := by
  have hweights := resetSeriesWeights_nonneg_sum_one
    hfirst0 hfirst1 hsecond0 hsecond1
  unfold resetSeriesEffectiveTarget
  rw [hfirst, hsecond]
  calc
    resetSeriesFirstWeight firstRatio secondRatio * pinned +
        resetSeriesSecondWeight firstRatio secondRatio * pinned =
      (resetSeriesFirstWeight firstRatio secondRatio +
        resetSeriesSecondWeight firstRatio secondRatio) * pinned := by ring
    _ = pinned := by rw [hweights.2.2, one_mul]

/-- **Cross-pin rigidity.**  If the first phase pins a coordinate, then its
series contraction pins that coordinate exactly iff the second phase pins it
too.  Thus a phase-specific owner cannot simply be eliminated: the adjacent
target must already satisfy the missing pin, or a calibration charge is
unavoidable. -/
theorem resetSeriesEffectiveTarget_eq_pin_iff_second_eq_pin
    {firstRatio secondRatio : ℝ}
    (hfirst0 : 0 < firstRatio) (hfirst1 : firstRatio < 1)
    (hsecond0 : 0 < secondRatio) (hsecond1 : secondRatio < 1)
    (firstTarget secondTarget : ι → ℝ) (who : ι) (pinned : ℝ)
    (hfirst : firstTarget who = pinned) :
    resetSeriesEffectiveTarget firstRatio secondRatio
        firstTarget secondTarget who = pinned ↔
      secondTarget who = pinned := by
  have hweights := resetSeriesWeights_nonneg_sum_one
    hfirst0.le hfirst1 hsecond0.le hsecond1
  have hsecondWeight := (resetSeriesWeights_pos
    hfirst0 hfirst1 hsecond0 hsecond1).2
  unfold resetSeriesEffectiveTarget
  rw [hfirst]
  constructor
  · intro heffective
    have hbalance : resetSeriesSecondWeight firstRatio secondRatio *
        (secondTarget who - pinned) = 0 := by
      calc
        resetSeriesSecondWeight firstRatio secondRatio *
            (secondTarget who - pinned) =
          (resetSeriesFirstWeight firstRatio secondRatio * pinned +
              resetSeriesSecondWeight firstRatio secondRatio *
                secondTarget who) -
            (resetSeriesFirstWeight firstRatio secondRatio +
              resetSeriesSecondWeight firstRatio secondRatio) * pinned := by
            ring
        _ = pinned - 1 * pinned := by rw [heffective, hweights.2.2]
        _ = 0 := by ring
    rcases mul_eq_zero.mp hbalance with hweightZero | hdifference
    · exact (ne_of_gt hsecondWeight hweightZero).elim
    · exact sub_eq_zero.mp hdifference
  · intro hsecond
    rw [hsecond]
    calc
      resetSeriesFirstWeight firstRatio secondRatio * pinned +
          resetSeriesSecondWeight firstRatio secondRatio * pinned =
        (resetSeriesFirstWeight firstRatio secondRatio +
          resetSeriesSecondWeight firstRatio secondRatio) * pinned := by ring
      _ = pinned := by rw [hweights.2.2, one_mul]

/-- Exact quantitative form of cross-pin rigidity: the contraction's pin
error is the adjacent phase's pin error times its canonical series weight. -/
theorem resetSeriesEffectiveTarget_sub_pin
    {firstRatio secondRatio : ℝ}
    (hfirst0 : 0 ≤ firstRatio) (hfirst1 : firstRatio < 1)
    (hsecond0 : 0 ≤ secondRatio) (hsecond1 : secondRatio < 1)
    (firstTarget secondTarget : ι → ℝ) (who : ι) (pinned : ℝ)
    (hfirst : firstTarget who = pinned) :
    resetSeriesEffectiveTarget firstRatio secondRatio
          firstTarget secondTarget who - pinned =
      resetSeriesSecondWeight firstRatio secondRatio *
        (secondTarget who - pinned) := by
  have hweights := resetSeriesWeights_nonneg_sum_one
    hfirst0 hfirst1 hsecond0 hsecond1
  unfold resetSeriesEffectiveTarget
  rw [hfirst]
  calc
    resetSeriesFirstWeight firstRatio secondRatio * pinned +
          resetSeriesSecondWeight firstRatio secondRatio * secondTarget who -
        pinned =
      (resetSeriesFirstWeight firstRatio secondRatio +
          resetSeriesSecondWeight firstRatio secondRatio - 1) * pinned +
        resetSeriesSecondWeight firstRatio secondRatio *
          (secondTarget who - pinned) := by ring
    _ = resetSeriesSecondWeight firstRatio secondRatio *
        (secondTarget who - pinned) := by rw [hweights.2.2]; ring

theorem abs_resetSeriesEffectiveTarget_sub_pin
    {firstRatio secondRatio : ℝ}
    (hfirst0 : 0 ≤ firstRatio) (hfirst1 : firstRatio < 1)
    (hsecond0 : 0 ≤ secondRatio) (hsecond1 : secondRatio < 1)
    (firstTarget secondTarget : ι → ℝ) (who : ι) (pinned : ℝ)
    (hfirst : firstTarget who = pinned) :
    |resetSeriesEffectiveTarget firstRatio secondRatio
          firstTarget secondTarget who - pinned| =
      resetSeriesSecondWeight firstRatio secondRatio *
        |secondTarget who - pinned| := by
  rw [resetSeriesEffectiveTarget_sub_pin hfirst0 hfirst1 hsecond0 hsecond1
    firstTarget secondTarget who pinned hfirst, abs_mul,
    abs_of_nonneg (resetSeriesWeights_nonneg_sum_one
      hfirst0 hfirst1 hsecond0 hsecond1).2.1]

/-- A common coordinatewise floor of both phase targets is also a floor of
the effective target. -/
theorem le_resetSeriesEffectiveTarget_of_common_floor
    {firstRatio secondRatio : ℝ}
    (hfirst0 : 0 ≤ firstRatio) (hfirst1 : firstRatio < 1)
    (hsecond0 : 0 ≤ secondRatio) (hsecond1 : secondRatio < 1)
    (firstTarget secondTarget floor : ι → ℝ)
    (hfirstFloor : ∀ who, floor who ≤ firstTarget who)
    (hsecondFloor : ∀ who, floor who ≤ secondTarget who)
    (who : ι) :
    floor who ≤ resetSeriesEffectiveTarget firstRatio secondRatio
      firstTarget secondTarget who := by
  have hweights := resetSeriesWeights_nonneg_sum_one
    hfirst0 hfirst1 hsecond0 hsecond1
  unfold resetSeriesEffectiveTarget
  calc
    floor who = 1 * floor who := by rw [one_mul]
    _ =
        resetSeriesFirstWeight firstRatio secondRatio * floor who +
          resetSeriesSecondWeight firstRatio secondRatio * floor who := by
      rw [← hweights.2.2]
      ring
    _ ≤ resetSeriesFirstWeight firstRatio secondRatio * firstTarget who +
          resetSeriesSecondWeight firstRatio secondRatio * secondTarget who :=
      add_le_add
        (mul_le_mul_of_nonneg_left (hfirstFloor who) hweights.1)
        (mul_le_mul_of_nonneg_left (hsecondFloor who) hweights.2.1)

/-! ## Closure of the mixed-solo target grammar -/

variable [Fintype ι]

/-- Effective owner distribution obtained by contracting two phase
distributions. -/
def resetSeriesMixWeight
    (firstRatio secondRatio : ℝ)
    (firstWeight secondWeight : ι → ℝ) : ι → ℝ :=
  fun owner =>
    resetSeriesFirstWeight firstRatio secondRatio * firstWeight owner +
      resetSeriesSecondWeight firstRatio secondRatio * secondWeight owner

/-- Convex phase distributions remain a convex distribution after series
contraction. -/
theorem resetSeriesMixWeight_nonneg_sum_one
    {firstRatio secondRatio : ℝ}
    (hfirst0 : 0 ≤ firstRatio) (hfirst1 : firstRatio < 1)
    (hsecond0 : 0 ≤ secondRatio) (hsecond1 : secondRatio < 1)
    (firstWeight secondWeight : ι → ℝ)
    (hfirstWeight0 : ∀ owner, 0 ≤ firstWeight owner)
    (hsecondWeight0 : ∀ owner, 0 ≤ secondWeight owner)
    (hfirstSum : ∑ owner, firstWeight owner = 1)
    (hsecondSum : ∑ owner, secondWeight owner = 1) :
    (∀ owner, 0 ≤ resetSeriesMixWeight firstRatio secondRatio
      firstWeight secondWeight owner) ∧
      ∑ owner, resetSeriesMixWeight firstRatio secondRatio
        firstWeight secondWeight owner = 1 := by
  have hseries := resetSeriesWeights_nonneg_sum_one
    hfirst0 hfirst1 hsecond0 hsecond1
  constructor
  · intro owner
    unfold resetSeriesMixWeight
    exact add_nonneg
      (mul_nonneg hseries.1 (hfirstWeight0 owner))
      (mul_nonneg hseries.2.1 (hsecondWeight0 owner))
  · unfold resetSeriesMixWeight
    rw [Finset.sum_add_distrib]
    simp_rw [← Finset.mul_sum]
    rw [hfirstSum, hsecondSum, mul_one, mul_one, hseries.2.2]

/-- The effective target of two mixed-solo phases is exactly the mixed-solo
target of their effective owner distribution.  No reward coordinate is lost
at the purely affine level. -/
theorem resetSeriesEffectiveTarget_mixTarget
    (reward : Finset ι → ι → ℝ)
    (firstRatio secondRatio : ℝ)
    (firstWeight secondWeight : ι → ℝ) :
    resetSeriesEffectiveTarget firstRatio secondRatio
        (mixTarget reward firstWeight) (mixTarget reward secondWeight) =
      mixTarget reward
        (resetSeriesMixWeight firstRatio secondRatio
          firstWeight secondWeight) := by
  funext who
  unfold resetSeriesEffectiveTarget resetSeriesMixWeight mixTarget
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro owner _
    ring
  · apply Finset.sum_congr rfl
    intro owner _
    ring

end GameTheory

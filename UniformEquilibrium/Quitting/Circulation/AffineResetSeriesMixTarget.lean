/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.LinearAlgebra.AffineResetSeries
import UniformEquilibrium.Quitting.Circulation.SingletonFaceCirculation

/-!
# Affine reset series for mixed-solo targets

The canonical effective target of two affine reset phases remains in the
mixed-solo target grammar, with an explicitly computed owner distribution.
-/

noncomputable section

namespace GameTheory

open Math.AffineResetSeries

variable {ι : Type*} [Fintype ι]

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
    (hfirst1 : firstRatio < 1)
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
    hfirst1 hsecond0 hsecond1
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
target of their effective owner distribution. -/
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

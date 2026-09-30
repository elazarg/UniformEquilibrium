/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.LinearAlgebra.UniformNonsingularity
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.StrictInversePassiveRowCycle

/-!
# Permutation inverse boundary of the strict three-player clocks

The literal off-diagonal perturbation of a permutation matrix enters the
strict-inverse chamber. Its actual right-cycle hazards tend to one as the
perturbation tends to zero. This records the boundary behavior only: it does
not substitute a unit hazard into the strict compiler or assert a uniform
calendar-size estimate over the approaching family.
-/

noncomputable section

namespace GameTheory.PermutationInverseClockBoundary

open Filter QuittingLCPClassification Math.LinearProgramming
open Math.LinearAlgebra
open Math.LinearProgramming.ThreeCycleInverseFormulas

/-- The weak-boundary singleton-difference matrix. -/
def matrix : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

/-- The literal zero-diagonal perturbation used by the passive-row source. -/
def perturbedMatrix (epsilon : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  matrix - epsilon • offDiagonalOnes (Fin 3)

theorem perturbedMatrix_literal (epsilon : ℝ) :
    perturbedMatrix epsilon =
      !![0, -epsilon, 1 - epsilon; 1 - epsilon, 0, -epsilon;
        -epsilon, 1 - epsilon, 0] := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [perturbedMatrix, matrix, offDiagonalOnes]

theorem perturbedMatrix_directed (epsilon : ℝ) :
    perturbedMatrix epsilon = directedCycleMatrix
      epsilon (1 - epsilon) (1 - epsilon) epsilon epsilon (1 - epsilon) := by
  rw [perturbedMatrix_literal]
  ext row column
  fin_cases row <;> fin_cases column <;> simp [directedCycleMatrix]

theorem perturbedMatrix_det (epsilon : ℝ) :
    (perturbedMatrix epsilon).det = (1 - epsilon) ^ 3 - epsilon ^ 3 := by
  rw [perturbedMatrix_directed, directedCycleMatrix_det]
  unfold cycleGap
  ring

/-- The source's literal inverse, delegated to the canonical six-parameter formula. -/
theorem perturbedMatrix_inverse (epsilon : ℝ) :
    (perturbedMatrix epsilon)⁻¹ = ((1 - epsilon) ^ 3 - epsilon ^ 3)⁻¹ •
      !![epsilon * (1 - epsilon), (1 - epsilon) ^ 2, epsilon ^ 2;
        epsilon ^ 2, epsilon * (1 - epsilon), (1 - epsilon) ^ 2;
        (1 - epsilon) ^ 2, epsilon ^ 2, epsilon * (1 - epsilon)] := by
  rw [perturbedMatrix_directed, directedCycleMatrix_inverse]
  have hgap : cycleGap epsilon (1 - epsilon) (1 - epsilon)
      epsilon epsilon (1 - epsilon) = (1 - epsilon) ^ 3 - epsilon ^ 3 := by
    unfold cycleGap
    ring
  rw [hgap]
  congr 1
  ext row column
  fin_cases row <;> fin_cases column <;> simp [pow_two, mul_comm]

private theorem perturb_gap_pos {epsilon : ℝ}
    (hpositive : 0 < epsilon) (hhalf : epsilon < 1 / 2) :
    0 < cycleGap epsilon (1 - epsilon) (1 - epsilon)
      epsilon epsilon (1 - epsilon) := by
  have hlt : epsilon < 1 - epsilon := by linarith
  have hpower := pow_lt_pow_left₀ hlt hpositive.le (by norm_num : (3 : ℕ) ≠ 0)
  unfold cycleGap
  nlinarith [hpower]

theorem perturbedMatrix_hasStrictlyPositiveInverse {epsilon : ℝ}
    (hpositive : 0 < epsilon) (hhalf : epsilon < 1 / 2) :
    HasStrictlyPositiveInverse (perturbedMatrix epsilon) := by
  rw [perturbedMatrix_directed]
  have hcomplement : 0 < 1 - epsilon := by linarith
  exact directedCycleMatrix_hasStrictlyPositiveInverse
    hpositive hcomplement hcomplement hpositive hpositive hcomplement
      (perturb_gap_pos hpositive hhalf)

/-- The original inverse is again a permutation matrix, not a strict inverse. -/
theorem matrix_inverse : matrix⁻¹ = !![0, 1, 0; 0, 0, 1; 1, 0, 0] := by
  simpa [perturbedMatrix] using perturbedMatrix_inverse 0

theorem matrix_det : matrix.det = 1 := by
  simpa [perturbedMatrix] using perturbedMatrix_det 0

theorem matrix_inverse_nonnegative (row column : Fin 3) : 0 ≤ matrix⁻¹ row column := by
  rw [matrix_inverse]
  fin_cases row <;> fin_cases column <;> norm_num

theorem matrix_not_hasStrictlyPositiveInverse : ¬ HasStrictlyPositiveInverse matrix := by
  intro hstrict
  have hzero := hstrict.2 0 0
  rw [matrix_inverse] at hzero
  norm_num at hzero

/-- The actual equal strict-cycle hazards. -/
def hazard (epsilon : ℝ) : ℝ := (1 - 2 * epsilon) / (1 - epsilon)

/-- Any reward table with this literal normalized singleton matrix has the
same six cyclic gaps, regardless of its own singletons or nonsingleton rows. -/
theorem right_parameters (reward : QuittingReward3) (epsilon : ℝ)
    (hmatrix : normalizedSoloMatrix reward = perturbedMatrix epsilon) :
    rightP reward = epsilon ∧ rightQ reward = 1 - epsilon ∧
      rightR reward = epsilon ∧ rightS reward = 1 - epsilon ∧
      rightT reward = epsilon ∧ rightU reward = 1 - epsilon := by
  have hentry (who owner : Fin 3) :
      quittingSoloReward reward owner who - quittingSoloReward reward who who =
        directedCycleMatrix epsilon (1 - epsilon) (1 - epsilon)
          epsilon epsilon (1 - epsilon) who owner := by
    rw [← normalizedSoloMatrix_eq_soloReward_sub]
    exact congrFun (congrFun (hmatrix.trans (perturbedMatrix_directed epsilon)) who) owner
  have h01 := hentry 0 1
  have h02 := hentry 0 2
  have h12 := hentry 1 2
  have h10 := hentry 1 0
  have h20 := hentry 2 0
  have h21 := hentry 2 1
  simp [directedCycleMatrix] at h01 h02 h12 h10 h20 h21
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold rightP
    linarith
  · exact h02
  · unfold rightR
    linarith
  · exact h10
  · unfold rightT
    linarith
  · exact h21

theorem rightSingletonCycle (reward : QuittingReward3) {epsilon : ℝ}
    (hpositive : 0 < epsilon) (hhalf : epsilon < 1 / 2)
    (hmatrix : normalizedSoloMatrix reward = perturbedMatrix epsilon) :
    RightSingletonCycle reward := by
  have hcomplement : 0 < 1 - epsilon := by linarith
  exact rightSingletonCycle_of_directedSoloMatrix reward
    epsilon (1 - epsilon) (1 - epsilon) epsilon epsilon (1 - epsilon)
      hpositive hcomplement hcomplement hpositive hpositive hcomplement
      (perturb_gap_pos hpositive hhalf) (hmatrix.trans (perturbedMatrix_directed epsilon))

/-- The actual compiler rates, not merely a candidate rate, equal the source
fraction for every table with the prescribed singleton-difference matrix. -/
theorem right_rates (reward : QuittingReward3) {epsilon : ℝ}
    (hpositive : 0 < epsilon) (hhalf : epsilon < 1 / 2)
    (hmatrix : normalizedSoloMatrix reward = perturbedMatrix epsilon) :
    rightAlpha reward = hazard epsilon ∧ rightBeta reward = hazard epsilon ∧
      rightGamma reward = hazard epsilon := by
  obtain ⟨hp, hq, hr, hs, ht, hu⟩ := right_parameters reward epsilon hmatrix
  have hcomplement : 0 < 1 - epsilon := by linarith
  have hden : 0 <
      (1 - epsilon) * (1 - epsilon) * (1 - epsilon) +
        (1 - epsilon) * (1 - epsilon) * epsilon + epsilon * (1 - epsilon) * epsilon := by
    positivity
  have hformula :
      ((1 - epsilon) * (1 - epsilon) * (1 - epsilon) - epsilon * epsilon * epsilon) /
        ((1 - epsilon) * (1 - epsilon) * (1 - epsilon) +
          (1 - epsilon) * (1 - epsilon) * epsilon + epsilon * (1 - epsilon) * epsilon) =
        hazard epsilon := by
    unfold hazard
    field_simp [hden.ne', hcomplement.ne']
    ring
  have hbeta :
      (1 - epsilon) * (1 - epsilon) * (1 - epsilon) +
        epsilon * (1 - epsilon) * (1 - epsilon) + epsilon * epsilon * (1 - epsilon) =
      (1 - epsilon) * (1 - epsilon) * (1 - epsilon) +
        (1 - epsilon) * (1 - epsilon) * epsilon + epsilon * (1 - epsilon) * epsilon := by
    ring
  have hgamma :
      (1 - epsilon) * (1 - epsilon) * (1 - epsilon) +
        (1 - epsilon) * epsilon * (1 - epsilon) + (1 - epsilon) * epsilon * epsilon =
      (1 - epsilon) * (1 - epsilon) * (1 - epsilon) +
        (1 - epsilon) * (1 - epsilon) * epsilon + epsilon * (1 - epsilon) * epsilon := by
    ring
  simp only [rightAlpha, rightBeta, rightGamma, rightDelta, hp, hq, hr, hs, ht, hu]
  rw [hbeta, hgamma]
  exact ⟨hformula, hformula, hformula⟩

/-- The equal hazards tend to one from the positive side. This is a limit
of strict clocks, not a unit-hazard clock supplied to the strict consumer. -/
theorem hazard_tendsto_one :
    Tendsto hazard (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
  have hnum : ContinuousAt (fun epsilon : ℝ => 1 - 2 * epsilon) 0 :=
    continuousAt_const.sub (continuousAt_const.mul continuousAt_id)
  have hden : ContinuousAt (fun epsilon : ℝ => 1 - epsilon) 0 :=
    continuousAt_const.sub continuousAt_id
  have hcontinuous : ContinuousAt hazard 0 := by
    change ContinuousAt (fun epsilon : ℝ => (1 - 2 * epsilon) / (1 - epsilon)) 0
    exact hnum.div hden (by norm_num : (1 : ℝ) - 0 ≠ 0)
  have hlimit := hcontinuous.tendsto
  have hzero : hazard 0 = 1 := by norm_num [hazard]
  rw [hzero] at hlimit
  exact hlimit.mono_left nhdsWithin_le_nhds

end GameTheory.PermutationInverseClockBoundary

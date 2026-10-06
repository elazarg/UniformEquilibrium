import UniformEquilibrium.Quitting.Cycles.SignedFourCycleRewardAdapter
import MathUE.SignedFourCycleLargerEigenvalue

/-! # Actual singleton-table tests for the larger spectral branch

These tests are literal reward comparisons and a determinant, not supplied
positive weights or a favorable strategic root. The smaller tests are unchanged.
-/

noncomputable section

namespace GameTheory.SignedFourCycleSingletonData

open QuittingLCPClassification

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable (data : SignedFourCycleSingletonData reward)

structure LargerTests : Prop where
  gZero_neg : data.g 0 < 0
  gOne_pos : 0 < data.g 1
  gTwo_neg : data.g 2 < 0
  gThree_pos : 0 < data.g 3
  lowerRight_gt_one : 1 < data.coefficients.lowerRight
  singleton_det_pos : 0 < (quittingSingletonMatrix reward).det

theorem singletonMatrix_eq_diagonal_mul_normalized :
    quittingSingletonMatrix reward =
      Matrix.diagonal data.b * data.coefficients.normalizedComparisonMatrix := by
  have hrow0 : quittingSingletonMatrix reward 0 = ![0, -data.b 0, data.g 0, data.h 0] := by
    funext player
    fin_cases player
    · simp [quittingSingletonMatrix]
    · simpa using data.successor 0
    · simpa using data.opposite 0
    · simpa using data.predecessor 0
  have hrow1 : quittingSingletonMatrix reward 1 = ![data.h 1, 0, -data.b 1, data.g 1] := by
    funext player
    fin_cases player
    · simpa using data.predecessor 1
    · simp [quittingSingletonMatrix]
    · simpa using data.successor 1
    · simpa using data.opposite 1
  have hrow2 : quittingSingletonMatrix reward 2 = ![data.g 2, data.h 2, 0, -data.b 2] := by
    funext player
    fin_cases player
    · simpa using data.opposite 2
    · simpa using data.predecessor 2
    · simp [quittingSingletonMatrix]
    · simpa using data.successor 2
  have hrow3 : quittingSingletonMatrix reward 3 = ![-data.b 3, data.g 3, data.h 3, 0] := by
    funext player
    fin_cases player
    · simpa using data.successor 3
    · simpa using data.opposite 3
    · simpa using data.predecessor 3
    · simp [quittingSingletonMatrix]
  ext row column
  simp only [Matrix.diagonal_mul]
  fin_cases row <;> fin_cases column <;>
    simp [hrow0, hrow1, hrow2, hrow3,
      Math.SignedFourCycleCoefficients.normalizedComparisonMatrix, coefficients]
  all_goals field_simp [ne_of_gt (data.b_pos 0), ne_of_gt (data.b_pos 1),
    ne_of_gt (data.b_pos 2), ne_of_gt (data.b_pos 3)]

theorem singletonMatrix_det_eq_characteristic :
    (quittingSingletonMatrix reward).det =
      (∏ player, data.b player) * -data.coefficients.characteristicAt 1 := by
  rw [data.singletonMatrix_eq_diagonal_mul_normalized, Matrix.det_mul,
    Matrix.det_diagonal, data.coefficients.normalizedComparisonMatrix_det]

theorem LargerTests.coefficientTests (tests : data.LargerTests) :
    data.coefficients.LargerBranchTests := {
  aZero_neg := div_neg_of_neg_of_pos tests.gZero_neg (data.b_pos 0)
  aOne_pos := div_pos tests.gOne_pos (data.b_pos 1)
  aTwo_neg := div_neg_of_neg_of_pos tests.gTwo_neg (data.b_pos 2)
  aThree_pos := div_pos tests.gThree_pos (data.b_pos 3)
  dOne_pos := div_pos (data.h_pos 1) (data.b_pos 1)
  dTwo_pos := div_pos (data.h_pos 2) (data.b_pos 2)
  dThree_pos := div_pos (data.h_pos 3) (data.b_pos 3)
  lowerRight_gt_one := tests.lowerRight_gt_one
  characteristic_one_neg := by
    have hdet := tests.singleton_det_pos
    rw [data.singletonMatrix_det_eq_characteristic] at hdet
    have hproduct : 0 < ∏ player, data.b player :=
      Finset.prod_pos (fun player _ => data.b_pos player)
    by_contra hnot
    have hnonpositive := mul_nonpos_of_nonneg_of_nonpos hproduct.le
      (neg_nonpos.mpr (le_of_not_gt hnot))
    exact hdet.not_ge hnonpositive
}

theorem larger_weights_positive_of_raw_tests (tests : data.LargerTests) :
    0 < data.coefficients.largerPeriodSurvival ∧
      data.coefficients.largerPeriodSurvival < 1 ∧
      0 < data.coefficients.largerRawWeightZero ∧
      0 < data.coefficients.largerRawWeightOne ∧
      0 < data.coefficients.largerRawWeightTwo ∧
      0 < data.coefficients.largerRawWeightThree :=
  data.coefficients.larger_weights_positive tests.coefficientTests

end GameTheory.SignedFourCycleSingletonData

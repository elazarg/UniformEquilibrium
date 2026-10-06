import MathUE.SignedFourCycleAlgebra
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-! # The larger transfer eigenvalue and positive four-cycle weights

The smaller-branch definitions and tests are unchanged. The input here is
scalar sign data and a negative characteristic value at one, not a supplied
eigenvector, strategic witness or positive reconstructed weight.
-/

noncomputable section

namespace Math.SignedFourCycleCoefficients

variable (c : SignedFourCycleCoefficients)

def characteristicAt (value : ℝ) : ℝ :=
  (value - c.upperLeft) * (value - c.lowerRight) - c.upperRight * c.lowerLeft

def normalizedComparisonMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, -1, c.aZero, c.dZero;
    c.dOne, 0, -1, c.aOne;
    c.aTwo, c.dTwo, 0, -1;
    -1, c.aThree, c.dThree, 0]

theorem normalizedComparisonMatrix_det :
    c.normalizedComparisonMatrix.det = -c.characteristicAt 1 := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Matrix.det_fin_three,
    Matrix.submatrix_apply]
  norm_num [normalizedComparisonMatrix, Fin.succAbove]
  unfold characteristicAt upperLeft upperRight lowerLeft lowerRight
  ring

def largerEigenvalue : ℝ :=
  (c.upperLeft + c.lowerRight + Real.sqrt c.discriminant) / 2

def largerPeriodSurvival : ℝ := 1 / c.largerEigenvalue
def largerRawWeightZero : ℝ := c.upperRight
def largerRawWeightOne : ℝ := c.largerEigenvalue - c.upperLeft
def largerRawWeightThree : ℝ :=
  c.largerPeriodSurvival * (c.aTwo * c.largerRawWeightZero + c.dTwo * c.largerRawWeightOne)
def largerRawWeightTwo : ℝ :=
  c.largerPeriodSurvival * c.dOne * c.largerRawWeightZero + c.aOne * c.largerRawWeightThree

theorem eigenvalues_straddle_one_of_characteristic_neg
    (hnegative : c.characteristicAt 1 < 0) :
    0 < c.discriminant ∧ c.smallerEigenvalue < 1 ∧ 1 < c.largerEigenvalue := by
  have hidentity : c.discriminant =
      (c.upperLeft + c.lowerRight - 2) ^ 2 - 4 * c.characteristicAt 1 := by
    unfold discriminant characteristicAt
    ring
  have hdisc : 0 < c.discriminant := by
    rw [hidentity]
    nlinarith [sq_nonneg (c.upperLeft + c.lowerRight - 2)]
  have hsqrt := Real.sq_sqrt hdisc.le
  have hnonnegative := Real.sqrt_nonneg c.discriminant
  have hupper : c.upperLeft + c.lowerRight - 2 < Real.sqrt c.discriminant := by
    by_contra hnot
    have hle := le_of_not_gt hnot
    nlinarith
  have hlower : -(Real.sqrt c.discriminant) < c.upperLeft + c.lowerRight - 2 := by
    by_contra hnot
    have hle := le_of_not_gt hnot
    nlinarith
  refine ⟨hdisc, ?_, ?_⟩
  · unfold smallerEigenvalue
    linarith
  · unfold largerEigenvalue
    linarith

theorem larger_characteristic (hdisc : 0 ≤ c.discriminant) :
    c.characteristicAt c.largerEigenvalue = 0 := by
  have hsqrt := Real.sq_sqrt hdisc
  unfold discriminant at hsqrt
  unfold characteristicAt largerEigenvalue discriminant
  nlinarith

theorem larger_eigen_first :
    c.upperLeft * c.largerRawWeightZero + c.upperRight * c.largerRawWeightOne =
      c.largerEigenvalue * c.largerRawWeightZero := by
  unfold largerRawWeightZero largerRawWeightOne
  ring

theorem larger_eigen_second (hdisc : 0 ≤ c.discriminant) :
    c.lowerLeft * c.largerRawWeightZero + c.lowerRight * c.largerRawWeightOne =
      c.largerEigenvalue * c.largerRawWeightOne := by
  have h := c.larger_characteristic hdisc
  unfold characteristicAt at h
  unfold largerRawWeightZero largerRawWeightOne
  nlinarith

theorem larger_reconstructed_balance_identities
    (hnegative : c.characteristicAt 1 < 0) :
    c.largerRawWeightOne = c.aZero * c.largerRawWeightTwo +
        c.dZero * c.largerRawWeightThree ∧
      c.largerRawWeightZero = c.aThree * c.largerRawWeightOne +
        c.dThree * c.largerRawWeightTwo := by
  have hspectral := c.eigenvalues_straddle_one_of_characteristic_neg hnegative
  have hbalance := c.balance_identities_of_eigenvector c.largerEigenvalue
    c.largerRawWeightZero c.largerRawWeightOne
    (ne_of_gt (zero_lt_one.trans hspectral.2.2)) c.larger_eigen_first
    (c.larger_eigen_second hspectral.1.le)
  simpa only [largerRawWeightTwo, largerRawWeightThree, largerPeriodSurvival, one_div,
    div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, one_mul] using hbalance

/-- Raw recurrence signs and the two scalar inequalities. No spectral or
weight positivity is supplied as an input. -/
structure LargerBranchTests : Prop where
  aZero_neg : c.aZero < 0
  aOne_pos : 0 < c.aOne
  aTwo_neg : c.aTwo < 0
  aThree_pos : 0 < c.aThree
  dOne_pos : 0 < c.dOne
  dTwo_pos : 0 < c.dTwo
  dThree_pos : 0 < c.dThree
  lowerRight_gt_one : 1 < c.lowerRight
  characteristic_one_neg : c.characteristicAt 1 < 0

theorem larger_weights_positive (tests : c.LargerBranchTests) :
    0 < c.largerPeriodSurvival ∧ c.largerPeriodSurvival < 1 ∧
      0 < c.largerRawWeightZero ∧ 0 < c.largerRawWeightOne ∧
        0 < c.largerRawWeightTwo ∧ 0 < c.largerRawWeightThree := by
  have hD := zero_lt_one.trans tests.lowerRight_gt_one
  have hDzero : 0 < c.aZero * c.aOne + c.dZero := by
    by_contra hnot
    have hnonpositive := mul_nonpos_of_nonpos_of_nonneg
      (le_of_not_gt hnot) tests.dTwo_pos.le
    exact hD.not_ge (by simpa only [lowerRight] using hnonpositive)
  have hL : c.lowerLeft < 0 := by
    unfold lowerLeft
    exact add_neg (mul_neg_of_neg_of_pos tests.aZero_neg tests.dOne_pos)
      (mul_neg_of_pos_of_neg hDzero tests.aTwo_neg)
  have hV : 0 < c.upperRight := by
    unfold upperRight
    exact add_pos (mul_pos tests.aThree_pos hD)
      (mul_pos (mul_pos tests.dThree_pos tests.aOne_pos) tests.dTwo_pos)
  have hU : c.upperLeft < 1 := by
    by_contra hnot
    have hnonnegative := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hnot))
      (sub_nonneg.mpr tests.lowerRight_gt_one.le)
    have hVL := mul_neg_of_pos_of_neg hV hL
    have hnegative := tests.characteristic_one_neg
    unfold characteristicAt at hnegative
    nlinarith
  have hspectral := c.eigenvalues_straddle_one_of_characteristic_neg
    tests.characteristic_one_neg
  have hperiod : 0 < c.largerPeriodSurvival :=
    one_div_pos.mpr (zero_lt_one.trans hspectral.2.2)
  have hperiod_lt : c.largerPeriodSurvival < 1 := by
    simpa only [largerPeriodSurvival, one_div] using
      inv_lt_one_of_one_lt₀ hspectral.2.2
  have hzero : 0 < c.largerRawWeightZero := hV
  have hone : 0 < c.largerRawWeightOne := by
    unfold largerRawWeightOne
    linarith [hspectral.2.2]
  have hbalance := c.larger_reconstructed_balance_identities tests.characteristic_one_neg
  have hterm : c.largerPeriodSurvival * c.aZero * c.dOne * c.largerRawWeightZero < 0 :=
    mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hperiod tests.aZero_neg) tests.dOne_pos)
      hzero
  have hthree : 0 < c.largerRawWeightThree := by
    have hidentity : (c.aZero * c.aOne + c.dZero) * c.largerRawWeightThree =
        c.largerRawWeightOne -
          c.largerPeriodSurvival * c.aZero * c.dOne * c.largerRawWeightZero := by
      rw [hbalance.1]
      unfold largerRawWeightTwo
      ring
    by_contra hnot
    have hnonpositive := mul_nonpos_of_nonneg_of_nonpos hDzero.le (le_of_not_gt hnot)
    rw [hidentity] at hnonpositive
    linarith
  have htwo : 0 < c.largerRawWeightTwo := by
    unfold largerRawWeightTwo
    exact add_pos (mul_pos (mul_pos hperiod tests.dOne_pos) hzero)
      (mul_pos tests.aOne_pos hthree)
  exact ⟨hperiod, hperiod_lt, hzero, hone, htwo, hthree⟩

end Math.SignedFourCycleCoefficients

import MathUE.Polynomial.TensorBernsteinDifferences
import MathUE.Polynomial.MvPolynomialFDeriv
import MathUE.Polynomial.TensorBernsteinGridEstimates
import MathUE.Analysis.PositiveWeightedApproximation
import MathUE.Analysis.CoordinateSecantEstimate

/-! # Quantitative tensor Bernstein derivative estimates -/

noncomputable section

namespace Math

open scoped BigOperators
open Set

variable {dimension : ℕ}

/-- A coordinate finite difference on the common-denominator Bernstein sample grid. -/
def mixedBernsteinFiniteDifference (function : (Fin dimension → ℝ) → ℝ)
    (coordinate : Fin dimension) (order : ℕ)
    (index : BernsteinGridIndex (mixedBernsteinDegree coordinate order)) : ℝ :=
  (order + 1 : ℝ) *
    (function (Function.update (mixedBernsteinSamplePoint coordinate order index) coordinate
      (mixedBernsteinSamplePoint coordinate order index coordinate + 1 / (order + 1 : ℝ))) -
      function (mixedBernsteinSamplePoint coordinate order index))

private theorem bernsteinCoordinateDifference_sample (function : (Fin dimension → ℝ) → ℝ)
    (coordinate : Fin dimension) (order : ℕ)
    (index : BernsteinGridIndex (mixedBernsteinDegree coordinate order)) :
    bernsteinCoordinateDifference coordinate
      (fun input ↦ function (fun axis ↦ (input axis : ℝ) / (order + 1)))
      (fun axis ↦ index axis) =
      function (Function.update (mixedBernsteinSamplePoint coordinate order index) coordinate
        (mixedBernsteinSamplePoint coordinate order index coordinate + 1 / (order + 1 : ℝ))) -
        function (mixedBernsteinSamplePoint coordinate order index) := by
  unfold bernsteinCoordinateDifference
  dsimp only
  congr 2
  funext axis
  by_cases haxis : axis = coordinate
  · subst axis
    simp [mixedBernsteinSamplePoint, add_div]
  · simp [mixedBernsteinSamplePoint, haxis]

/-- Every coordinate of the same polynomial is a positive average of finite differences. -/
theorem fderiv_tensorBernsteinApproximation_apply_single
    (function : (Fin dimension → ℝ) → ℝ) (order : ℕ)
    (point : Fin dimension → ℝ) (coordinate : Fin dimension) :
    fderiv ℝ (fun input ↦ MvPolynomial.eval input
      (tensorBernsteinApproximation (fun _ : Fin dimension ↦ order + 1) function))
      point (Pi.single coordinate 1) =
      ∑ index : BernsteinGridIndex (mixedBernsteinDegree coordinate order),
        tensorBernsteinWeight (mixedBernsteinDegree coordinate order) index point *
          mixedBernsteinFiniteDifference function coordinate order index := by
  rw [fderiv_eval_mvPolynomial_apply_single,
    tensorBernsteinApproximation_eq_coefficientPolynomial]
  have hdegree : (fun _ : Fin dimension ↦ order + 1) =
      Function.update (fun _ : Fin dimension ↦ order + 1) coordinate (order + 1) := by
    simp
  rw [hdegree, eval_pderiv_tensorBernsteinCoefficientPolynomial]
  simp only [Nat.cast_add, Nat.cast_one]
  change (order + 1 : ℝ) *
      (∑ index : BernsteinGridIndex (mixedBernsteinDegree coordinate order),
        bernsteinCoordinateDifference coordinate
          (fun input ↦ function (fun axis ↦ (input axis : ℝ) / (order + 1)))
          (fun axis ↦ index axis) *
          tensorBernsteinWeight (mixedBernsteinDegree coordinate order) index point) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [bernsteinCoordinateDifference_sample]
  unfold mixedBernsteinFiniteDifference
  ring

/-- Actual derivative control on one sample segment controls the corresponding finite difference. -/
theorem abs_mixedBernsteinFiniteDifference_sub_le
    (function : (Fin dimension → ℝ) → ℝ)
    (derivative : (Fin dimension → ℝ) → ((Fin dimension → ℝ) →L[ℝ] ℝ))
    (coordinate : Fin dimension) (order : ℕ)
    (index : BernsteinGridIndex (mixedBernsteinDegree coordinate order))
    (slope errorBound : ℝ)
    (hderivative : ∀ point, (∀ axis, point axis ∈ Icc (0 : ℝ) 1) →
      HasFDerivAt function (derivative point) point)
    (hclose : ∀ value ∈
      Ico (mixedBernsteinSamplePoint coordinate order index coordinate)
        (mixedBernsteinSamplePoint coordinate order index coordinate + 1 / (order + 1 : ℝ)),
      |derivative (Function.update (mixedBernsteinSamplePoint coordinate order index)
        coordinate value) (Pi.single coordinate 1) - slope| ≤ errorBound) :
    |mixedBernsteinFiniteDifference function coordinate order index - slope| ≤ errorBound := by
  have hbound := abs_coordinate_finiteDifference_sub_slope_le_of_hasFDerivAt function derivative
    (mixedBernsteinSamplePoint coordinate order index) coordinate
    (mixedBernsteinSamplePoint coordinate order index coordinate) (1 / (order + 1 : ℝ))
    slope errorBound (by positivity)
    (fun value hvalue ↦ hderivative _
      (update_mixedBernsteinSamplePoint_mem_unitCube coordinate order index value hvalue)) hclose
  simpa only [one_div, inv_inv, Function.update_eq_self,
    mixedBernsteinFiniteDifference] using hbound

/-- Local and global bounds on the actual derivative give a uniform quantitative error bound. -/
theorem abs_fderiv_tensorBernsteinApproximation_sub_le
    (function : (Fin dimension → ℝ) → ℝ)
    (derivative : (Fin dimension → ℝ) → ((Fin dimension → ℝ) →L[ℝ] ℝ))
    (coordinate : Fin dimension) (order : ℕ) (horder : 0 < order)
    (point : Fin dimension → ℝ)
    (hpoint : ∀ axis, point axis ∈ Icc (0 : ℝ) 1)
    (nearBound globalBound radius threshold : ℝ)
    (hnearBound : 0 ≤ nearBound) (hthreshold : 0 < threshold)
    (hmargin : 2 / (order + 1 : ℝ) + threshold ≤ radius)
    (hderivative : ∀ input, (∀ axis, input axis ∈ Icc (0 : ℝ) 1) →
      HasFDerivAt function (derivative input) input)
    (hglobal : ∀ input, (∀ axis, input axis ∈ Icc (0 : ℝ) 1) →
      |derivative input (Pi.single coordinate 1) - derivative point (Pi.single coordinate 1)| ≤
        globalBound)
    (hnear : ∀ input, (∀ axis, input axis ∈ Icc (0 : ℝ) 1) → dist input point < radius →
      |derivative input (Pi.single coordinate 1) - derivative point (Pi.single coordinate 1)| ≤
        nearBound) :
    |fderiv ℝ (fun input ↦ MvPolynomial.eval input
      (tensorBernsteinApproximation (fun _ : Fin dimension ↦ order + 1) function))
        point (Pi.single coordinate 1) - derivative point (Pi.single coordinate 1)| ≤
      nearBound + globalBound * ((dimension : ℝ) / order) / threshold ^ 2 := by
  rw [fderiv_tensorBernsteinApproximation_apply_single]
  apply abs_sum_weight_mul_sub_target_le_of_near_and_sq_moment Finset.univ
    (fun index ↦ tensorBernsteinWeight (mixedBernsteinDegree coordinate order) index point)
    (fun index ↦ dist point (bernsteinGridPoint (mixedBernsteinDegree coordinate order) index))
    (mixedBernsteinFiniteDifference function coordinate order)
    (derivative point (Pi.single coordinate 1)) nearBound globalBound
    ((dimension : ℝ) / order) threshold
  · intro index _
    exact tensorBernsteinWeight_nonneg _ index point hpoint
  · exact sum_tensorBernsteinWeight _ point
  · exact hnearBound
  · exact hthreshold
  · intro index _
    apply abs_mixedBernsteinFiniteDifference_sub_le function derivative coordinate order index
      _ globalBound hderivative
    intro value hvalue
    exact hglobal _ (update_mixedBernsteinSamplePoint_mem_unitCube coordinate order index value
      (Ico_subset_Icc_self hvalue))
  · intro index _ hindex
    apply abs_mixedBernsteinFiniteDifference_sub_le function derivative coordinate order index
      _ nearBound hderivative
    intro value hvalue
    apply hnear _ (update_mixedBernsteinSamplePoint_mem_unitCube coordinate order index value
      (Ico_subset_Icc_self hvalue))
    have hsegment := dist_update_mixedBernsteinSamplePoint_grid_le coordinate order horder index
      value (Ico_subset_Icc_self hvalue)
    have htriangle := dist_triangle
      (Function.update (mixedBernsteinSamplePoint coordinate order index) coordinate value)
      (bernsteinGridPoint (mixedBernsteinDegree coordinate order) index) point
    rw [dist_comm (bernsteinGridPoint _ _) point] at htriangle
    linarith
  · exact sum_mixedBernsteinWeight_mul_dist_sq_le coordinate order horder point hpoint

end Math

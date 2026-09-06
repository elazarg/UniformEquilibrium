import MathUE.Polynomial.TensorBernstein
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Normed.Group.Constructions

/-! # Tensor Bernstein grid moments and mixed-degree sample locations -/

noncomputable section

namespace Math

open scoped BigOperators
open Set

variable {dimension : ℕ}

/-- The ordinary sup-distance squared is bounded by the sum of coordinate squares. -/
theorem dist_sq_le_sum_coordinate_sq (first second : Fin dimension → ℝ) :
    dist first second ^ 2 ≤ ∑ coordinate, (first coordinate - second coordinate) ^ 2 := by
  have hnonneg : 0 ≤ ∑ coordinate, (first coordinate - second coordinate) ^ 2 :=
    Finset.sum_nonneg (fun coordinate _ ↦ sq_nonneg _)
  have hbound : dist first second ≤
      Real.sqrt (∑ coordinate, (first coordinate - second coordinate) ^ 2) := by
    apply (dist_pi_le_iff (Real.sqrt_nonneg _)).mpr
    intro coordinate
    rw [Real.dist_eq]
    apply Real.le_sqrt_of_sq_le
    simpa only [sq_abs] using
      (Finset.single_le_sum (fun axis _ ↦ sq_nonneg (first axis - second axis))
        (Finset.mem_univ coordinate))
  exact (Real.le_sqrt dist_nonneg hnonneg).mp hbound

/-- A uniform lower bound on degrees gives a uniform second moment for the canonical grid. -/
theorem sum_tensorBernsteinWeight_mul_dist_sq_le (degree : Fin dimension → ℕ)
    (point : Fin dimension → ℝ) (hpoint : ∀ axis, point axis ∈ Icc (0 : ℝ) 1)
    (minimumDegree : ℕ) (hminimum : 0 < minimumDegree)
    (hdegree : ∀ axis, minimumDegree ≤ degree axis) :
    ∑ index, tensorBernsteinWeight degree index point *
      dist point (bernsteinGridPoint degree index) ^ 2 ≤
      (dimension : ℝ) / minimumDegree := by
  have hminimumReal : (0 : ℝ) < minimumDegree := by exact_mod_cast hminimum
  calc
    _ ≤ ∑ index : BernsteinGridIndex degree, tensorBernsteinWeight degree index point *
        ∑ axis, (point axis - bernsteinGridPoint degree index axis) ^ 2 := by
      apply Finset.sum_le_sum
      intro index _
      exact mul_le_mul_of_nonneg_left (dist_sq_le_sum_coordinate_sq _ _)
        (tensorBernsteinWeight_nonneg degree index point hpoint)
    _ = ∑ axis, point axis * (1 - point axis) / degree axis := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro axis _
      simpa only [mul_comm] using sum_tensorBernsteinWeight_mul_coordinate_sq degree point axis
        (Nat.ne_zero_of_lt (hminimum.trans_le (hdegree axis))) (hpoint axis)
    _ ≤ ∑ _axis : Fin dimension, (1 : ℝ) / minimumDegree := by
      apply Finset.sum_le_sum
      intro axis _
      have hdegreeReal : (minimumDegree : ℝ) ≤ degree axis := by exact_mod_cast hdegree axis
      have hdegreePos := hminimumReal.trans_le hdegreeReal
      have hvariance : point axis * (1 - point axis) ≤ 1 := by
        nlinarith [(hpoint axis).1, (hpoint axis).2, sq_nonneg (point axis)]
      exact (div_le_div_of_nonneg_right hvariance hdegreePos.le).trans
        (div_le_div_of_nonneg_left zero_le_one hminimumReal hdegreeReal)
    _ = _ := by simp [div_eq_mul_inv]

/-- Differentiate degree `order + 1`: the selected weight degree becomes `order`. -/
def mixedBernsteinDegree (coordinate : Fin dimension) (order : ℕ) : Fin dimension → ℕ :=
  Function.update (fun _ ↦ order + 1) coordinate order

theorem mixedBernsteinDegree_ge (coordinate axis : Fin dimension) (order : ℕ) :
    order ≤ mixedBernsteinDegree coordinate order axis := by
  by_cases haxis : axis = coordinate <;> simp [mixedBernsteinDegree, haxis]

/-- Finite-difference sample nodes retain denominator `order + 1` on every coordinate. -/
def mixedBernsteinSamplePoint (coordinate : Fin dimension) (order : ℕ)
    (index : BernsteinGridIndex (mixedBernsteinDegree coordinate order)) : Fin dimension → ℝ :=
  fun axis ↦ (index axis : ℝ) / (order + 1)

theorem mixedBernsteinSamplePoint_mem_unitCube (coordinate : Fin dimension) (order : ℕ)
    (index : BernsteinGridIndex (mixedBernsteinDegree coordinate order)) (axis : Fin dimension) :
    mixedBernsteinSamplePoint coordinate order index axis ∈ Icc (0 : ℝ) 1 := by
  have hindex : (index axis : ℕ) ≤ order + 1 := by
    have := (index axis).is_le
    by_cases haxis : axis = coordinate <;>
      simp [mixedBernsteinDegree, haxis] at this ⊢ <;> omega
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  · exact (div_le_one (by positivity : (0 : ℝ) < order + 1)).mpr (by exact_mod_cast hindex)

/-- The common-denominator sample node differs from its canonical mixed node by at most one step. -/
theorem dist_mixedBernsteinSamplePoint_grid_le (coordinate : Fin dimension) (order : ℕ)
    (horder : 0 < order)
    (index : BernsteinGridIndex (mixedBernsteinDegree coordinate order)) :
    dist (mixedBernsteinSamplePoint coordinate order index)
      (bernsteinGridPoint (mixedBernsteinDegree coordinate order) index) ≤
      1 / (order + 1 : ℝ) := by
  have horderReal : (0 : ℝ) < order := by exact_mod_cast horder
  have hnext : (0 : ℝ) < order + 1 := by positivity
  apply (dist_pi_le_iff (by positivity)).mpr
  intro axis
  by_cases haxis : axis = coordinate
  · subst axis
    have hindex : (index coordinate : ℝ) ≤ order := by
      exact_mod_cast (show (index coordinate : ℕ) ≤ order by
        simpa [mixedBernsteinDegree] using (index coordinate).is_le)
    have hindexNonneg : (0 : ℝ) ≤ index coordinate := Nat.cast_nonneg _
    simp only [Real.dist_eq, mixedBernsteinSamplePoint, bernsteinGridPoint,
      mixedBernsteinDegree, Function.update_self]
    rw [abs_of_nonpos (sub_nonpos.mpr
      (div_le_div_of_nonneg_left hindexNonneg horderReal (by linarith)))]
    apply (le_div_iff₀ hnext).mpr
    field_simp
    nlinarith
  · simp [mixedBernsteinSamplePoint, bernsteinGridPoint,
      mixedBernsteinDegree, haxis]
    positivity

/-- The whole forward sample segment stays in the unit cube, including both endpoints. -/
theorem update_mixedBernsteinSamplePoint_mem_unitCube (coordinate : Fin dimension) (order : ℕ)
    (index : BernsteinGridIndex (mixedBernsteinDegree coordinate order)) (value : ℝ)
    (hvalue : value ∈ Icc (mixedBernsteinSamplePoint coordinate order index coordinate)
      (mixedBernsteinSamplePoint coordinate order index coordinate + 1 / (order + 1 : ℝ)))
    (axis : Fin dimension) :
    Function.update (mixedBernsteinSamplePoint coordinate order index) coordinate value axis ∈
      Icc (0 : ℝ) 1 := by
  have hnext : (0 : ℝ) < order + 1 := by positivity
  by_cases haxis : axis = coordinate
  · subst axis
    rw [Function.update_self]
    refine ⟨(mixedBernsteinSamplePoint_mem_unitCube coordinate order index coordinate).1.trans
      hvalue.1, hvalue.2.trans ?_⟩
    unfold mixedBernsteinSamplePoint
    rw [← add_div]
    apply (div_le_one hnext).mpr
    have hindex : (index coordinate : ℕ) ≤ order := by
      simpa [mixedBernsteinDegree] using (index coordinate).is_le
    exact_mod_cast Nat.add_le_add_right hindex 1
  · rw [Function.update_of_ne haxis]
    exact mixedBernsteinSamplePoint_mem_unitCube coordinate order index axis

/-- Moving along one sample segment changes the sample point by at most one step. -/
theorem dist_update_mixedBernsteinSamplePoint_le (coordinate : Fin dimension) (order : ℕ)
    (index : BernsteinGridIndex (mixedBernsteinDegree coordinate order)) (value : ℝ)
    (hvalue : value ∈ Icc (mixedBernsteinSamplePoint coordinate order index coordinate)
      (mixedBernsteinSamplePoint coordinate order index coordinate + 1 / (order + 1 : ℝ))) :
    dist (Function.update (mixedBernsteinSamplePoint coordinate order index) coordinate value)
      (mixedBernsteinSamplePoint coordinate order index) ≤ 1 / (order + 1 : ℝ) := by
  apply (dist_pi_le_iff (by positivity)).mpr
  intro axis
  by_cases haxis : axis = coordinate
  · subst axis
    rw [Function.update_self, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hvalue.1)]
    linarith [hvalue.2]
  · simp only [Function.update_of_ne haxis, dist_self]
    positivity

/-- A sample segment is within two steps of its canonical mixed-degree Bernstein node. -/
theorem dist_update_mixedBernsteinSamplePoint_grid_le (coordinate : Fin dimension) (order : ℕ)
    (horder : 0 < order)
    (index : BernsteinGridIndex (mixedBernsteinDegree coordinate order)) (value : ℝ)
    (hvalue : value ∈ Icc (mixedBernsteinSamplePoint coordinate order index coordinate)
      (mixedBernsteinSamplePoint coordinate order index coordinate + 1 / (order + 1 : ℝ))) :
    dist (Function.update (mixedBernsteinSamplePoint coordinate order index) coordinate value)
      (bernsteinGridPoint (mixedBernsteinDegree coordinate order) index) ≤
        2 / (order + 1 : ℝ) := by
  have htriangle := dist_triangle
    (Function.update (mixedBernsteinSamplePoint coordinate order index) coordinate value)
    (mixedBernsteinSamplePoint coordinate order index)
    (bernsteinGridPoint (mixedBernsteinDegree coordinate order) index)
  have hfirst := dist_update_mixedBernsteinSamplePoint_le coordinate order index value hvalue
  have hsecond := dist_mixedBernsteinSamplePoint_grid_le coordinate order horder index
  convert! htriangle.trans (add_le_add hfirst hsecond) using 1
  ring

/-- The mixed-degree weights have canonical-node second moment at most `dimension / order`. -/
theorem sum_mixedBernsteinWeight_mul_dist_sq_le (coordinate : Fin dimension) (order : ℕ)
    (horder : 0 < order) (point : Fin dimension → ℝ)
    (hpoint : ∀ axis, point axis ∈ Icc (0 : ℝ) 1) :
    ∑ index, tensorBernsteinWeight (mixedBernsteinDegree coordinate order) index point *
      dist point (bernsteinGridPoint (mixedBernsteinDegree coordinate order) index) ^ 2 ≤
      (dimension : ℝ) / order :=
  sum_tensorBernsteinWeight_mul_dist_sq_le _ point hpoint order horder
    (fun axis ↦ mixedBernsteinDegree_ge coordinate axis order)

end Math


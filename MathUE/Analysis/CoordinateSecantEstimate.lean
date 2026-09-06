import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pi

/-! # Coordinate secant estimates from actual derivative bounds -/

noncomputable section

namespace Math

open Set

/-- Derivative closeness to a slope controls the affine-corrected endpoint difference. -/
theorem abs_sub_sub_slope_mul_le_of_hasDerivWithinAt
    (function derivative : ℝ → ℝ) (left right slope errorBound : ℝ)
    (hendpoints : left ≤ right)
    (hderivative : ∀ value ∈ Icc left right,
      HasDerivWithinAt function (derivative value) (Icc left right) value)
    (hclose : ∀ value ∈ Ico left right, |derivative value - slope| ≤ errorBound) :
    |function right - function left - slope * (right - left)| ≤
      errorBound * (right - left) := by
  have hcorrected (value : ℝ) (hvalue : value ∈ Icc left right) :
      HasDerivWithinAt (fun input ↦ function input - slope * input)
        (derivative value - slope) (Icc left right) value := by
    simpa using! (hderivative value hvalue).sub
      (((hasDerivAt_id value).const_mul slope).hasDerivWithinAt)
  have hbound := norm_image_sub_le_of_norm_deriv_le_segment' hcorrected
    (fun value hvalue ↦ by simpa only [Real.norm_eq_abs] using hclose value hvalue)
    right (right_mem_Icc.mpr hendpoints)
  convert hbound using 1
  simp only [Real.norm_eq_abs]
  congr 1
  ring

/-- On a positive-length interval, derivative closeness controls its secant slope. -/
theorem abs_secant_sub_slope_le_of_hasDerivWithinAt
    (function derivative : ℝ → ℝ) (left right slope errorBound : ℝ)
    (hendpoints : left < right)
    (hderivative : ∀ value ∈ Icc left right,
      HasDerivWithinAt function (derivative value) (Icc left right) value)
    (hclose : ∀ value ∈ Ico left right, |derivative value - slope| ≤ errorBound) :
    |(function right - function left) / (right - left) - slope| ≤ errorBound := by
  have hlength : 0 < right - left := sub_pos.mpr hendpoints
  have hbound := abs_sub_sub_slope_mul_le_of_hasDerivWithinAt function derivative left right
    slope errorBound hendpoints.le hderivative hclose
  calc
    _ = |(function right - function left - slope * (right - left)) / (right - left)| := by
      congr 1
      field_simp
    _ = |function right - function left - slope * (right - left)| / (right - left) := by
      rw [abs_div, abs_of_pos hlength]
    _ ≤ _ := (div_le_iff₀ hlength).mpr hbound

/-- Ambient derivative control along the literal coordinate segment bounds its secant slope. -/
theorem abs_coordinate_secant_sub_slope_le_of_hasFDerivAt {dimension : ℕ}
    (function : (Fin dimension → ℝ) → ℝ)
    (derivative : (Fin dimension → ℝ) → ((Fin dimension → ℝ) →L[ℝ] ℝ))
    (point : Fin dimension → ℝ) (coordinate : Fin dimension)
    (left right slope errorBound : ℝ) (hendpoints : left < right)
    (hderivative : ∀ value ∈ Icc left right,
      HasFDerivAt function (derivative (Function.update point coordinate value))
        (Function.update point coordinate value))
    (hclose : ∀ value ∈ Ico left right,
      |derivative (Function.update point coordinate value) (Pi.single coordinate 1) - slope| ≤
        errorBound) :
    |(function (Function.update point coordinate right) -
      function (Function.update point coordinate left)) / (right - left) - slope| ≤ errorBound := by
  apply abs_secant_sub_slope_le_of_hasDerivWithinAt
    (fun value ↦ function (Function.update point coordinate value))
    (fun value ↦ derivative (Function.update point coordinate value) (Pi.single coordinate 1))
    left right slope errorBound hendpoints
  · intro value hvalue
    exact ((hderivative value hvalue).comp_hasDerivAt value
      (hasDerivAt_update point coordinate value)).hasDerivWithinAt
  · exact hclose

/-- Positive-step finite differences are controlled by the actual derivatives on that segment. -/
theorem abs_coordinate_finiteDifference_sub_slope_le_of_hasFDerivAt {dimension : ℕ}
    (function : (Fin dimension → ℝ) → ℝ)
    (derivative : (Fin dimension → ℝ) → ((Fin dimension → ℝ) →L[ℝ] ℝ))
    (point : Fin dimension → ℝ) (coordinate : Fin dimension)
    (left step slope errorBound : ℝ) (hstep : 0 < step)
    (hderivative : ∀ value ∈ Icc left (left + step),
      HasFDerivAt function (derivative (Function.update point coordinate value))
        (Function.update point coordinate value))
    (hclose : ∀ value ∈ Ico left (left + step),
      |derivative (Function.update point coordinate value) (Pi.single coordinate 1) - slope| ≤
        errorBound) :
    |step⁻¹ * (function (Function.update point coordinate (left + step)) -
      function (Function.update point coordinate left)) - slope| ≤ errorBound := by
  simpa only [add_sub_cancel_left, div_eq_mul_inv, mul_comm] using
    abs_coordinate_secant_sub_slope_le_of_hasFDerivAt function derivative point coordinate
      left (left + step) slope errorBound (lt_add_of_pos_right left hstep) hderivative hclose

end Math


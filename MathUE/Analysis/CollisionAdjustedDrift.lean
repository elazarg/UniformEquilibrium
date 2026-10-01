import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # The difference quotient of a collision-adjusted affine probe -/

noncomputable section

namespace Math

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The fixed correction cancels from the derivative. Differentiability is
required only at the queried point. -/
theorem hasDerivAt_collisionAdjusted_potential_difference
    (potential : E → ℝ) (derivative : E →L[ℝ] ℝ) (point correction reward : E)
    (hdiff : HasFDerivAt potential derivative point) :
    HasDerivAt (fun rate : ℝ =>
      potential (point + (rate / (1 - rate)) • correction) -
        potential (point + rate • (correction + reward - point)))
      (derivative (point - reward)) 0 := by
  have hrate : HasDerivAt (fun rate : ℝ => rate / (1 - rate)) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).fun_div
      ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id (0 : ℝ)))
      (by norm_num)
  have hsource : HasDerivAt
      (fun rate : ℝ => point + (rate / (1 - rate)) • correction) correction 0 := by
    have hscaled : HasDerivAt
        (fun rate : ℝ => (rate / (1 - rate)) • correction) correction 0 :=
      (hrate.smul_const correction).congr_deriv (one_smul ℝ correction)
    exact hscaled.const_add point
  have htarget : HasDerivAt
      (fun rate : ℝ => point + rate • (correction + reward - point))
      (correction + reward - point) 0 := by
    have hscaled : HasDerivAt
        (fun rate : ℝ => rate • (correction + reward - point))
        (correction + reward - point) 0 :=
      ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const (correction + reward - point)).congr_deriv
        (one_smul ℝ (correction + reward - point))
    exact hscaled.const_add point
  have hfirst : HasDerivAt
      (fun rate : ℝ => potential (point + (rate / (1 - rate)) • correction))
      (derivative correction) 0 := by
    apply (hdiff.comp_hasDerivAt_of_eq 0 hsource (by simp)).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun _ => rfl
  have hsecond : HasDerivAt
      (fun rate : ℝ => potential (point + rate • (correction + reward - point)))
      (derivative (correction + reward - point)) 0 := by
    apply (hdiff.comp_hasDerivAt_of_eq 0 htarget (by simp)).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun _ => rfl
  have hderivative : derivative correction - derivative (correction + reward - point) =
      derivative (point - reward) := by
    simp only [map_sub, map_add]
    ring
  apply ((hfirst.fun_sub (𝕜 := ℝ) hsecond).congr_deriv hderivative).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun _ => rfl

/-- A right-hand quotient limit for the literal source and affine successor.
No derivative continuity or interior-point assumption is used. -/
theorem tendsto_collisionAdjusted_potential_differenceQuotient
    (potential : E → ℝ) (derivative : E →L[ℝ] ℝ) (point correction reward : E)
    (hdiff : HasFDerivAt potential derivative point) :
    Tendsto (fun rate : ℝ =>
      (potential (point + (rate / (1 - rate)) • correction) -
        potential (point + rate • (correction + reward - point))) / rate)
      (𝓝[>] 0) (𝓝 (derivative (point - reward))) := by
  simpa [div_eq_mul_inv, mul_comm] using
    (hasDerivAt_collisionAdjusted_potential_difference
      potential derivative point correction reward hdiff).tendsto_slope_zero_right

end Math

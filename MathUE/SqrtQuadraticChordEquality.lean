import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Strict equality in a square-root quadratic chord -/

noncomputable section

namespace Math

/-- With positive constant and scale, equality in the endpoint chord bound
can occur only at an endpoint of the unit interval. -/
theorem sqrt_quadratic_chord_eq_imp_endpoint
    {constant scale weight : ℝ}
    (hconstant : 0 < constant) (hscale : 0 < scale)
    (hweight : weight ∈ Set.Icc (0 : ℝ) 1)
    (heq : Real.sqrt (constant + scale * weight ^ 2) =
      weight * Real.sqrt (constant + scale) +
        (1 - weight) * Real.sqrt constant) :
    weight = 0 ∨ weight = 1 := by
  by_contra hendpoint
  push Not at hendpoint
  have hweightPos : 0 < weight := lt_of_le_of_ne hweight.1 (Ne.symm hendpoint.1)
  have hweightLt : weight < 1 := lt_of_le_of_ne hweight.2 hendpoint.2
  let upper := Real.sqrt (constant + scale)
  let lower := Real.sqrt constant
  have hconstantNonneg : 0 ≤ constant := hconstant.le
  have hsumNonneg : 0 ≤ constant + scale := by positivity
  have hlowerSq : lower ^ 2 = constant := Real.sq_sqrt hconstantNonneg
  have hupperSq : upper ^ 2 = constant + scale := Real.sq_sqrt hsumNonneg
  have hupperGt : lower < upper := by
    dsimp only [lower, upper]
    exact Real.sqrt_lt_sqrt hconstantNonneg (by linarith)
  have hlowerPos : 0 < lower := Real.sqrt_pos.2 hconstant
  have hcross : constant < upper * lower := by
    calc
      constant = lower * lower := by nlinarith [hlowerSq]
      _ < upper * lower := mul_lt_mul_of_pos_right hupperGt hlowerPos
  have hradicand : 0 ≤ constant + scale * weight ^ 2 := by positivity
  have hsquare := congrArg (fun value : ℝ => value ^ 2) heq
  rw [Real.sq_sqrt hradicand] at hsquare
  change constant + scale * weight ^ 2 =
    (weight * upper + (1 - weight) * lower) ^ 2 at hsquare
  have hcoefficient : 0 < weight * (1 - weight) :=
    mul_pos hweightPos (sub_pos.mpr hweightLt)
  nlinarith

end Math

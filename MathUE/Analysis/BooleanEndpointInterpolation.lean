import MathUE.Analysis.CoordinateAffineBoxMinimum
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Algebraic interpolation of Boolean endpoint data

The Boolean tensor formula is defined for every real coordinate weight, including
weights outside the unit interval. It constructs no probability distribution.
All statements retain the empty finite index type.
-/

noncomputable section

namespace Math

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The real zero-one point associated with a Boolean vertex. -/
def booleanEndpoint (vertex : ι → Bool) : ι → ℝ :=
  fun coordinate => if vertex coordinate then 1 else 0

/-- The algebraic tensor weight of a Boolean vertex at arbitrary real weights. -/
def booleanEndpointWeight (vertex : ι → Bool) (weights : ι → ℝ) : ℝ :=
  ∏ coordinate, if vertex coordinate then weights coordinate else 1 - weights coordinate

/-- Interpolation of arbitrary Boolean endpoint coefficients by an actual finite sum. -/
def booleanEndpointInterpolant (coefficient : (ι → Bool) → ℝ) (weights : ι → ℝ) : ℝ := by
  classical
  exact ∑ vertex, coefficient vertex * booleanEndpointWeight vertex weights

/-- At an endpoint, exactly its own Boolean tensor weight is one. -/
theorem booleanEndpointWeight_at_endpoint (vertex endpoint : ι → Bool) :
    booleanEndpointWeight vertex (booleanEndpoint endpoint) =
      if vertex = endpoint then 1 else 0 := by
  classical
  by_cases heq : vertex = endpoint
  · subst vertex
    rw [booleanEndpointWeight, ite_eq_left (rfl : endpoint = endpoint)]
    apply Finset.prod_eq_one
    intro coordinate _
    cases hendpoint : endpoint coordinate <;> simp [booleanEndpoint, hendpoint]
  · rw [ite_eq_right heq]
    obtain ⟨coordinate, hcoordinate⟩ : ∃ coordinate, vertex coordinate ≠ endpoint coordinate := by
      by_contra h
      exact heq (funext (by simpa using h))
    apply Finset.prod_eq_zero (Finset.mem_univ coordinate)
    cases hvertex : vertex coordinate <;> cases hendpoint : endpoint coordinate <;>
      simp_all [booleanEndpoint]

/-- The actual interpolant recovers every supplied endpoint coefficient. -/
theorem booleanEndpointInterpolant_at_endpoint (coefficient : (ι → Bool) → ℝ)
    (endpoint : ι → Bool) :
    booleanEndpointInterpolant coefficient (booleanEndpoint endpoint) = coefficient endpoint := by
  classical
  simp [booleanEndpointInterpolant, booleanEndpointWeight_at_endpoint]

section CoordinateLines

variable [DecidableEq ι]

private theorem booleanEndpointWeight_update (vertex : ι → Bool) (weights : ι → ℝ)
    (coordinate : ι) (value : ℝ) :
    booleanEndpointWeight vertex (Function.update weights coordinate value) =
      (if vertex coordinate then value else 1 - value) *
        ∏ axis ∈ Finset.univ.erase coordinate,
          if vertex axis then weights axis else 1 - weights axis := by
  unfold booleanEndpointWeight
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ coordinate)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro axis haxis
  rw [Function.update_of_ne (Finset.ne_of_mem_erase haxis)]

/-- Every coordinate line has the exact zero-one interpolation formula for all real values. -/
theorem booleanEndpointInterpolant_update (coefficient : (ι → Bool) → ℝ)
    (weights : ι → ℝ) (coordinate : ι) (value : ℝ) :
    booleanEndpointInterpolant coefficient (Function.update weights coordinate value) =
      (1 - value) * booleanEndpointInterpolant coefficient (Function.update weights coordinate 0) +
        value * booleanEndpointInterpolant coefficient (Function.update weights coordinate 1) := by
  classical
  have hterm (vertex : ι → Bool) :
      coefficient vertex *
          booleanEndpointWeight vertex (Function.update weights coordinate value) =
        (1 - value) * (coefficient vertex *
          booleanEndpointWeight vertex (Function.update weights coordinate 0)) +
        value * (coefficient vertex *
          booleanEndpointWeight vertex (Function.update weights coordinate 1)) := by
    rw [booleanEndpointWeight_update, booleanEndpointWeight_update, booleanEndpointWeight_update]
    cases vertex coordinate <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> ring
  unfold booleanEndpointInterpolant
  calc
    _ = ∑ vertex, ((1 - value) * (coefficient vertex *
        booleanEndpointWeight vertex (Function.update weights coordinate 0)) +
        value * (coefficient vertex *
          booleanEndpointWeight vertex (Function.update weights coordinate 1))) := by
      exact Finset.sum_congr (by ext vertex; simp) (fun vertex _ => hterm vertex)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      apply congrArg₂ (fun first second : ℝ => first + second)
      · exact Finset.sum_congr (by ext vertex; simp) (fun _ _ => rfl)
      · exact Finset.sum_congr (by ext vertex; simp) (fun _ _ => rfl)

/-- Boolean endpoint interpolation is coordinate-affine on the entire real space. -/
theorem isCoordinateAffine_booleanEndpointInterpolant (coefficient : (ι → Bool) → ℝ) :
    IsCoordinateAffine (booleanEndpointInterpolant coefficient) := by
  intro weights coordinate
  refine ⟨booleanEndpointInterpolant coefficient (Function.update weights coordinate 0),
    booleanEndpointInterpolant coefficient (Function.update weights coordinate 1) -
      booleanEndpointInterpolant coefficient (Function.update weights coordinate 0), ?_⟩
  intro value
  rw [booleanEndpointInterpolant_update]
  ring

end CoordinateLines

end Math

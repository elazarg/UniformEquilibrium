/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib

/-!
# Scale-direction blow-up of a finite hazard cone

A nonzero nonnegative hazard vector is resolved into total scale

`λ = ∑ i, x i`

and simplex direction `θ i = x i / λ`.  This file proves normalization,
exact reconstruction, invariance of direction under positive rescaling, and
injectivity of the resolved coordinates away from the zero-hazard apex.

The chart is the elementary real-oriented blow-up of the positive cone at
zero.  It remembers first-order approach direction.  It does not remember
hierarchical orders such as `(ε, ε²)` after the first direction reaches a
simplex face; those require an iterated blow-up of that face.
-/


noncomputable section

namespace GameTheory

variable {ι : Type*} [Fintype ι]

/-- Total hazard scale. -/
def hazardScale (x : ι → ℝ) : ℝ := ∑ i, x i

/-- Projective direction of a hazard vector.  It is meaningful when its scale
is nonzero. -/
def hazardDirection (x : ι → ℝ) (i : ι) : ℝ :=
  x i / hazardScale x

/-- A nonnegative hazard vector has a nonnegative resolved direction. -/
theorem hazardDirection_nonneg
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (i : ι) :
    0 ≤ hazardDirection x i := by
  unfold hazardDirection
  exact div_nonneg (hx i) (Finset.sum_nonneg fun j _ ↦ hx j)

/-- Away from zero scale, the direction lies on the unit simplex. -/
theorem sum_hazardDirection
    (x : ι → ℝ) (hscale : hazardScale x ≠ 0) :
    ∑ i, hazardDirection x i = 1 := by
  simp only [hazardDirection, ← Finset.sum_div, hazardScale]
  exact div_self hscale

/-- Scale and direction reconstruct every coordinate exactly. -/
theorem hazardScale_mul_hazardDirection
    (x : ι → ℝ) (hscale : hazardScale x ≠ 0) (i : ι) :
    hazardScale x * hazardDirection x i = x i := by
  unfold hazardDirection
  exact mul_div_cancel₀ (x i) hscale

/-- Total scale is homogeneous. -/
theorem hazardScale_smul (c : ℝ) (x : ι → ℝ) :
    hazardScale (fun i ↦ c * x i) = c * hazardScale x := by
  simp [hazardScale, Finset.mul_sum]

/-- Positive (indeed nonzero) radial rescaling leaves direction unchanged. -/
theorem hazardDirection_smul
    (c : ℝ) (hc : c ≠ 0) (x : ι → ℝ)
    (hscale : hazardScale x ≠ 0) (i : ι) :
    hazardDirection (fun j ↦ c * x j) i = hazardDirection x i := by
  rw [hazardDirection, hazardDirection, hazardScale_smul]
  field_simp

/-- A supplied scale and unit-sum direction return the supplied scale. -/
theorem hazardScale_of_scale_direction
    (scale : ℝ) (direction : ι → ℝ)
    (hdirection : ∑ i, direction i = 1) :
    hazardScale (fun i ↦ scale * direction i) = scale := by
  rw [hazardScale_smul]
  change scale * (∑ i, direction i) = scale
  rw [hdirection, mul_one]

/-- A nonzero supplied scale and unit-sum direction return the supplied
direction after normalization. -/
theorem hazardDirection_of_scale_direction
    (scale : ℝ) (hscale : scale ≠ 0) (direction : ι → ℝ)
    (hdirection : ∑ i, direction i = 1) (i : ι) :
    hazardDirection (fun j ↦ scale * direction j) i = direction i := by
  unfold hazardDirection
  rw [hazardScale_of_scale_direction scale direction hdirection]
  exact mul_div_cancel_left₀ (direction i) hscale

/-- The scale-direction chart is injective away from its zero-scale apex. -/
theorem eq_of_hazardScale_eq_of_hazardDirection_eq
    {x y : ι → ℝ} (hx : hazardScale x ≠ 0)
    (hy : hazardScale y ≠ 0)
    (hscale : hazardScale x = hazardScale y)
    (hdirection : hazardDirection x = hazardDirection y) :
    x = y := by
  funext i
  have hxrec := hazardScale_mul_hazardDirection x hx i
  have hyrec := hazardScale_mul_hazardDirection y hy i
  rw [hscale, hdirection] at hxrec
  exact hxrec.symm.trans hyrec


end GameTheory

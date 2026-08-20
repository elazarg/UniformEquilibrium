/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Repair.CertifiedBoundaryPolyhedron

/-!
# The max-affine holonomy semigroup

Finite quitting blocks act on a terminal best-response value by

`w ↦ max early (tail + survival * w)`.

Nonnegative slopes make this class closed under composition.  This file
packages the coefficient law as an associative semigroup (without identity:
an exact identity would need the extended-real floor `-∞`) and proves that
evaluation turns coefficient composition into function composition.
-/


noncomputable section

namespace GameTheory

/-- Coefficients of a max-affine boundary map with nonnegative slope. -/
@[ext] structure MaxAffineSummary where
  early : ℝ
  tail : ℝ
  survival : NNReal
deriving DecidableEq

namespace MaxAffineSummary

/-- Evaluate a max-affine summary on a supplied terminal value. -/
def eval (summary : MaxAffineSummary) (w : ℝ) : ℝ :=
  max summary.early (summary.tail + summary.survival * w)

/-- Chronological composition: `outer.compose inner` first passes the
terminal value through `inner`, then through `outer`. -/
def compose (outer inner : MaxAffineSummary) : MaxAffineSummary where
  early := max outer.early
    (outer.tail + outer.survival * inner.early)
  tail := outer.tail + outer.survival * inner.tail
  survival := outer.survival * inner.survival

/-- Coefficient composition represents literal function composition. -/
theorem eval_compose (outer inner : MaxAffineSummary) (w : ℝ) :
    (outer.compose inner).eval w = outer.eval (inner.eval w) := by
  change quittingBoundaryBestResponse
      (max outer.early (outer.tail + outer.survival * inner.early))
      (outer.tail + outer.survival * inner.tail)
      (↑(outer.survival * inner.survival) : ℝ) w =
    quittingBoundaryBestResponse outer.early outer.tail outer.survival
      (quittingBoundaryBestResponse inner.early inner.tail
        inner.survival w)
  rw [NNReal.coe_mul]
  exact (quittingBoundaryBestResponse_compose
      outer.early outer.tail outer.survival
      inner.early inner.tail inner.survival w
      outer.survival.coe_nonneg).symm

/-- Max-affine coefficient composition is associative. -/
theorem compose_assoc (first second third : MaxAffineSummary) :
    (first.compose second).compose third =
      first.compose (second.compose third) := by
  ext
  · simp only [compose]
    have hdistrib :
        first.tail + (first.survival : ℝ) *
            max second.early
              (second.tail + (second.survival : ℝ) * third.early) =
          max (first.tail + (first.survival : ℝ) * second.early)
            (first.tail + (first.survival : ℝ) *
              (second.tail + (second.survival : ℝ) * third.early)) := by
      rcases le_total second.early
          (second.tail + (second.survival : ℝ) * third.early) with h | h
      · rw [max_eq_right h, max_eq_right]
        nlinarith [first.survival.coe_nonneg]
      · rw [max_eq_left h, max_eq_left]
        nlinarith [first.survival.coe_nonneg]
    rw [hdistrib, max_assoc]
    congr 2
    push_cast
    ring
  · simp only [compose]
    push_cast
    ring
  · simp [compose, mul_assoc]

/-- Bundled semigroup structure for block holonomies. -/
instance : Semigroup MaxAffineSummary where
  mul := compose
  mul_assoc := compose_assoc

@[simp] theorem mul_eq_compose (outer inner : MaxAffineSummary) :
    outer * inner = outer.compose inner := rfl

@[simp] theorem eval_mul (outer inner : MaxAffineSummary) (w : ℝ) :
    (outer * inner).eval w = outer.eval (inner.eval w) :=
  eval_compose outer inner w

/-- No finite real early floor can represent the identity function on all
terminal values.  A literal identity therefore requires adjoining `-∞`. -/
theorem not_exists_eval_eq_id :
    ¬ ∃ identity : MaxAffineSummary, ∀ w, identity.eval w = w := by
  rintro ⟨identity, hidentity⟩
  have hlower := le_max_left identity.early
    (identity.tail + identity.survival * (identity.early - 1))
  rw [← eval, hidentity (identity.early - 1)] at hlower
  linarith


end MaxAffineSummary

end GameTheory

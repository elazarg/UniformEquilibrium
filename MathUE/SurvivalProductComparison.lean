/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.SurvivalProduct

/-!
# Comparing two survival products over the same window

`Math.survivalProduct` is the canonical name for the finite product of a
per-stage continue coefficient over a window; see the module docstring of
`Math.SurvivalProduct` for the census of names bridging into it.  This file
adds the two comparison principles that a prefix-truncation argument needs,
both stated once for the canonical name rather than separately for each
bridged sibling.

* `survivalProduct_congr`: a survival product reads only the coefficients
  inside its own window, so two coefficient sequences agreeing there give the
  same product.  This is the "agreement on a prefix" core.
* `survivalProduct_le_survivalProduct`: a survival product is monotone in its
  coefficient sequence, given nonnegativity of the smaller one; and its
  specialization `survivalProduct_mul_le`, in which one sequence carries an
  extra per-stage factor in `[0, 1]`.  A survival clock that additionally
  tracks one more source of absorption therefore runs no slower to zero than
  one that ignores it.

Everything here is deterministic algebra on real sequences.  No coefficient
is required to be a probability, and nothing here interprets a product as a
survival event, a payoff, or an equilibrium object.
-/

namespace Math

/-- A survival product reads only the coefficients inside its own window. -/
theorem survivalProduct_congr (C D : ℕ → ℝ) (start fuel : ℕ)
    (hwindow : ∀ offset, offset < fuel → C (start + offset) = D (start + offset)) :
    survivalProduct C start fuel = survivalProduct D start fuel :=
  Finset.prod_congr rfl fun offset hoffset =>
    hwindow offset (Finset.mem_range.mp hoffset)

/-- A survival product is monotone in its per-stage coefficient, provided the
dominated sequence is nonnegative. -/
theorem survivalProduct_le_survivalProduct (C D : ℕ → ℝ)
    (hC : ∀ time, 0 ≤ C time) (hCD : ∀ time, C time ≤ D time)
    (start fuel : ℕ) :
    survivalProduct C start fuel ≤ survivalProduct D start fuel :=
  Finset.prod_le_prod (fun offset _ => hC (start + offset))
    (fun offset _ => hCD (start + offset))

/-- Attaching an extra per-stage factor in `[0, 1]` can only shrink a survival
product.  This is the shape taken by a joint clock compared against the clock
that deletes one of its sources of absorption. -/
theorem survivalProduct_mul_le (C weight : ℕ → ℝ)
    (hC : ∀ time, 0 ≤ C time)
    (hweight0 : ∀ time, 0 ≤ weight time) (hweight1 : ∀ time, weight time ≤ 1)
    (start fuel : ℕ) :
    survivalProduct (fun time => C time * weight time) start fuel ≤
      survivalProduct C start fuel :=
  survivalProduct_le_survivalProduct _ _
    (fun time => mul_nonneg (hC time) (hweight0 time))
    (fun time => mul_le_of_le_one_right (hC time) (hweight1 time)) start fuel

end Math

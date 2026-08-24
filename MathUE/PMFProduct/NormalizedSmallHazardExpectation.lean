/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import MathUE.PMFProduct.SmallHazardExpectation

/-!
# Normalized first-order estimates for small product hazards

The quadratic product-law remainders become linear errors after division by
the positive total hazard.  These forms are convenient for compact
small-hazard arguments whose normalized direction is `x / sum x`.
-/

namespace Math.PMFProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Normalized absorption probability differs from one by at most half the
total hazard. -/
theorem abs_one_sub_continueMass_div_sum_sub_one_le
    (x : ι → ℝ) (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1)
    (hsum : 0 < ∑ i, x i) :
    |(1 - continueMass x) / (∑ i, x i) - 1| ≤
      (∑ i, x i) / 2 := by
  let total := ∑ i, x i
  change |(1 - continueMass x) / total - 1| ≤ total / 2
  have hbounds := continueMass_firstOrder_bounds x h0 h1
  change 0 ≤ continueMass x - (1 - total) ∧
    continueMass x - (1 - total) ≤ total ^ 2 / 2 at hbounds
  have htotalNe : total ≠ 0 := ne_of_gt hsum
  have hidentity :
      (1 - continueMass x) / total - 1 =
        -(continueMass x - (1 - total)) / total := by
    field_simp [htotalNe]
    ring
  rw [hidentity, abs_div, abs_neg,
    abs_of_nonneg hbounds.1, abs_of_pos hsum]
  apply (div_le_iff₀ hsum).2
  calc
    continueMass x - (1 - total) ≤ total ^ 2 / 2 := hbounds.2
    _ = (total / 2) * total := by ring

/-- A bounded small-hazard expectation, divided by total hazard, differs
from its normalized singleton linearization by at most a linear error. -/
theorem abs_smallHazardExpectation_div_sum_sub_normalizedSingleton_le
    (terminal : Finset ι → ℝ) (x : ι → ℝ) {R : ℝ}
    (hR : 0 ≤ R)
    (hterminal : ∀ S, S.Nonempty → |terminal S| ≤ R)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1)
    (hsum : 0 < ∑ i, x i) :
    |smallHazardExpectation terminal 0 x / (∑ i, x i) -
        ∑ i, (x i / (∑ j, x j)) * terminal {i}| ≤
      (3 * R / 2) * (∑ i, x i) := by
  let total := ∑ i, x i
  change |smallHazardExpectation terminal 0 x / total -
      ∑ i, (x i / total) * terminal {i}| ≤ (3 * R / 2) * total
  have htotalNe : total ≠ 0 := ne_of_gt hsum
  have hquad := abs_smallHazardExpectation_sub_tail_sub_linearization_le
    terminal 0 x (K := 0) (R := R) le_rfl hR (by simp) hterminal h0 h1
  have hlinear : smallHazardLinearization terminal 0 x =
      ∑ i, x i * terminal {i} := by
    simp [smallHazardLinearization]
  have hnormalized :
      ∑ i, (x i / total) * terminal {i} =
        (∑ i, x i * terminal {i}) / total := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hidentity :
      smallHazardExpectation terminal 0 x / total -
          ∑ i, (x i / total) * terminal {i} =
        (smallHazardExpectation terminal 0 x -
          smallHazardLinearization terminal 0 x) / total := by
    rw [hnormalized, hlinear]
    ring
  rw [hidentity, abs_div, abs_of_pos hsum]
  apply (div_le_iff₀ hsum).2
  calc
    |smallHazardExpectation terminal 0 x -
        smallHazardLinearization terminal 0 x| ≤
        (3 * R / 2) * total ^ 2 := by
      simpa [total] using hquad
    _ = ((3 * R / 2) * total) * total := by ring

end Math.PMFProduct

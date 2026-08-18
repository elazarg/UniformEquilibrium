/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.LinearProgramming.ColumnSumQ
import MathUE.LinearProgramming.CopositiveQ
import MathUE.LinearProgramming.R0Margin

/-!
# `R₀` for five-cycle circulants with two negative margins

Let `m : ZMod 5 → ℝ` satisfy `m 0 = 0` and put `M = rowCirculant m`, so that
`(M z) i = ∑ j, z j * m (j - i)`.  Call `m` a *pocket* margin vector when

`m 1 < 0`, `m 4 < 0`, `0 ≤ m 2`, `0 ≤ m 3`, `0 < m 1 + m 2 + m 3 + m 4`.

`isR0Matrix_rowCirculant_pentagon_pocket` shows that a pocket circulant is
`R₀`: the homogeneous problem `LCP(M, 0)` has only the zero solution.

The proof is a walk around the cycle.  If some coordinate of a solution is
zero, so is the next one — otherwise the four complementarity equations at the
remaining coordinates hold, and multiplying them in the two available pairings
gives two identities whose sum is `0 = (a strictly positive quantity)`.  A
solution with no zero coordinate makes every residual vanish, and the five
residuals sum to the margin sum times the total weight, which is positive.

`IsStandardQOnPocketCirculants` states, as an unproved proposition, that every
pocket circulant is a textbook `Q`-matrix.  Nothing here proves it: passing
from `R₀` to `Q` on this family uses degree theory for the piecewise-linear
LCP map, which is not developed in this repository.

## Main results

* `isR0Matrix_rowCirculant_pentagon_pocket` — the `R₀` property
* `r0Margin_rowCirculant_pentagon_pocket_pos` — the explicit perturbation
  radius is positive on the pocket
* `exists_pos_isR0Matrix_of_dist_le_rowCirculant_pentagon_pocket` — the pocket
  `R₀` family is entrywise open

## Main definitions

* `IsStandardQOnPocketCirculants` — the unproved standard-`Q` proposition
-/

noncomputable section

namespace Math.LinearProgramming

/-! ## Index arithmetic on the five-cycle -/

/-- Every index of the five-cycle is reached from any other by at most four
unit steps. -/
theorem eq_or_eq_shift_pentagon (i j : ZMod 5) :
    i = j ∨ i = j + 1 ∨ i = j + 2 ∨ i = j + 3 ∨ i = j + 4 := by
  revert i j
  decide

/-! ## The homogeneous residual of a five-cycle circulant -/

variable (m z : ZMod 5 → ℝ)

/-- The homogeneous residual of a five-cycle circulant, read forward from its
own index. -/
theorem lcpResidual_rowCirculant_pentagon (i : ZMod 5) :
    lcpResidual (rowCirculant m) 0 z i =
      m 0 * z i + m 1 * z (i + 1) + m 2 * z (i + 2) + m 3 * z (i + 3) +
        m 4 * z (i + 4) := by
  rw [lcpResidual_zero]
  have hre : (∑ j : ZMod 5, z j * rowCirculant m i j) =
      ∑ k : ZMod 5, z (i + k) * m k := by
    refine (Fintype.sum_equiv (Equiv.addLeft i) _ _ ?_).symm
    intro k
    simp
  have henum : (∑ k : ZMod 5, z (i + k) * m k) =
      z (i + 0) * m 0 + z (i + 1) * m 1 + z (i + 2) * m 2 + z (i + 3) * m 3 +
        z (i + 4) * m 4 :=
    Fin.sum_univ_five (fun k : ZMod 5 => z (i + k) * m k)
  rw [hre, henum, add_zero]
  ring

variable {m z}

/-- Reassociation of a doubly shifted index. -/
theorem add_add_of_add_eq {r t u : ZMod 5} (j : ZMod 5) (h : r + t = u) :
    j + r + t = j + u := by
  rw [add_assoc, h]

theorem lcpResidual_rowCirculant_pentagon_one (j : ZMod 5) :
    lcpResidual (rowCirculant m) 0 z (j + 1) =
      m 0 * z (j + 1) + m 1 * z (j + 2) + m 2 * z (j + 3) + m 3 * z (j + 4) +
        m 4 * z j := by
  rw [lcpResidual_rowCirculant_pentagon,
    add_add_of_add_eq j (show (1 : ZMod 5) + 1 = 2 from by decide),
    add_add_of_add_eq j (show (1 : ZMod 5) + 2 = 3 from by decide),
    add_add_of_add_eq j (show (1 : ZMod 5) + 3 = 4 from by decide),
    add_add_of_add_eq j (show (1 : ZMod 5) + 4 = 0 from by decide), add_zero]

theorem lcpResidual_rowCirculant_pentagon_two (j : ZMod 5) :
    lcpResidual (rowCirculant m) 0 z (j + 2) =
      m 0 * z (j + 2) + m 1 * z (j + 3) + m 2 * z (j + 4) + m 3 * z j +
        m 4 * z (j + 1) := by
  rw [lcpResidual_rowCirculant_pentagon,
    add_add_of_add_eq j (show (2 : ZMod 5) + 1 = 3 from by decide),
    add_add_of_add_eq j (show (2 : ZMod 5) + 2 = 4 from by decide),
    add_add_of_add_eq j (show (2 : ZMod 5) + 3 = 0 from by decide),
    add_add_of_add_eq j (show (2 : ZMod 5) + 4 = 1 from by decide), add_zero]

theorem lcpResidual_rowCirculant_pentagon_three (j : ZMod 5) :
    lcpResidual (rowCirculant m) 0 z (j + 3) =
      m 0 * z (j + 3) + m 1 * z (j + 4) + m 2 * z j + m 3 * z (j + 1) +
        m 4 * z (j + 2) := by
  rw [lcpResidual_rowCirculant_pentagon,
    add_add_of_add_eq j (show (3 : ZMod 5) + 1 = 4 from by decide),
    add_add_of_add_eq j (show (3 : ZMod 5) + 2 = 0 from by decide),
    add_add_of_add_eq j (show (3 : ZMod 5) + 3 = 1 from by decide),
    add_add_of_add_eq j (show (3 : ZMod 5) + 4 = 2 from by decide), add_zero]

theorem lcpResidual_rowCirculant_pentagon_four (j : ZMod 5) :
    lcpResidual (rowCirculant m) 0 z (j + 4) =
      m 0 * z (j + 4) + m 1 * z j + m 2 * z (j + 1) + m 3 * z (j + 2) +
        m 4 * z (j + 3) := by
  rw [lcpResidual_rowCirculant_pentagon,
    add_add_of_add_eq j (show (4 : ZMod 5) + 1 = 0 from by decide),
    add_add_of_add_eq j (show (4 : ZMod 5) + 2 = 1 from by decide),
    add_add_of_add_eq j (show (4 : ZMod 5) + 3 = 2 from by decide),
    add_add_of_add_eq j (show (4 : ZMod 5) + 4 = 3 from by decide), add_zero]

/-! ## The pocket -/

/-- **Pocket circulants of the five-cycle are `R₀`.**  If `m 0 = 0`,
`m 1 < 0`, `m 4 < 0`, `0 ≤ m 2`, `0 ≤ m 3` and the margin sum is positive, then
the only solution of the homogeneous linear complementarity problem of
`rowCirculant m` is the zero vector. -/
theorem isR0Matrix_rowCirculant_pentagon_pocket (hm0 : m 0 = 0)
    (hm1 : m 1 < 0) (hm4 : m 4 < 0) (hm2 : 0 ≤ m 2) (hm3 : 0 ≤ m 3)
    (hsum : 0 < m 1 + m 2 + m 3 + m 4) :
    IsR0Matrix (rowCirculant m) := by
  intro z hsol
  have hznn : ∀ i, 0 ≤ z i := hsol.weight_nonneg
  have hwnn : ∀ i, 0 ≤ lcpResidual (rowCirculant m) 0 z i := hsol.residual_nonneg
  have hres : ∀ i, 0 < z i → lcpResidual (rowCirculant m) 0 z i = 0 := by
    intro i hi
    rcases mul_eq_zero.mp (hsol.complementary i) with h | h
    · exact absurd h (ne_of_gt hi)
    · exact h
  -- one vanishing coordinate forces the next one to vanish
  have hstep : ∀ j : ZMod 5, z j = 0 → z (j + 1) = 0 := by
    intro j hj
    by_contra hne
    have hn1 : 0 < z (j + 1) := lt_of_le_of_ne (hznn _) (Ne.symm hne)
    have hv0 := hwnn j
    have hv1 := hres (j + 1) hn1
    rw [lcpResidual_rowCirculant_pentagon] at hv0
    rw [lcpResidual_rowCirculant_pentagon_one] at hv1
    rw [hm0, hj] at hv0 hv1
    -- `hv1` is the phase-one equation; split on the next coordinate
    rcases eq_or_lt_of_le (hznn (j + 2)) with hn2 | hn2
    · -- the next coordinate vanishes: the phase-three residual is then a
      -- strictly positive multiple of a positive weight
      rw [← hn2] at hv0 hv1
      have hm3n3 : 0 < m 3 * z (j + 3) := by
        have hleft : m 1 * z (j + 1) < 0 := mul_neg_of_neg_of_pos hm1 hn1
        have hright : m 4 * z (j + 4) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hm4.le (hznn (j + 4))
        linarith
      have hn3 : 0 < z (j + 3) := by nlinarith [hznn (j + 3)]
      have hm3pos : 0 < m 3 := by nlinarith [hznn (j + 3)]
      have hm2n3 : 0 ≤ m 2 * z (j + 3) := mul_nonneg hm2 (hznn (j + 3))
      have hm3n4 : 0 ≤ m 3 * z (j + 4) := mul_nonneg hm3 (hznn (j + 4))
      have h34 : m 3 * z (j + 4) = 0 := by linarith
      have hn4 : z (j + 4) = 0 :=
        (mul_eq_zero.mp h34).resolve_left (ne_of_gt hm3pos)
      have hv3 := hres (j + 3) hn3
      rw [lcpResidual_rowCirculant_pentagon_three, hm0, hj, hn4, ← hn2] at hv3
      have hfinal : 0 < m 3 * z (j + 1) := mul_pos hm3pos hn1
      linarith
    · -- every remaining coordinate is positive
      have hv2 := hres (j + 2) hn2
      rw [lcpResidual_rowCirculant_pentagon_two, hm0, hj] at hv2
      have hm2n4 : 0 < m 2 * z (j + 4) := by
        have hleft : 0 ≤ -m 1 * z (j + 3) :=
          mul_nonneg (by linarith) (hznn (j + 3))
        have hright : 0 < -m 4 * z (j + 1) := mul_pos (by linarith) hn1
        linarith
      have hn4 : 0 < z (j + 4) := by nlinarith [hznn (j + 4)]
      have hm2pos : 0 < m 2 := by nlinarith
      have hv4 := hres (j + 4) hn4
      rw [lcpResidual_rowCirculant_pentagon_four, hm0, hj] at hv4
      have hn3 : 0 < z (j + 3) := by
        nlinarith [mul_pos hm2pos hn1, mul_nonneg hm3 (hznn (j + 2)), hznn (j + 3)]
      have hv3 := hres (j + 3) hn3
      rw [lcpResidual_rowCirculant_pentagon_three, hm0, hj] at hv3
      -- the two pairings of the four equations
      have hI : m 1 * m 4 * (z (j + 2) * z (j + 3)) =
          m 2 ^ 2 * (z (j + 1) * z (j + 3)) + m 2 * m 3 * (z (j + 2) * z (j + 3)) +
            m 2 * m 3 * (z (j + 1) * z (j + 4)) +
            m 3 ^ 2 * (z (j + 2) * z (j + 4)) := by
        linear_combination (m 4 * z (j + 3)) * hv1 -
          (m 2 * z (j + 3) + m 3 * z (j + 4)) * hv4
      have hII : m 2 * m 3 * (z (j + 1) * z (j + 4)) =
          m 1 ^ 2 * (z (j + 3) * z (j + 4)) + m 1 * m 4 * (z (j + 2) * z (j + 3)) +
            m 1 * m 4 * (z (j + 1) * z (j + 4)) +
            m 4 ^ 2 * (z (j + 1) * z (j + 2)) := by
        linear_combination (m 3 * z (j + 1)) * hv2 -
          (m 1 * z (j + 3) + m 4 * z (j + 1)) * hv3
      have hm14 : 0 < m 1 * m 4 := mul_pos_of_neg_of_neg hm1 hm4
      have hm1sq : 0 < m 1 ^ 2 := by nlinarith
      have hm4sq : 0 < m 4 ^ 2 := by nlinarith
      have t1 : 0 < m 1 ^ 2 * (z (j + 3) * z (j + 4)) :=
        mul_pos hm1sq (mul_pos hn3 hn4)
      have t2 : 0 < m 1 * m 4 * (z (j + 1) * z (j + 4)) :=
        mul_pos hm14 (mul_pos hn1 hn4)
      have t3 : 0 < m 4 ^ 2 * (z (j + 1) * z (j + 2)) :=
        mul_pos hm4sq (mul_pos hn1 hn2)
      have s1 : 0 ≤ m 2 ^ 2 * (z (j + 1) * z (j + 3)) := by positivity
      have s2 : 0 ≤ m 2 * m 3 * (z (j + 2) * z (j + 3)) := by positivity
      have s3 : 0 ≤ m 3 ^ 2 * (z (j + 2) * z (j + 4)) := by positivity
      linarith
  -- some coordinate vanishes
  have hexists : ∃ j : ZMod 5, z j = 0 := by
    by_contra hall
    simp only [not_exists] at hall
    have hpos : ∀ i, 0 < z i := fun i => lt_of_le_of_ne (hznn i) (Ne.symm (hall i))
    have e0 := hres 0 (hpos 0)
    have e1 := hres (0 + 1) (hpos _)
    have e2 := hres (0 + 2) (hpos _)
    have e3 := hres (0 + 3) (hpos _)
    have e4 := hres (0 + 4) (hpos _)
    rw [lcpResidual_rowCirculant_pentagon, hm0] at e0
    rw [lcpResidual_rowCirculant_pentagon_one, hm0] at e1
    rw [lcpResidual_rowCirculant_pentagon_two, hm0] at e2
    rw [lcpResidual_rowCirculant_pentagon_three, hm0] at e3
    rw [lcpResidual_rowCirculant_pentagon_four, hm0] at e4
    have hkey : (m 1 + m 2 + m 3 + m 4) *
        (z 0 + z (0 + 1) + z (0 + 2) + z (0 + 3) + z (0 + 4)) = 0 := by
      linear_combination e0 + e1 + e2 + e3 + e4
    nlinarith [hpos 0, hpos (0 + 1), hpos (0 + 2), hpos (0 + 3), hpos (0 + 4)]
  obtain ⟨j, hj⟩ := hexists
  have h1 : z (j + 1) = 0 := hstep j hj
  have h2 : z (j + 2) = 0 := by
    have := hstep (j + 1) h1
    rwa [show j + 1 + 1 = j + 2 from by ring] at this
  have h3 : z (j + 3) = 0 := by
    have := hstep (j + 2) h2
    rwa [show j + 2 + 1 = j + 3 from by ring] at this
  have h4 : z (j + 4) = 0 := by
    have := hstep (j + 3) h3
    rwa [show j + 3 + 1 = j + 4 from by ring] at this
  intro i
  rcases eq_or_eq_shift_pentagon i j with h | h | h | h | h <;> rw [h]
  · exact hj
  · exact h1
  · exact h2
  · exact h3
  · exact h4

/-! ## The pocket is entrywise open

`R₀` is an open condition on matrices with the explicit radius
`r0Margin M / (card ι + 1)` of `isR0Matrix_of_r0Margin_lt`, so the pocket family
sits inside an entrywise ball of `R₀` matrices.  Only `R₀` transfers: a
perturbation of a pocket circulant need not be a circulant, need not be
copositive, and standard `Q` for the pocket family itself is not established
here. -/

/-- **Pocket circulants have a positive `R₀` margin.**  This is the numerator of
the explicit perturbation radius `r0Margin M / (card ι + 1)`. -/
theorem r0Margin_rowCirculant_pentagon_pocket_pos (hm0 : m 0 = 0)
    (hm1 : m 1 < 0) (hm4 : m 4 < 0) (hm2 : 0 ≤ m 2) (hm3 : 0 ≤ m 3)
    (hsum : 0 < m 1 + m 2 + m 3 + m 4) :
    0 < r0Margin (rowCirculant m) :=
  (r0Margin_pos_iff_isR0Matrix _).mpr
    (isR0Matrix_rowCirculant_pentagon_pocket hm0 hm1 hm4 hm2 hm3 hsum)

/-- **The pocket `R₀` family is entrywise open.**  Around every pocket circulant
there is an entrywise ball of positive radius consisting of `R₀` matrices; half
of `r0Margin (rowCirculant m) / (card (ZMod 5) + 1)` is such a radius.

The conclusion is `R₀` alone.  A standard-`Q` conclusion for a perturbed matrix
needs copositivity supplied at that matrix, as in
`isStandardQ_of_copositive_of_r0Margin_lt`, or the strictly copositive route of
`isStandardQ_of_copositiveMargin_lt`. -/
theorem exists_pos_isR0Matrix_of_dist_le_rowCirculant_pentagon_pocket
    (hm0 : m 0 = 0) (hm1 : m 1 < 0) (hm4 : m 4 < 0) (hm2 : 0 ≤ m 2)
    (hm3 : 0 ≤ m 3) (hsum : 0 < m 1 + m 2 + m 3 + m 4) :
    ∃ ρ, 0 < ρ ∧ ∀ N : ZMod 5 → ZMod 5 → ℝ,
      (∀ i j, |rowCirculant m i j - N i j| ≤ ρ) → IsR0Matrix N :=
  exists_pos_isR0Matrix_of_dist_le
    (isR0Matrix_rowCirculant_pentagon_pocket hm0 hm1 hm4 hm2 hm3 hsum)

/-! ## The standard-`Q` question -/

/-- The proposition that every pocket circulant of the five-cycle is a textbook
`Q`-matrix.  This is stated, not proved: the known route from `R₀` to `Q` on
this family runs through the degree of the piecewise-linear LCP map, which is
not developed here. -/
def IsStandardQOnPocketCirculants : Prop :=
  ∀ m : ZMod 5 → ℝ, m 0 = 0 → m 1 < 0 → m 4 < 0 → 0 ≤ m 2 → 0 ≤ m 3 →
    0 < m 1 + m 2 + m 3 + m 4 → IsStandardQ (rowCirculant m)

end Math.LinearProgramming

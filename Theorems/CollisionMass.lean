import MathUE.PMFProduct.CollisionMass

/-!
# Collision mass of independent Bernoulli events

Reader-facing statements of the finite Bernoulli collision bound and the
exact positive-support characterization. The canonical proofs remain in
`MathUE.PMFProduct.CollisionMass`.
-/

namespace Theorems.CollisionMass

open Math.PMFProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The probability mass of two or more independent successes is quadratic
in the total absorption probability, with the finite-player pair count as a
uniform coefficient. -/
theorem collisionMass_le_choose_card_mul_absorption_sq
    (x : ι → ℝ) (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) :
    collisionMass x ≤
      (Fintype.card ι).choose 2 * (1 - continueMass x) ^ 2 := by
  exact Math.PMFProduct.collisionMass_le_choose_card_mul_absorption_sq x h0 h1

/-- Collision mass is positive exactly when two distinct coordinates have
positive success probability. -/
theorem collisionMass_pos_iff_exists_two_pos
    (x : ι → ℝ) (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) :
    0 < collisionMass x ↔
      ∃ first second, first ≠ second ∧ 0 < x first ∧ 0 < x second := by
  exact Math.PMFProduct.collisionMass_pos_iff_exists_two_pos x h0 h1

/-- Collision mass vanishes exactly when the positive support has cardinality
at most one. -/
theorem collisionMass_eq_zero_iff_atMostOne_pos
    (x : ι → ℝ) (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) :
    collisionMass x = 0 ↔
      ∀ first second, 0 < x first → 0 < x second → first = second := by
  exact Math.PMFProduct.collisionMass_eq_zero_iff_atMostOne_pos x h0 h1

end Theorems.CollisionMass

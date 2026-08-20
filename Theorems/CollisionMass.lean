import MathUE.PMFProduct.CollisionMass

/-!
# Quadratic collision mass

Reader-facing statement of the finite Bernoulli collision bound. The
canonical proof remains in `MathUE.PMFProduct.CollisionMass`.
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

end Theorems.CollisionMass

/-
Collision pair bounds at one product quitting root.

At a one-date product root each player quits independently, so the event that
at least two players quit together is covered by the union of the pairwise
both-quit events.  That union bound reads the collision mass off as at most
the order-free sum of pairwise quit products, taken over unordered distinct
pairs and written here as the half-weighted off-diagonal sum.

Bounding each pairwise factor by the joint absorption mass turns the pair sum
into the quadratic estimate: collision mass is at most the number of unordered
player pairs times squared absorption.  Combined with the exact split of
absorption into singleton and collision mass, the same estimate caps the
defect between absorption and its singleton part.

The generic Bernoulli mathematics behind these bounds is owned by
`Math.PMFProduct` in `MathUE/PMFProduct/CollisionMass.lean` and by the
Bonferroni pair sum `Math.pairMulSum` in `MathUE/BonferroniProductBounds.lean`,
and it is already specialized to quitting roots in
`UniformEquilibrium/Quitting/AbsorptionPath/CollisionConcentration.lean`.  This
module only restates the finite-dimensional kernel in the shape the surrounding
argument consumes; every proof delegates to the canonical owner.
-/
import UniformEquilibrium.Quitting.AbsorptionPath.CollisionConcentration
import UniformEquilibrium.Quitting.AbsorptionPath.NormalizedFiniteWindowOccupation

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The pair-union bound -/

/-- **Collision is covered by the pairwise both-quit events.**  The one-date
collision mass is at most the sum of pairwise quit products over unordered
distinct pairs, written as the half-weighted sum over ordered distinct pairs.

This is `quittingRootCollisionMass_le_pairMulSum` with the order-free pair sum
`Math.pairMulSum` expanded into its off-diagonal definition. -/
theorem fable_collisionMass_le_sum_pairProducts (root : ι → PMF Bool) :
    quittingRootCollisionMass root ≤
      ∑ pair ∈ Finset.univ.offDiag,
        (root pair.1 true).toReal * (root pair.2 true).toReal / 2 := by
  have hbound := quittingRootCollisionMass_le_pairMulSum root
  have hpair : Math.pairMulSum (quittingRootQuitRates root) Finset.univ =
      ∑ pair ∈ Finset.univ.offDiag,
        (root pair.1 true).toReal * (root pair.2 true).toReal / 2 := by
    unfold Math.pairMulSum quittingRootQuitRates
    rw [Finset.sum_div]
  rwa [hpair] at hbound

/-! ## The quadratic collision estimate -/

/-- **Quadratic collision bound.**  Bounding both factors of every pairwise
quit product by the joint absorption mass leaves the number of unordered player
pairs times squared absorption.

This is `quittingRootCollisionMass_le_choose_card_mul_absorption_sq`, whose own
per-factor step is `quittingQuitProbability_le_absorptionMass`. -/
theorem fable_collisionMass_le_choose_two_mul_absorption_sq
    (root : ι → PMF Bool) :
    quittingRootCollisionMass root ≤
      (Fintype.card ι).choose 2 * quittingRootAbsorptionMass root ^ 2 :=
  quittingRootCollisionMass_le_choose_card_mul_absorption_sq root

/-! ## The singleton defect -/

/-- **Absorption is singleton absorption up to a quadratic defect.**  One-date
absorption splits exactly into the singleton masses and the collision mass, so
the quadratic collision estimate caps the gap between absorption and its
singleton part. -/
theorem fable_absorption_sub_singletonSum_le_choose_two_mul_absorption_sq
    (root : ι → PMF Bool) :
    quittingRootAbsorptionMass root -
        ∑ who, quittingRootCoalitionMass root {who} ≤
      (Fintype.card ι).choose 2 * quittingRootAbsorptionMass root ^ 2 := by
  have hsplit :=
    QuittingFiniteRootWindow.quittingRootAbsorptionMass_eq_sum_singletonMass_add_collisionMass root
  have hcollision := fable_collisionMass_le_choose_two_mul_absorption_sq root
  linarith

end GameTheory

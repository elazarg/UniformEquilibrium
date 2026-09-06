import UniformEquilibrium.Quitting.Projective.RobustChargedRelationPolynomialCapacity
import UniformEquilibrium.Quitting.Projective.RobustChargedRelationPacketAdapter
import UniformEquilibrium.Quitting.Projective.FixedBoxForwardCharacterization

/-! # Polynomial ALL-edge certificates exclude fixed-box forward production and uniform payoffs -/

noncomputable section

namespace GameTheory

open Math.Interval Math.Interval.RationalPolynomial

/-- Finite robust capacity at one positive tolerance rules out the all-tolerance/all-charge
floor-free producer in that same box, through the literal packet-to-path adapter. -/
theorem not_hasFloorFreeAbsorptionWeightedFiniteForwardPackets_of_robustFiniteBudget
    (reward : {coalition : Finset (Fin 4) // coalition.Nonempty} → Payoff (Fin 4))
    (tolerance bound : ℝ) (htolerance : 0 < tolerance)
    (hbudget : (quittingFloorFreeRobustChargedRelation reward tolerance bound).HasFiniteBudget) :
    ¬ HasFloorFreeAbsorptionWeightedFiniteForwardPackets reward bound := by
  intro hpackets
  let relation := quittingFloorFreeRobustChargedRelation reward tolerance bound
  obtain ⟨packet⟩ := hpackets tolerance htolerance (relation.budget + 1)
    (by linarith [relation.budget_nonneg])
  have hpath := relation.chargeSum_le_budget hbudget packet.robustPath
  rw [packet.robustPath_charge_eq] at hpath
  linarith [packet.chargeTarget_le]

/-- A native rational ALL-edge certificate at one positive tolerance excludes weighted packet
production in the identical fixed box, even when the producer retains punishment floors. -/
theorem not_hasAbsorptionWeightedFiniteForwardPackets_of_rationalPotential
    (reward : {coalition : Finset (Fin 4) // coalition.Nonempty} → Payoff (Fin 4))
    (tolerance bound : ℝ) (htolerance : 0 < tolerance)
    (expression : RationalPolynomial 4)
    (hpotential : (quittingFloorFreeRobustChargedRelation reward tolerance bound).IsPotential
      (fun state ↦ evalReal state.1 expression)) :
    ¬ HasAbsorptionWeightedFiniteForwardPackets reward bound := by
  intro hpackets
  exact not_hasFloorFreeAbsorptionWeightedFiniteForwardPackets_of_robustFiniteBudget
    reward tolerance bound htolerance
    (quittingRobustChargedRelation_hasFiniteBudget_of_rationalPotential expression hpotential)
    (hasFloorFreeAbsorptionWeightedFiniteForwardPackets_of_weighted reward bound hpackets)

/-- In the fixed box `rewardBound + 2`, a polynomial certificate and failure of the finite
sure-root alternative rule out every uniform-equilibrium payoff. Deviations remain unrestricted. -/
theorem quittingGame_not_exists_uniformEquilibriumPayoff_of_noSureRoot_of_rationalPotential
    (reward : {coalition : Finset (Fin 4) // coalition.Nonempty} → Payoff (Fin 4))
    (rewardBound : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound)
    (hnormal : ∀ player, IsQuittingNormalPlayer reward player)
    (hpositive : ∃ who, 0 < reward (quittingSingletonTerminal who) who)
    (hnoSureRoot : ¬ HasQuittingPunishmentVectorNashRootWithSureQuitter reward)
    (tolerance : ℝ) (htolerance : 0 < tolerance)
    (expression : RationalPolynomial 4)
    (hpotential :
      (quittingFloorFreeRobustChargedRelation reward tolerance (rewardBound + 2)).IsPotential
        (fun state ↦ evalReal state.1 expression)) :
    ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  intro huniform
  exact not_hasAbsorptionWeightedFiniteForwardPackets_of_rationalPotential reward tolerance
    (rewardBound + 2) htolerance expression hpotential
    (hasFixedBoxPackets_of_uniformEquilibriumPayoff_of_noSureRoot reward rewardBound hreward
      hnormal hpositive huniform hnoSureRoot)

end GameTheory

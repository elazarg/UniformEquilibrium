import UniformEquilibrium.Quitting.Classification.NonnegativeProductLowSmoothDrift
import UniformEquilibrium.Quitting.Projective.RobustChargedRelationSmoothing
import UniformEquilibrium.Quitting.Projective.RobustChargedRelationPacketAdapter

/-! # Fixed-box weighted packets from nonnegative product-low premiums -/

noncomputable section

namespace GameTheory

open Math.Probability Math.ChargedPathBudget

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Finite outer-box robust capacity would supply a smooth potential
forbidden by the lower-boundary geometry. This conclusion allows arbitrary
signed singleton rewards and arbitrary finite nonempty player sets. -/
theorem not_hasFiniteBudget_of_nonnegative_productLow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnonnegative : HasNonnegativeOwnQuittingPremium reward)
    (hlow : HasProductLowQuittingPremium reward)
    (rewardBound tolerance : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound)
    (htolerance : 0 < tolerance) (htoleranceMax : tolerance ≤ 1) :
    ¬ (quittingFloorFreeRobustChargedRelation reward tolerance
      (rewardBound + 2)).HasFiniteBudget := by
  intro hbudget
  have hbudget' : (quittingFloorFreeRobustChargedRelation reward tolerance
      ((rewardBound + 1) + 1)).HasFiniteBudget := by
    rw [show (rewardBound + 1) + 1 = rewardBound + 2 by ring]
    exact hbudget
  let potential := quittingRobustSmoothedCapacity reward tolerance (rewardBound + 1) htolerance
  apply not_differentiable_absorptionDrift_of_nonnegative_productLow reward hnonnegative hlow
    rewardBound (rewardBound + 1) hreward (by linarith) potential
  · intro point _
    exact ((contDiff_quittingRobustSmoothedCapacity htolerance hbudget').differentiable
      (by norm_num)).differentiableAt
  · intro point hpoint root hnash hpositive
    have htarget : ∀ player,
        |quittingRootSuccessorPayoff reward point root player| ≤ rewardBound + 1 := by
      intro player
      exact abs_quittingRootExpectedPayoff_le_bound reward point root player
        (fun terminal player => (hreward terminal player).trans (by linarith)) hpoint
    have hdefect := (isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero
      reward point root).mp hnash
    let edge : QuittingRobustChargedEdge reward (tolerance / 4) (rewardBound + 1) :=
      ⟨((⟨point, hpoint⟩, quittingSimplexOfRoot root),
        ⟨quittingRootSuccessorPayoff reward point root, htarget⟩), by
        intro player
        change |quittingRootSuccessorPayoff reward point root player -
            quittingRootSuccessorPayoff reward point
              (quittingRootOfSimplex (quittingSimplexOfRoot root)) player| ≤
              tolerance / 4 * quittingRootAbsorptionMass
                (quittingRootOfSimplex (quittingSimplexOfRoot root)) ∧
          quittingRootCoordinateNashDefect reward point
              (quittingRootOfSimplex (quittingSimplexOfRoot root)) player ≤
            tolerance / 4 * quittingRootAbsorptionMass
              (quittingRootOfSimplex (quittingSimplexOfRoot root))
        rw [quittingRootOfSimplex_simplexOfRoot, sub_self, abs_zero, hdefect player]
        exact ⟨mul_nonneg (by positivity) hpositive.le,
          mul_nonneg (by positivity) hpositive.le⟩⟩
    have hdrop := quittingRobustChargedEdge_charge_add_smoothedCapacity_target_le_source
      htolerance htoleranceMax hbudget' edge
    change quittingRootAbsorptionMass
        (quittingRootOfSimplex (quittingSimplexOfRoot root)) +
      potential (quittingRootSuccessorPayoff reward point root) ≤ potential point at hdrop
    rw [quittingRootOfSimplex_simplexOfRoot] at hdrop
    linarith

/-- For four players, NN and product-low supply floor-free weighted packets
at every positive tolerance and every nonnegative requested charge in the
one fixed box of radius `rewardBound + 2`. Singleton levels may be signed. -/
theorem hasFloorFreeAbsorptionWeightedFiniteForwardPackets_of_nonnegative_productLow
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnonnegative : HasNonnegativeOwnQuittingPremium reward)
    (hlow : HasProductLowQuittingPremium reward)
    (rewardBound : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound) :
    HasFloorFreeAbsorptionWeightedFiniteForwardPackets reward (rewardBound + 2) := by
  intro tolerance htolerance requested _hrequested
  let epsilon := min tolerance 1
  have hepsilon : 0 < epsilon := lt_min htolerance (by norm_num)
  have hnot := not_hasFiniteBudget_of_nonnegative_productLow reward hnonnegative hlow
    rewardBound epsilon hreward hepsilon (min_le_right _ _)
  obtain ⟨charge, ⟨source, target, path, rfl⟩, hcharge⟩ :=
    not_bddAbove_iff.mp hnot requested
  let packet := quittingRobustChargedPathToFloorFreePacket path
  refine ⟨{
    roots := packet.roots
    value := packet.value
    horizon := packet.horizon
    value_mem := packet.value_mem
    bellman := ?_
    regret := ?_
    chargeTarget_le := hcharge.le.trans packet.chargeTarget_le }⟩
  · intro time htime player
    exact (packet.bellman time htime player).trans
      (mul_le_mul_of_nonneg_right (min_le_left _ _)
        (quittingRootAbsorptionMass_nonneg _))
  · intro time htime player
    exact (packet.regret time htime player).trans
      (mul_le_mul_of_nonneg_right (min_le_left _ _)
        (quittingRootAbsorptionMass_nonneg _))

/-- The finite weak support-peeling input supplies the same fixed-box
floor-free producer under nonnegative own premiums. -/
theorem hasFloorFreeAbsorptionWeightedFiniteForwardPackets_of_nonnegative_weakSupportPeeling
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnonnegative : HasNonnegativeOwnQuittingPremium reward)
    (hpeeling : HasWeakQuittingPremiumSupportPeeling reward)
    (rewardBound : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound) :
    HasFloorFreeAbsorptionWeightedFiniteForwardPackets reward (rewardBound + 2) :=
  hasFloorFreeAbsorptionWeightedFiniteForwardPackets_of_nonnegative_productLow
    reward hnonnegative
    ((hasProductLowQuittingPremium_iff_weakSupportPeeling_of_nonnegative
      reward hnonnegative).mpr hpeeling) rewardBound hreward

end GameTheory

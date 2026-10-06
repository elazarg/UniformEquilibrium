import MathUE.Topology.AmbientDegreeNegativeFixedPointObstruction
import UniformEquilibrium.Quitting.Classification.JoiningAttractiveCoreBadJacobian

/-! # Actual selected return on the dense attractive-core annotation domain

The negative-index obstruction internally counts all full ambient fixed
points. The source hypotheses supply their actual derivatives. The pure-core
exit is explicit; boundary restoration is not part of this declaration.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_exactRoot_singletonSublevel_of_joiningAttractive_generic_tail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (hattractive : HasStrictJoiningAttractivePremiumCore reward)
    (hcard : (quittingPremiumCore reward).card = 3)
    (havoid : tail ∈ quittingPairTieAvoidanceDomain reward (quittingCoreOrderedPairs reward))
    (hbelow : ∃ player, tail player < reward (quittingSingletonTerminal player) player)
    (hnopure : ¬IsεQuittingRootNash reward tail 0
      (quittingPureSetRoot (quittingPremiumCore reward))) :
    ∃ root, IsεQuittingRootNash reward tail 0 root ∧
      ∃ player, quittingRootSuccessorPayoff reward tail root player ≤
        reward (quittingSingletonTerminal player) player := by
  by_contra hreturn
  have hbad : ∀ root, IsεQuittingRootNash reward tail 0 root →
      ∀ player, reward (quittingSingletonTerminal player) player <
        quittingRootSuccessorPayoff reward tail root player := by
    intro root hnash player
    by_contra hnot
    exact hreturn ⟨root, hnash, player, le_of_not_gt hnot⟩
  apply Math.Topology.not_all_fixedPoints_have_negative_det_finite
    (quittingFullClippedEndpointMap reward tail)
    (continuous_quittingFullClippedEndpointMap reward tail)
    (quittingFullClippedEndpointMap_mem_unitCube reward tail)
  intro hazard hfixed
  have hcube : hazard ∈ Set.Icc (fun _ => 0) (fun _ => 1) := by
    rw [← hfixed]
    exact quittingFullClippedEndpointMap_mem_unitCube reward tail hazard
  let root := rootOfHazard hazard hcube.1 hcube.2
  have hnash : IsεQuittingRootNash reward tail 0 root :=
    (quittingFullClippedEndpointMap_eq_self_iff_isZeroNash_rootOfHazard
      reward tail hazard hcube.1 hcube.2).mp hfixed
  obtain ⟨derivative, hdiff, hnegative⟩ :=
    joiningAttractive_badRoot_hasFDerivAt_and_negative_det reward tail hattractive hcard
      havoid hbelow hnopure root hnash (hbad root hnash)
  exact ⟨derivative, by simpa only [root, hazardOfRoot_rootOfHazard] using hdiff, hnegative⟩

end GameTheory

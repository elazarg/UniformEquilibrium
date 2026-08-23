/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.LogarithmicPathBlockAdapter

/-!
# Strategic exceptional-owner adapter for punishment-normal paths

This narrow module connects the analytic positive-survival conclusion to the
literal exceptional-owner branch consumed by the projective decoder.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open Filter
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A positive deleted-survival limit on an ambient punishment-normal path is
exactly a normal no-harm singleton-owner certificate. -/
theorem
    ContinuousZeroPerfectSingletonPath.quittingNormalNoHarmSingletonOwner_of_positive_deletedLimit
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward))
    {owner : ι} {limit : ℝ}
    (htendsto : Tendsto
      (witness.ambientSingletonWitness.deletedSurvival owner)
      atTop (nhds limit))
    (hlimit : 0 < limit) :
    QuittingNormalNoHarmSingletonOwner reward := by
  obtain ⟨hnoHarm, hnormal⟩ :=
    witness.ambient_positive_deletedLimit_ownerData htendsto hlimit
  exact quittingNormalNoHarmSingletonOwner_of_owner reward owner
    hnoHarm hnormal

/-- The analytic deleted-clock split closes the literal strategic fork for
one punishment-normal path. -/
theorem ContinuousZeroPerfectSingletonPath.punishmentNormalPathStrategicForkAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward)) :
    QuittingPunishmentNormalPathStrategicForkAt reward witness := by
  rcases witness.ambientSingletonWitness.exists_positive_deletedLimit_or_all_zero with
    ⟨owner, limit, hlimit, htendsto⟩ | hzero
  · exact Or.inl
      (witness.quittingNormalNoHarmSingletonOwner_of_positive_deletedLimit
        htendsto hlimit)
  · exact Or.inr ⟨
      witness.ambientLogarithmicPureTimeTargetCertificate_of_zero
        reward hzero⟩

/-- Every punishment-normal singleton path satisfies the exact exceptional
owner versus fixed-target product-approximation fork. -/
theorem quittingPunishmentNormalPathStrategicFork
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    QuittingPunishmentNormalPathStrategicFork reward :=
  fun witness => witness.punishmentNormalPathStrategicForkAt reward

/-- The stronger Snell fork also supplies the compatibility path-decoder
interface without an additional hypothesis. -/
theorem quittingPunishmentNormalPathDecoder_of_snell
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    QuittingPunishmentNormalPathDecoder reward :=
  (quittingPunishmentNormalPathStrategicFork reward).pathDecoder

/-- Projective Q-bar on the punishment-normal principal matrix now has its
unconditional checked uniform-payoff consumer. -/
theorem exists_uniformEquilibriumPayoff_of_punishmentNormal_projectiveQBar_snell
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hQ : IsProjectiveQBarMatrix
      (normalizedPunishmentNormalPlayerMatrix reward)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_of_punishmentNormal_projectiveQBar_of_strategicFork
    reward (quittingPunishmentNormalPathStrategicFork reward) hQ

/-- The packet's ambient projective-Q-bar hypothesis implies the final
uniform-equilibrium-payoff conclusion. -/
theorem exists_uniformEquilibriumPayoff_of_projectiveQBar_snell
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hQ : IsProjectiveQBarMatrix (normalizedSoloMatrix reward)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_of_projectiveQBar_of_strategicFork
    reward (quittingPunishmentNormalPathStrategicFork reward) hQ

end QuittingLCPClassification
end GameTheory

/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Classification.AbnormalSingletonConsequences
import UniformEquilibrium.Quitting.Classification.LCP.NormalCore
import UniformEquilibrium.Quitting.Classification.PreemptionGateDictionary

/-!
# Normal-core membership implies punishment normality

Every member of the recursively stabilized normal core has a distinct
nonpositive normalized solo-matrix entry.  An abnormal player has the
opposite strict singleton comparison against every distinct owner.  Combining
the two statements proves the strategic normality of every core member.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Membership in the recursively stabilized normal core implies that the
player's solo payoff covers its behavioral punishment value. -/
theorem mem_punishmentNormalPlayers_of_mem_normalCore
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {who : ι}
    (hwho : who ∈ normalCore (normalizedSoloMatrix reward)) :
    IsQuittingNormalPlayer reward who := by
  obtain ⟨owner, _howner, hne, hentry⟩ :=
    exists_core_blocker_of_mem_normalCore
      (normalizedSoloMatrix reward) hwho
  by_contra hnotNormal
  have habnormal : IsQuittingAbnormalPlayer reward who :=
    lt_of_not_ge hnotNormal
  obtain ⟨_hself, hfloor⟩ :=
    abnormal_singletonFloor_chain reward habnormal hne.symm
  rw [normalizedSoloMatrix_eq_soloReward_sub] at hentry
  linarith

/-- If the normalized solo matrix has full normal core, every player is
punishment-normal. -/
theorem all_punishmentNormal_of_normalCore_eq_univ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcore : normalCore (normalizedSoloMatrix reward) = Finset.univ) :
    ∀ who, IsQuittingNormalPlayer reward who := by
  intro who
  apply mem_punishmentNormalPlayers_of_mem_normalCore reward
  rw [hcore]
  exact Finset.mem_univ who

end QuittingLCPClassification
end GameTheory

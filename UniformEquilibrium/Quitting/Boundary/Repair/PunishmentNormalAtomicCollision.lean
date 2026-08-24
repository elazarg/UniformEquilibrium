/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Repair.AtomicBlockerPaidGeometry
import UniformEquilibrium.Quitting.Classification.AbnormalPlayers

/-!
# Punishment-normal singleton rows force atomic collisions

At the pure singleton root, punishment normality makes the forced owner's
atomic-blocker balance nonnegative.  The terminal exploitability barrier must
therefore be paid by a distinct outsider.  Its attaining pure endpoint cannot
be Continue, so the outsider's literal collision gain retains the full
terminal gap.

The barrier used here is proved against arbitrary behavioral deviations.  The
pure endpoint appears only after that unrestricted semantic estimate has been
reduced to the surely absorbing singleton row.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- At the instant singleton root, the atomic balance is exactly the owner's
singleton payoff minus its punishment value. -/
theorem quittingAtomicBlockerBalance_instantRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) :
    quittingAtomicBlockerBalance reward (quittingInstantRoot owner) owner =
      quittingSoloReward reward owner owner -
        quittingPunishmentValue reward owner := by
  unfold quittingInstantRoot
  rw [← quittingPureSetRoot_singleton]
  unfold quittingAtomicBlockerBalance quittingForcedOwnerObeyValue
    quittingForcedOwnerRefusalCap quittingForcedOwnerAllOutsidersContinueMass
  rw [quittingRootAbsorbingContribution_pureSetRoot,
    quittingStationaryFixedOpponentsContinueReward_pureSetRoot,
    quittingStationaryFixedOpponentsContinueMass_pureSetRoot_of_erase_empty]
  · simp [quittingSoloReward]
  · simp

/-- At the instant singleton root, an outsider coordinate is exactly the
positive part of its literal Quit-together gain. -/
theorem quittingForcedOwnerOutsiderCoordinateDefect_instantRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner other : ι) (hne : other ≠ owner) :
    quittingForcedOwnerOutsiderCoordinateDefect reward
        (quittingInstantRoot owner) owner other =
      max 0 (quittingSingletonCollisionReward reward owner other -
        quittingSoloReward reward owner other) := by
  unfold quittingInstantRoot
  rw [← quittingPureSetRoot_singleton]
  unfold quittingForcedOwnerOutsiderCoordinateDefect
  rw [if_neg hne,
    quittingStationaryFixedOpponentsQuitValue_pureSetRoot,
    quittingStationaryFixedOpponentsContinueReward_pureSetRoot,
    quittingRootAbsorbingContribution_pureSetRoot]
  have hnotMem : other ∉ ({owner} : Finset ι) := by
    simpa using hne
  rw [Finset.erase_eq_of_notMem hnotMem,
    quittingSetReward_insert_singleton,
    quittingSetReward_singleton_eq_soloReward]
  by_cases hle : quittingSingletonCollisionReward reward owner other ≤
      quittingSoloReward reward owner other
  · rw [max_eq_right hle, sub_self, max_self,
      max_eq_left (sub_nonpos.mpr hle)]
  · rw [max_eq_left (le_of_not_ge hle)]

namespace QuittingTerminalExploitabilityWitness

/-- A punishment-normal owner forces a distinct outsider whose literal
singleton collision gain is at least the full terminal exploitability gap. -/
theorem exists_atomicCollision_gain_of_punishmentValue_le_solo
    (witness : QuittingTerminalExploitabilityWitness reward) (owner : ι)
    (hnormal : quittingPunishmentValue reward owner ≤
      quittingSoloReward reward owner owner) :
    ∃ other, other ≠ owner ∧
      quittingSoloReward reward owner other + witness.terminalGap ≤
        quittingSingletonCollisionReward reward owner other := by
  let root := quittingInstantRoot owner
  have howner : root owner = PMF.pure true := by
    dsimp only [root, quittingInstantRoot]
    simp [quittingSoloStationaryRoot]
  have hbalance : 0 ≤ quittingAtomicBlockerBalance reward root owner := by
    dsimp only [root]
    rw [quittingAtomicBlockerBalance_instantRoot]
    linarith
  obtain ⟨other, hne, action, hgain⟩ :=
    exists_outsider_pureEndpoint_gain_ge_of_nonneg_blockerBalance
      howner witness.terminalGap_pos witness.terminalExploitability hbalance
  cases action with
  | false =>
      have hupdate :
          Function.update root other (PMF.pure false) = root := by
        dsimp only [root]
        unfold quittingInstantRoot
        rw [← quittingPureSetRoot_singleton]
        simp [hne]
      rw [hupdate] at hgain
      linarith [witness.terminalGap_pos]
  | true =>
      refine ⟨other, hne, ?_⟩
      dsimp only [root] at hgain
      unfold quittingInstantRoot at hgain
      rw [← quittingPureSetRoot_singleton] at hgain
      rw [update_quittingPureSetRoot_true,
        quittingRootExpectedPayoff_eq_absorbingContribution_add,
        quittingRootExpectedPayoff_eq_absorbingContribution_add,
        quittingRootAbsorbingContribution_pureSetRoot,
        quittingRootAbsorbingContribution_pureSetRoot,
        stationaryContinueMass_pureSetRoot_of_nonempty
          (Finset.singleton_nonempty owner),
        stationaryContinueMass_pureSetRoot_of_nonempty
          (Finset.insert_nonempty other {owner}),
        zero_mul, add_zero, quittingSetReward_singleton_eq_soloReward,
        quittingSetReward_insert_singleton] at hgain
      simpa using hgain

/-- Punishment normality is the named source adapter for the atomic collision
handoff. -/
theorem exists_atomicCollision_gain_of_normal
    (witness : QuittingTerminalExploitabilityWitness reward) (owner : ι)
    (hnormal : IsQuittingNormalPlayer reward owner) :
    ∃ other, other ≠ owner ∧
      quittingSoloReward reward owner other + witness.terminalGap ≤
        quittingSingletonCollisionReward reward owner other := by
  apply witness.exists_atomicCollision_gain_of_punishmentValue_le_solo owner
  simpa [IsQuittingNormalPlayer, quittingSoloSelfPayoff,
    quittingSoloReward] using hnormal

end QuittingTerminalExploitabilityWitness

end GameTheory

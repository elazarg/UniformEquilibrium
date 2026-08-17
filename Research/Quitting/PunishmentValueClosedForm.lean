/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.BlockPlayerDeletion
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlayerDeletion
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# The punishment value of a join-antitone player in closed form

`quittingPunishmentValue` is an infimum of behavioral best-reply values over
all opponent plans.  For a player that weakly loses by joining every nonempty
opponent coalition, that infimum collapses to a finite table minimum: the
least of `0` and the player's own rewards at the coalitions excluding it.

The consequence is that the abstract punishment hypotheses of
`quittingBestReplyValue_eq_never_of_ownerJoinAntitone` and
`hasTerminalExploitabilityGap_deletePlayer_of_ownerJoinAntitone` become
decidable table checks, and that their strict solo inequality can be relaxed
to a weak one — the weak form is delivered here by instantiating
`hasTerminalExploitabilityGap_deleteBlock_of_dispensable` at a singleton
block.
-/

noncomputable section

namespace GameTheory

open StochasticGame QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The **continue floor** of `owner`: the least of `0` and the rewards of
`owner` at the nonempty coalitions that exclude it. -/
def quittingContinueFloor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) : ℝ :=
  quittingBlockContinueFloor reward {owner} owner

theorem quittingContinueFloor_nonpos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) :
    quittingContinueFloor reward owner ≤ 0 :=
  quittingBlockContinueFloor_nonpos reward {owner} owner

theorem quittingContinueFloor_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (S : Finset ι) (hS : S.Nonempty) (howner : owner ∉ S) :
    quittingContinueFloor reward owner ≤ reward ⟨S, hS⟩ owner :=
  quittingBlockContinueFloor_le reward {owner} owner S hS
    (Finset.disjoint_singleton_right.mpr howner)

omit [Fintype ι] in
/-- Single-owner join antitonicity is block join antitonicity at the
singleton block. -/
theorem quittingBlockJoinAntitone_singleton_of_ownerJoinAntitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {owner : ι}
    (hjoin : QuittingOwnerJoinAntitone reward owner) :
    QuittingBlockJoinAntitone reward {owner} owner :=
  fun quitters hquitters hdisjoint =>
    hjoin quitters hquitters (Finset.disjoint_singleton_right.mp hdisjoint)

/-- **The lower leg.**  The continue floor is below the punishment value for
every player, with no hypothesis on the table.  Never quitting already
guarantees the floor against every opponent plan. -/
theorem quittingContinueFloor_le_quittingPunishmentValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) :
    quittingContinueFloor reward owner ≤ quittingPunishmentValue reward owner := by
  rw [quittingPunishmentValue]
  refine le_ciInf fun profile => ?_
  refine le_trans ?_ (le_quittingBestReplyValue reward profile owner
    (quittingPureTimeBehaviorStrategy reward owner none))
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
  exact continueFloor_le_neverTail_of_quiet reward {owner}
    (quittingProfileLiveRoot reward profile) owner
    (quittingContinueFloor reward owner)
    (quittingRootsBlockQuiet_singleton owner _)
    (fun S hS hdisjoint =>
      quittingBlockContinueFloor_le reward {owner} owner S hS hdisjoint)
    (quittingContinueFloor_nonpos reward owner) 0

/-- **The upper leg.**  For a join-antitone player with a nonpositive solo
reward, every pure exit row already caps the punishment value by the
corresponding table entry. -/
theorem quittingPunishmentValue_le_continueFloor_of_ownerJoinAntitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {owner : ι}
    (hjoin : QuittingOwnerJoinAntitone reward owner)
    (hsolo : reward (quittingSingletonTerminal owner) owner ≤ 0) :
    quittingPunishmentValue reward owner ≤ quittingContinueFloor reward owner := by
  classical
  unfold quittingContinueFloor quittingBlockContinueFloor
  refine Finset.le_min' _ _ _ ?_
  intro value hvalue
  rcases Finset.mem_insert.mp hvalue with hzero | hmem
  · subst hzero
    have hcap := quittingPunishmentValue_le_stationaryUnilateralCap reward owner
      (quittingPureSetRoot (∅ : Finset ι))
    rw [quittingStationaryUnilateralCap_pureSetRoot] at hcap
    have hinsert : quittingSetReward reward (insert owner (∅ : Finset ι)) owner =
        reward (quittingSingletonTerminal owner) owner := by
      simp [quittingSetReward, quittingSingletonTerminal]
    have herase : quittingSetReward reward
        ((∅ : Finset ι).erase owner) owner = 0 := by
      simp [quittingSetReward]
    rw [hinsert, herase] at hcap
    exact le_trans hcap (max_le hsolo le_rfl)
  · obtain ⟨terminal, hterminal, rfl⟩ := Finset.mem_image.mp hmem
    have hdisjoint : Disjoint terminal.1 ({owner} : Finset ι) :=
      (Finset.mem_filter.mp hterminal).2
    have hnotMem : owner ∉ terminal.1 :=
      Finset.disjoint_singleton_right.mp hdisjoint
    have hcap := quittingPunishmentValue_le_stationaryUnilateralCap reward owner
      (quittingPureSetRoot terminal.1)
    rw [quittingStationaryUnilateralCap_pureSetRoot,
      Finset.erase_eq_of_notMem hnotMem,
      quittingSetReward_of_nonempty reward terminal.2,
      quittingSetReward_of_nonempty reward
        (Finset.insert_nonempty owner terminal.1)] at hcap
    exact le_trans hcap
      (max_le (hjoin terminal.1 terminal.2 hnotMem) le_rfl)

/-- **The closed form.**  Under join antitonicity and a nonpositive solo
reward, the punishment value is the continue floor: an infimum over all
behavior profiles equals a finite minimum over the reward table. -/
theorem quittingPunishmentValue_eq_continueFloor_of_ownerJoinAntitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {owner : ι}
    (hjoin : QuittingOwnerJoinAntitone reward owner)
    (hsolo : reward (quittingSingletonTerminal owner) owner ≤ 0) :
    quittingPunishmentValue reward owner = quittingContinueFloor reward owner :=
  le_antisymm
    (quittingPunishmentValue_le_continueFloor_of_ownerJoinAntitone reward hjoin
      hsolo)
    (quittingContinueFloor_le_quittingPunishmentValue reward owner)

/-! ## Discharging the abstract punishment hypotheses -/

/-- **The finite table check discharges both punishment hypotheses.**  The
abstract pair consumed by `quittingBestReplyValue_eq_never_of_ownerJoinAntitone`
and `hasTerminalExploitabilityGap_deletePlayer_of_ownerJoinAntitone` follows
from a strict comparison of the solo reward with the continue floor. -/
theorem quittingPunishmentValue_gate_of_lt_continueFloor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {owner : ι}
    (hjoin : QuittingOwnerJoinAntitone reward owner)
    (hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingContinueFloor reward owner) :
    reward (quittingSingletonTerminal owner) owner <
        quittingPunishmentValue reward owner ∧
      quittingPunishmentValue reward owner ≤ 0 := by
  have hnonpos := quittingContinueFloor_nonpos reward owner
  have heq := quittingPunishmentValue_eq_continueFloor_of_ownerJoinAntitone
    reward hjoin (le_of_lt (lt_of_lt_of_le hsolo hnonpos))
  exact ⟨by rw [heq]; exact hsolo, by rw [heq]; exact hnonpos⟩

/-- The never-quit best response of
`quittingBestReplyValue_eq_never_of_ownerJoinAntitone`, with its punishment
hypotheses replaced by the finite table check. -/
theorem quittingBestReplyValue_eq_never_of_lt_continueFloor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) {owner : ι}
    (hjoin : QuittingOwnerJoinAntitone reward owner)
    (hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingContinueFloor reward owner) :
    quittingBestReplyValue reward profile owner =
      quittingTerminalPayoff reward
        (Function.update profile owner
          (quittingPureTimeBehaviorStrategy reward owner none)) owner := by
  obtain ⟨hlt, hchi⟩ :=
    quittingPunishmentValue_gate_of_lt_continueFloor reward hjoin hsolo
  exact quittingBestReplyValue_eq_never_of_ownerJoinAntitone reward profile
    owner hjoin hlt hchi

/-- The single-owner deletion descent of
`hasTerminalExploitabilityGap_deletePlayer_of_ownerJoinAntitone`, with its
punishment hypotheses replaced by the finite table check. -/
theorem hasTerminalExploitabilityGap_deletePlayer_of_lt_continueFloor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    {gap : ℝ} (hgap : 0 < gap)
    (hexploit : HasTerminalExploitabilityGap reward gap)
    (hjoin : QuittingOwnerJoinAntitone reward owner)
    (hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingContinueFloor reward owner) :
    HasTerminalExploitabilityGap
      (quittingDeletePlayerReward reward owner) gap := by
  obtain ⟨hlt, hchi⟩ :=
    quittingPunishmentValue_gate_of_lt_continueFloor reward hjoin hsolo
  exact hasTerminalExploitabilityGap_deletePlayer_of_ownerJoinAntitone reward
    owner hgap hexploit hjoin hlt hchi

/-! ## The weak solo inequality suffices

The strict inequality above is an artifact of routing through the punishment
value.  Deleting the singleton block `{owner}` instead uses the continue floor
directly, and only needs the weak comparison. -/

/-- **Exploitability-floor descent at the weak singleton gate.**  Deleting a
join-antitone player whose solo reward is at most its continue floor
preserves a witnessed positive terminal exploitability gap exactly. -/
theorem hasTerminalExploitabilityGap_deleteSingletonBlock_of_le_continueFloor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    {gap : ℝ} (hgap : 0 < gap)
    (hexploit : HasTerminalExploitabilityGap reward gap)
    (hjoin : QuittingOwnerJoinAntitone reward owner)
    (hsolo : reward (quittingSingletonTerminal owner) owner ≤
      quittingContinueFloor reward owner) :
    HasTerminalExploitabilityGap
      (quittingDeleteBlockReward reward {owner}) gap := by
  refine hasTerminalExploitabilityGap_deleteBlock_of_dispensable reward {owner}
    hgap hexploit fun d hd => ?_
  obtain rfl : d = owner := Finset.mem_singleton.mp hd
  exact ⟨quittingBlockJoinAntitone_singleton_of_ownerJoinAntitone reward hjoin,
    hsolo⟩

/-- **The weak singleton deletion producer.**  If a join-antitone player's
solo reward is at most its continue floor and the game on the other players
has a uniform-equilibrium payoff, so does the original game. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_le_continueFloor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (hjoin : QuittingOwnerJoinAntitone reward owner)
    (hsolo : reward (quittingSingletonTerminal owner) owner ≤
      quittingContinueFloor reward owner)
    (hsurvivor : ∃ payoff : Payoff (QuittingBlockSurvivor ({owner} : Finset ι)),
      (quittingGame
        (quittingDeleteBlockReward reward {owner})).IsUniformEquilibriumPayoff
          none payoff) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  refine quittingGame_exists_uniformEquilibriumPayoff_of_blockDispensable reward
    {owner} (fun d hd => ?_) hsurvivor
  obtain rfl : d = owner := Finset.mem_singleton.mp hd
  exact ⟨quittingBlockJoinAntitone_singleton_of_ownerJoinAntitone reward hjoin,
    hsolo⟩

end GameTheory

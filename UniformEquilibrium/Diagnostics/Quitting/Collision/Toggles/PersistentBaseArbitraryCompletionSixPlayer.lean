/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.PersistentBaseArbitraryCompletionEscape
import UniformEquilibrium.Quitting.Paths.SixPlayerOnePairMassTargetLock

/-!
# Six-player disjoint-target consequence of arbitrary persistent-base completion

The arbitrary-completion profile for the persistent pair `A` puts no terminal mass on the
disjoint pair `B`.  This specializes the general adapter without imposing any restriction on
the four payoff coordinates outside `A`.
-/

noncomputable section

namespace GameTheory

open StochasticGame
open _root_.Math.Probability
open SixPlayerOnePair

variable {Player : Type} [Fintype Player] [DecidableEq Player]

/-- Under literal membership reward at one coordinate, terminal membership mass is exactly that
coordinate's terminal payoff. -/
theorem coalitionMemberMass_terminalOutcomeMass_eq_payoff_of_persistentBaseMembership
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (profile : (quittingGame reward).BehaviorProfile)
    (base : Finset Player) (member : Player) (hmember : member ∈ base)
    (hmembership : QuittingPersistentBaseMembershipReward reward base) :
    coalitionMemberMass (quittingTerminalOutcomeMass reward profile) member =
      quittingTerminalPayoff reward profile member := by
  have hmoment := congrFun
    (quittingTerminalRewardMoment_outcomeMass reward profile) member
  rw [← hmoment]
  unfold coalitionMemberMass coalitionEventMass quittingTerminalRewardMoment
  apply Finset.sum_congr rfl
  intro outcome _
  cases outcome with
  | none => simp [CoalitionOutcome.coalition, quittingTerminalOutcomeReward]
  | some terminal =>
      simp [CoalitionOutcome.coalition, quittingTerminalOutcomeReward,
        hmembership terminal member hmember]

/-- The probability that a player belongs to the realized coalition is at most one. -/
theorem coalitionMemberMass_le_one
    {mass : CoalitionOutcome Player → ℝ}
    (hmass : mass ∈ stdSimplex ℝ (CoalitionOutcome Player)) (member : Player) :
    coalitionMemberMass mass member ≤ 1 := by
  rw [← hmass.2]
  unfold coalitionMemberMass coalitionEventMass
  apply Finset.sum_le_sum
  intro outcome _
  split_ifs <;> simp [hmass.1 outcome]

/-- An exact coalition omitting `member` is bounded by the complementary probability that
`member` is absent. -/
theorem exactCoalitionMass_le_one_sub_coalitionMemberMass_of_not_mem
    {mass : CoalitionOutcome Player → ℝ}
    (hmass : mass ∈ stdSimplex ℝ (CoalitionOutcome Player))
    (target : Finset Player) (member : Player) (hnot : member ∉ target) :
    exactCoalitionMass mass target ≤ 1 - coalitionMemberMass mass member := by
  rw [le_sub_iff_add_le, ← hmass.2]
  unfold exactCoalitionMass coalitionMemberMass coalitionEventMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro outcome _
  by_cases htarget : outcome.coalition = target
  · rw [if_pos htarget]
    have hmember : member ∉ outcome.coalition := by
      simpa [htarget] using hnot
    rw [if_neg hmember]
    simp
  · rw [if_neg htarget]
    split_ifs <;> simp [hmass.1 outcome]

/-- **Six-player arbitrary-completion escape.**  If the two coordinates of `A` retain literal
membership reward, arbitrary changes to all four other coordinates still provide an exact
stationary terminal Nash profile and a uniform payoff whose exact `B` atom has mass zero. -/
theorem exists_targetA_exactTerminalNash_uniformPayoff_and_secondPairMass_zero
    (reward : {S : Finset SixPlayer // S.Nonempty} → Payoff SixPlayer)
    (hmembership : QuittingPersistentBaseMembershipReward reward targetA) :
    ∃ point ∈ quittingPersistentBaseNashSet reward targetA (Finset.univ \ targetA),
      let root := quittingPersistentBaseRoot targetA (Finset.univ \ targetA) point
      let profile := quittingStationaryProfile reward root
      (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) 0 profile ∧
        (quittingGame reward).IsUniformEquilibriumPayoff none
          (fun player => quittingTerminalPayoff reward profile player) ∧
        secondPairMass reward profile = 0 := by
  have hbase : 2 ≤ targetA.card := by
    rw [targetA_card]
  obtain ⟨point, hpoint, hnash, huniform⟩ :=
    exists_exactTerminalNash_and_uniformPayoff_of_persistentBaseMembershipReward
      reward targetA hbase hmembership
  let root := quittingPersistentBaseRoot targetA (Finset.univ \ targetA) point
  let profile := quittingStationaryProfile reward root
  refine ⟨point, hpoint, hnash, huniform, ?_⟩
  have hplayer1 : player1 ∈ targetA := by
    simp [targetA]
  have htarget : ∀ terminal player, player ∈ targetA →
      reward terminal player = if player ∈ terminal.1 then 1 else 0 :=
    hmembership
  have hquit := quittingTerminalPayoff_update_quitNow_eq_one_of_targetMembership
    reward profile targetA player1 hplayer1 htarget
  have hdeviation := hnash player1
    (quittingPureTimeBehaviorStrategy reward player1 (some 0))
  rw [hquit] at hdeviation
  have hmemberEq :=
    coalitionMemberMass_terminalOutcomeMass_eq_payoff_of_persistentBaseMembership
      reward profile targetA player1 hplayer1 hmembership
  rw [← hmemberEq] at hdeviation
  have hmass := quittingTerminalOutcomeMass_mem_stdSimplex reward profile
  have hmemberLe := coalitionMemberMass_le_one hmass player1
  have hmemberOne :
      coalitionMemberMass (quittingTerminalOutcomeMass reward profile) player1 = 1 := by
    linarith
  have hnot : player1 ∉ targetB := by
    decide
  have hsecondLe :=
    exactCoalitionMass_le_one_sub_coalitionMemberMass_of_not_mem
      hmass targetB player1 hnot
  have hsecondNonneg := secondPairMass_nonneg reward profile
  change exactCoalitionMass (quittingTerminalOutcomeMass reward profile) targetB = 0
  unfold secondPairMass at hsecondNonneg
  rw [hmemberOne] at hsecondLe
  linarith

end GameTheory

/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.PersistentBaseArbitraryCompletionSixPlayer
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.SingleAnchorArbitraryCompletionEscape

/-!
# Six-player single-anchor arbitrary-completion escape

Retaining the literal membership coordinate of either member of the first
target pair suffices.  All five other reward coordinates may be arbitrary, yet
one exact stationary terminal Nash profile has zero terminal mass on the
disjoint second target pair.
-/

noncomputable section

namespace GameTheory

open StochasticGame
open _root_.Math.Probability
open SixPlayerOnePair

/-- **Six-player single-anchor escape.**  If either member of `targetA` retains
its literal membership coordinate, arbitrary changes to all five other reward
coordinates still leave an exact stationary terminal Nash profile, a uniform
payoff, and zero exact mass on `targetB`. -/
theorem exists_targetA_singleAnchor_exactTerminalNash_uniformPayoff_and_secondPairMass_zero
    (reward : {S : Finset SixPlayer // S.Nonempty} → Payoff SixPlayer)
    (anchor : SixPlayer) (hanchor : anchor ∈ targetA)
    (hmembership : QuittingSingleAnchorMembershipReward reward anchor) :
    ∃ point ∈ quittingPersistentBaseNashSet reward {anchor}
        (quittingSingleAnchorFree anchor),
      let root := quittingSingleAnchorRoot anchor point
      let profile := quittingStationaryProfile reward root
      (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) 0 profile ∧
        (quittingGame reward).IsUniformEquilibriumPayoff none
          (quittingTerminalPayoff reward profile) ∧
        secondPairMass reward profile = 0 := by
  obtain ⟨point, hpoint, hnash, huniform⟩ :=
    exists_exactTerminalNash_and_uniformPayoff_of_singleAnchorMembership
      reward anchor hmembership
  let root := quittingSingleAnchorRoot anchor point
  let profile := quittingStationaryProfile reward root
  refine ⟨point, hpoint, hnash, huniform, ?_⟩
  have hpersistent : QuittingPersistentBaseMembershipReward reward {anchor} := by
    intro terminal who hwho
    have hwhoEq : who = anchor := by simpa using hwho
    subst who
    exact hmembership terminal
  have htarget : ∀ terminal who, who ∈ ({anchor} : Finset SixPlayer) →
      reward terminal who = if who ∈ terminal.1 then 1 else 0 :=
    hpersistent
  have hquit := quittingTerminalPayoff_update_quitNow_eq_one_of_targetMembership
    reward profile {anchor} anchor (by simp) htarget
  have hdeviation := hnash anchor
    (quittingPureTimeBehaviorStrategy reward anchor (some 0))
  rw [hquit] at hdeviation
  have hmemberEq :=
    coalitionMemberMass_terminalOutcomeMass_eq_payoff_of_persistentBaseMembership
      reward profile {anchor} anchor (by simp) hpersistent
  rw [← hmemberEq] at hdeviation
  have hmass := quittingTerminalOutcomeMass_mem_stdSimplex reward profile
  have hmemberLe := coalitionMemberMass_le_one hmass anchor
  have hmemberOne :
      coalitionMemberMass (quittingTerminalOutcomeMass reward profile) anchor = 1 := by
    linarith
  have hnot : anchor ∉ targetB := by
    simp [targetA, targetB] at hanchor ⊢
    rcases hanchor with hanchor | hanchor
    · subst anchor
      decide
    · subst anchor
      decide
  have hsecondLe := exactCoalitionMass_le_one_sub_coalitionMemberMass_of_not_mem
    hmass targetB anchor hnot
  have hsecondNonneg := secondPairMass_nonneg reward profile
  change exactCoalitionMass (quittingTerminalOutcomeMass reward profile) targetB = 0
  unfold secondPairMass at hsecondNonneg
  rw [hmemberOne] at hsecondLe
  linarith

end GameTheory

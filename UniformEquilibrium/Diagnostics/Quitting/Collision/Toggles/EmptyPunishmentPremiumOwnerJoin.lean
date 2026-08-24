/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.ThreeRoleSpectator
import
  UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.RepairedResidualPureExitDescent
import UniformEquilibrium.Quitting.Paths.AnchoredJoinPromotion
import UniformEquilibrium.Quitting.Punishment.ContinueFloor

/-!
# Empty-punishment premium owner join

In a four-player terminal counterexample, a solo reward strictly below the
owner's punishment value forces a nonempty strict owner join.  Testing the
enlarged pure-exit set either supplies its all-behavior uniform payoff or a
strict membership toggle whose responsible player is not the owner.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Finite reward-table residue exposed after promoting the owner join. -/
def EmptyPunishmentPremiumToggleResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) : Prop :=
  ∃ opponentCoalition : Finset ι,
    opponentCoalition.Nonempty ∧ owner ∉ opponentCoalition ∧
    quittingSetReward reward opponentCoalition owner <
        quittingSetReward reward (insert owner opponentCoalition) owner ∧
    ((∃ member ∈ opponentCoalition, member ≠ owner ∧
        quittingSetReward reward (insert owner opponentCoalition) member <
          quittingSetReward reward
            ((insert owner opponentCoalition).erase member) member) ∨
      ∃ outsider ∉ insert owner opponentCoalition, outsider ≠ owner ∧
        quittingSetReward reward (insert owner opponentCoalition) outsider <
          quittingSetReward reward
            (insert outsider (insert owner opponentCoalition)) outsider)

/-- The empty pure opponent row turns a strict punishment premium into a
negative solo reward and a nonpositive punishment value. -/
theorem emptyPunishmentPremium_negatives
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (hpremium : quittingSoloReward reward owner owner <
      quittingPunishmentValue reward owner) :
    quittingSoloReward reward owner owner < 0 ∧
      quittingPunishmentValue reward owner ≤ 0 := by
  have hcap : quittingPunishmentValue reward owner ≤
      max (quittingSoloReward reward owner owner) 0 := by
    simpa only [Finset.insert_empty, Finset.erase_empty,
      quittingSetReward_singleton_eq_soloReward, quittingSetReward_empty] using
      quittingPunishmentValue_le_pureRowCap reward owner ∅
  have hsolo : quittingSoloReward reward owner owner < 0 := by
    by_contra hnot
    have hnonneg : 0 ≤ quittingSoloReward reward owner owner :=
      le_of_not_gt hnot
    have hle : quittingPunishmentValue reward owner ≤
        quittingSoloReward reward owner owner := by
      simpa [max_eq_left hnonneg] using hcap
    exact (not_lt_of_ge hle) hpremium
  refine ⟨hsolo, ?_⟩
  simpa [max_eq_right hsolo.le] using hcap

/-- Exact four-player dispatch before using terminal exploitability to remove
the sure-exit branch. -/
theorem emptyPunishmentPremium_uniform_or_toggle
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (hcard : Fintype.card ι = 4) (owner : ι)
    (hpremium : quittingSoloReward reward owner owner <
      quittingPunishmentValue reward owner) :
    (∃ opponentCoalition : Finset ι,
      opponentCoalition.Nonempty ∧ owner ∉ opponentCoalition ∧
        quittingSetReward reward opponentCoalition owner <
          quittingSetReward reward (insert owner opponentCoalition) owner ∧
        (quittingGame reward).IsUniformEquilibriumPayoff none
          (quittingSetReward reward (insert owner opponentCoalition))) ∨
      EmptyPunishmentPremiumToggleResidual reward owner := by
  obtain ⟨_hsolo, hchi⟩ :=
    emptyPunishmentPremium_negatives reward owner hpremium
  have hpremium' : reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue reward owner := by
    change reward ⟨{owner}, Finset.singleton_nonempty owner⟩ owner <
      quittingPunishmentValue reward owner
    exact hpremium
  obtain ⟨opponentCoalition, hnonempty, howner, hjoin⟩ :=
    witness.exists_strict_owner_toggle_of_card_eq_four
      hcard owner hpremium' hchi
  have hjoin' : quittingSetReward reward opponentCoalition owner <
      quittingSetReward reward (insert owner opponentCoalition) owner := by
    simpa [quittingSetReward_of_nonempty reward hnonempty] using hjoin
  rcases isQuittingSureExitSet_insert_or_oldLeave_or_otherJoin
      reward opponentCoalition howner hjoin' with hsure | htoggle
  · left
    exact ⟨opponentCoalition, hnonempty, howner, hjoin',
      isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet
        reward hsure⟩
  · right
    refine ⟨opponentCoalition, hnonempty, howner, hjoin', ?_⟩
    rcases htoggle with hleave | hjoinOther
    · left
      obtain ⟨member, hmember, hstrict⟩ := hleave
      exact ⟨member, hmember, fun heq => howner (heq ▸ hmember), hstrict⟩
    · right
      obtain ⟨outsider, houtside, hstrict⟩ := hjoinOther
      refine ⟨outsider, houtside, ?_, hstrict⟩
      intro heq
      subst outsider
      exact houtside (Finset.mem_insert_self owner opponentCoalition)

/-- In the terminal-witness regime the all-behavior sure-exit branch is
impossible, leaving the exact nonowner finite toggle residue. -/
theorem QuittingTerminalExploitabilityWitness.emptyPunishmentPremium_residual
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (hcard : Fintype.card ι = 4) (owner : ι)
    (hpremium : quittingSoloReward reward owner owner <
      quittingPunishmentValue reward owner) :
    quittingSoloReward reward owner owner < 0 ∧
      quittingPunishmentValue reward owner ≤ 0 ∧
      EmptyPunishmentPremiumToggleResidual reward owner := by
  obtain ⟨hsolo, hchi⟩ :=
    emptyPunishmentPremium_negatives reward owner hpremium
  refine ⟨hsolo, hchi, ?_⟩
  rcases emptyPunishmentPremium_uniform_or_toggle witness hcard owner hpremium with
    huniform | hresidual
  · obtain ⟨_, _, _, _, huniform⟩ := huniform
    exact False.elim (witness.not_exists_uniformEquilibriumPayoff
      ⟨_, huniform⟩)
  · exact hresidual

/-- The empty cell in the repaired owner-floor descent is not a terminal
residual in four-player counterexample semantics: its punishment premium
feeds the owner-join dispatch above. -/
theorem QuittingTerminalExploitabilityWitness.repairedOwnerFloorResidual_withoutEmpty
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (hcard : Fintype.card ι = 4)
    {owner remaining first second : ι} {fixed : Bool}
    (source : RepairedResidualPureExitSource owner remaining first second fixed)
    (positive : 0 < source.ownerFloorNumerator reward) :
    ∃ firstAction secondAction,
      0 < source.weight firstAction secondAction ∧
      let coalition := repairedResidualWithoutOwner owner remaining first second
        fixed firstAction secondAction
      (coalition.Nonempty ∧
          source.ownerFloorNumerator reward / source.denominator ≤
            quittingSetReward reward coalition owner -
              quittingSetReward reward (insert owner coalition) owner ∧
          0 < source.ownerFloorNumerator reward / source.denominator ∧
          HasRepairedOwnerToggleResidual reward owner coalition) ∨
        EmptyPunishmentPremiumToggleResidual reward owner := by
  obtain ⟨firstAction, secondAction, hweight, result⟩ :=
    witness.repairedOwnerFloorResidual source positive
  refine ⟨firstAction, secondAction, hweight, ?_⟩
  rcases result with hempty | hnonempty
  · right
    have hpremium : quittingSoloReward reward owner owner <
        quittingPunishmentValue reward owner := by
      rcases hempty with ⟨_, hbound, hnormalized⟩
      linarith
    exact (witness.emptyPunishmentPremium_residual hcard owner hpremium).2.2
  · exact Or.inl hnonempty

end GameTheory

/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityWitness
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetReprojectionDiffuseClockBridge
import UniformEquilibrium.Quitting.Boundary.Repair.AtomicBlockerPaidGeometry
import UniformEquilibrium.Quitting.Classification.PlayerDeletionLift
import UniformEquilibrium.Quitting.Cycles.ConditionedDeletedClockSoloCompletion
import UniformEquilibrium.Quitting.Cycles.ConditionedProperFaceDeficientClock
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# Player deletion inside a terminal exploitability witness

`UniformEquilibrium/Quitting/Classification/PlayerDeletionLift.lean` deletes a
universal Never player exactly: a witnessed terminal exploitability gap
descends to the smaller player subtype whenever the owner weakly loses by
joining every nonempty opponent coalition.  This module routes that descent
against the alternative branches available to a terminal exploitability witness.

The dispatcher `exists_strict_owner_toggle_or_exact_playerDeletion` splits on
`exists_strict_owner_toggle_or_ownerJoinAntitone`: either the table exposes a
strict owner-side coalition toggle, or the exploitability floor descends to a
nonempty, strictly smaller player type.  The toggle side is then handed to the
atomic blocker geometry, where the joined-coalition row cannot be a forced
owner Nash row, so some outsider has a strict one-stage deviation.

`QuittingTerminalExploitabilityWitness.strictToggle_or_playerDeletion_of_summableConditionedDeletedClock`
closes the summable conditioned deleted clock against a regime: either the
solo compiler contradicts the regime outright, or the dispatcher applies.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Toggle-or-cardinality-descent dispatcher.**  At the negative singleton
gate with a positive terminal exploitability floor, either a strict
owner-side coalition toggle exists, or the exact same floor descends to the
nonempty, strictly smaller player subtype. -/
theorem exists_strict_owner_toggle_or_exact_playerDeletion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    {gap : ℝ} (hgap : 0 < gap)
    (hexploit : HasTerminalExploitabilityGap reward gap)
    (hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue reward owner)
    (hchi : quittingPunishmentValue reward owner ≤ 0) :
    (∃ (quitters : Finset ι) (hquitters : quitters.Nonempty),
        owner ∉ quitters ∧
          reward ⟨quitters, hquitters⟩ owner <
            reward
              ⟨insert owner quitters,
                Finset.insert_nonempty owner quitters⟩ owner) ∨
      (Nonempty (QuittingDeletedPlayer owner) ∧
        HasTerminalExploitabilityGap
          (quittingDeletePlayerReward reward owner) gap ∧
        Fintype.card (QuittingDeletedPlayer owner) < Fintype.card ι) := by
  rcases exists_strict_owner_toggle_or_ownerJoinAntitone reward owner with
    htoggle | hjoin
  · exact Or.inl htoggle
  · exact Or.inr
      ⟨nonempty_deletedPlayer_of_ownerJoinAntitone_and_gap
          reward owner hgap hexploit hjoin hsolo hchi,
        hasTerminalExploitabilityGap_deletePlayer_of_ownerJoinAntitone
          reward owner hgap hexploit hjoin hsolo hchi,
        card_quittingDeletedPlayer_lt owner⟩

/-! ## The strict-toggle branch enters the atomic blocker geometry -/

/-- A strict owner-side insertion toggle cannot itself be a stable atomic
row in a game with a positive terminal exploitability floor.  Some outsider
has a strict one-stage deviation at the pure joined-coalition row.  This is
the exact handoff from deletion failure to the atomic blocker branch. -/
theorem exists_outsider_atomicDeviation_of_strict_ownerToggle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {gap : ℝ} (hgap : 0 < gap)
    (hexploit : HasTerminalExploitabilityGap reward gap)
    (owner : ι) (quitters : Finset ι) (hquitters : quitters.Nonempty)
    (howner : owner ∉ quitters)
    (htoggle : reward ⟨quitters, hquitters⟩ owner <
      reward
        ⟨insert owner quitters,
          Finset.insert_nonempty owner quitters⟩ owner) :
    ∃ who, who ≠ owner ∧ ∃ deviation : PMF Bool,
      quittingRootExpectedPayoff reward 0
          (Function.update
            (QuittingSureSetOwnerRepair.quittingPureSetRoot
              (insert owner quitters)) who deviation) who >
        quittingRootExpectedPayoff reward 0
          (QuittingSureSetOwnerRepair.quittingPureSetRoot
            (insert owner quitters)) who := by
  obtain ⟨who, hwho, deviation, hdeviation⟩ :=
    exists_outsider_atomicDeviation_ge_of_strict_ownerToggle
      reward hgap hexploit owner quitters hquitters howner htoggle
  exact ⟨who, hwho, deviation, by linarith⟩

/-- Strengthen the toggle side of the deletion dispatcher with its forced
atomic-row instability witness. -/
theorem strictToggle_or_playerDeletion_to_atomicHandoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {gap : ℝ} (hgap : 0 < gap)
    (hexploit : HasTerminalExploitabilityGap reward gap) (owner : ι)
    (hdispatch :
      (∃ (quitters : Finset ι) (hquitters : quitters.Nonempty),
          owner ∉ quitters ∧
            reward ⟨quitters, hquitters⟩ owner <
              reward
                ⟨insert owner quitters,
                  Finset.insert_nonempty owner quitters⟩ owner) ∨
        (Nonempty (QuittingDeletedPlayer owner) ∧
          HasTerminalExploitabilityGap
            (quittingDeletePlayerReward reward owner) gap ∧
          Fintype.card (QuittingDeletedPlayer owner) < Fintype.card ι)) :
    (∃ (quitters : Finset ι) (hquitters : quitters.Nonempty),
        owner ∉ quitters ∧
          reward ⟨quitters, hquitters⟩ owner <
            reward
              ⟨insert owner quitters,
                Finset.insert_nonempty owner quitters⟩ owner ∧
          ∃ who, who ≠ owner ∧ ∃ deviation : PMF Bool,
            quittingRootExpectedPayoff reward 0
                (Function.update
                  (QuittingSureSetOwnerRepair.quittingPureSetRoot
                    (insert owner quitters)) who deviation) who >
              quittingRootExpectedPayoff reward 0
                (QuittingSureSetOwnerRepair.quittingPureSetRoot
                  (insert owner quitters)) who) ∨
      (Nonempty (QuittingDeletedPlayer owner) ∧
        HasTerminalExploitabilityGap
          (quittingDeletePlayerReward reward owner) gap ∧
        Fintype.card (QuittingDeletedPlayer owner) < Fintype.card ι) := by
  rcases hdispatch with htoggle | hdelete
  · left
    obtain ⟨quitters, hquitters, howner, hstrict⟩ := htoggle
    exact ⟨quitters, hquitters, howner, hstrict,
      exists_outsider_atomicDeviation_of_strict_ownerToggle reward hgap
        hexploit owner quitters hquitters howner hstrict⟩
  · exact Or.inr hdelete

/-- **Deficient-clock closure in a terminal exploitability witness.**  A summable
conditioned deleted clock has no residual analytic branch.  If the limiting
solo payoff clears the owner's punishment floor, the existing solo compiler
contradicts the regime.  Otherwise, at a nonpositive punishment floor, the
reward table itself exposes either a strict coalition toggle or an exact
smaller-player exploitability-floor instance. -/
theorem
    QuittingTerminalExploitabilityWitness.strictToggle_or_playerDeletion_of_summableConditionedDeletedClock
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι) (owner : ι) (start : ℕ)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (heventualZero : Tendsto
      (quittingTailEventualAbsorption roots) atTop (nhds 0))
    (hconditionedBound : ∀ time player,
      |quittingTailConditionedValue roots value boundary time player| ≤
        quittingRewardBound reward)
    (htight : ∀ who,
      boundary who = quittingSoloBaseline reward who)
    (hmesh : Tendsto
      (quittingTailConditionedAbsorptionWeight roots) atTop (nhds 0))
    (hsmall : ∀ time, start ≤ time → Fintype.card ι *
      quittingTailConditionedAbsorptionWeight roots time ≤ 1)
    (hsummable : Summable (fun offset =>
      quittingTailConditionedOpponentWeight roots (start + offset) owner))
    (hchi : quittingPunishmentValue reward owner ≤ 0) :
    (∃ (quitters : Finset ι) (hquitters : quitters.Nonempty),
        owner ∉ quitters ∧
          reward ⟨quitters, hquitters⟩ owner <
            reward
              ⟨insert owner quitters,
                Finset.insert_nonempty owner quitters⟩ owner) ∨
      (Nonempty (QuittingDeletedPlayer owner) ∧
        HasTerminalExploitabilityGap
          (quittingDeletePlayerReward reward owner) witness.terminalGap ∧
        Fintype.card (QuittingDeletedPlayer owner) < Fintype.card ι) := by
  by_cases hpunishment : quittingPunishmentValue reward owner ≤
      quittingSoloReward reward owner owner
  · have huniform :=
      isUniformEquilibriumPayoff_soloReward_of_summableConditionedDeletedClock
        reward roots value boundary owner start hpolicy hnash hpositive
        heventualZero hconditionedBound htight hmesh hsmall hsummable
        hpunishment
    exact False.elim (witness.not_exists_uniformEquilibriumPayoff
      ⟨quittingSoloReward reward owner, huniform⟩)
  · have hsolo : reward (quittingSingletonTerminal owner) owner <
        quittingPunishmentValue reward owner := by
      change quittingSoloReward reward owner owner <
        quittingPunishmentValue reward owner
      exact lt_of_not_ge hpunishment
    exact exists_strict_owner_toggle_or_exact_playerDeletion reward owner
      witness.terminalGap_pos witness.terminalExploitability hsolo hchi


end GameTheory

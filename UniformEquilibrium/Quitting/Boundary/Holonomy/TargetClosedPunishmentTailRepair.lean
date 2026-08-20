/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Holonomy.TerminalExploitabilityRepair
import UniformEquilibrium.Quitting.Boundary.Holonomy.TwoOwnerCommonWordRealization

/-!
# Target-closed punishment tails and common-tail repair

Player-indexed target-closed tails can simultaneously approximate every
player's punishment value. A positive terminal exploitability gap nevertheless
forces positive common-tail repair after every positive prefix.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- At every positive accuracy, all players simultaneously have player-indexed
target-closed tails whose own endpoints approximate their punishment values. -/
theorem exists_targetClosedApproxPunishmentTailFamily
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ tails : ι → ℕ → ι → PMF Bool,
      (∀ player, IsQuittingTargetClosedAt reward (tails player) player 0) ∧
      (∀ player,
        quittingRootSequenceTerminalValue reward (tails player) player 0 <
          quittingPunishmentValue reward player + δ) := by
  choose rows hrows using fun player : ι =>
    exists_stationaryRoot_cap_lt_punishmentValue_add reward player hδ
  obtain ⟨tails, hclosed, hvalue⟩ :=
    exists_quittingTargetClosedTailFamily_of_stationaryRoots reward rows
  refine ⟨tails, hclosed, ?_⟩
  intro player
  rw [hvalue player]
  exact hrows player

/-- Arbitrarily accurate player-indexed target-closed tails coexist with a
common-tail repair value bounded below by the terminal exploitability gap
after every positive finite prefix. -/
theorem targetClosedApproxPunishmentTails_and_commonRepair_lowerBound
    (plan : ℕ → ι → PMF Bool) (switch : ℕ) (hswitch : 0 < switch)
    {gap : ℝ} (hexploit : HasTerminalExploitabilityGap reward gap) :
    (∀ δ : ℝ, 0 < δ →
      ∃ tails : ι → ℕ → ι → PMF Bool,
        (∀ player,
          IsQuittingTargetClosedAt reward (tails player) player 0) ∧
        (∀ player,
          quittingRootSequenceTerminalValue reward (tails player) player 0 <
            quittingPunishmentValue reward player + δ)) ∧
      gap ≤ @QuittingBoundaryHolonomy.behavioralTailRepairValue ι _ _
        hexploit.nonempty_players reward
        (quittingFiniteBoundaryHolonomy reward plan 0 (switch - 1)) := by
  letI : Nonempty ι := hexploit.nonempty_players
  constructor
  · intro δ hδ
    exact exists_targetClosedApproxPunishmentTailFamily
      (reward := reward) hδ
  · exact terminalExploitabilityGap_le_behavioralTailRepairValue
      reward plan switch hswitch hexploit

end GameTheory

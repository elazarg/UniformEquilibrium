/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Capacity.TerminalIncomingPathAlternative
import UniformEquilibrium.Quitting.Boundary.Repair.TerminalFunding.OneOwnerFarkas

/-!
# Terminal exploitability witness terminal-funding Farkas adapter

The production one-owner classification shows that a positive singleton debt
cap forces the canonical strict one-owner zero-target root into the Farkas
branch. This module applies that result to the aggregate-calibrated terminal
anchor supplied by a terminal exploitability witness.
-/

noncomputable section

namespace GameTheory

open Finset
open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingAggregateCalibratedTerminalAnchor

/-- For a calibrated positive-debt anchor, the canonical strict one-owner
hazard funds the aggregate terminal cap, but positive singleton debt forces
its affine continuation problem into the Farkas branch. -/
theorem exists_canonicalOwnerFundingFarkas
    (witness : QuittingTerminalExploitabilityWitness reward)
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward) :
    ∃ p : ℝ, ∃ hp0 : 0 < p, ∃ hp1 : p < 1,
      (Fintype.card ι : ℝ) * quittingRewardBound reward * p =
          ∑ who, quittingPositiveSingletonDebtCap reward who ∧
        HasQuittingFrozenRootLiftFarkasCertificate
          (reward := reward) 0 (quittingPunishmentValue reward)
            (quittingRewardBound reward)
            (quittingSureSetOwnerRoot ∅ anchor.owner p hp0.le hp1.le)
            {anchor.owner} ∧
        Nonempty (QuittingOneOwnerFundingObstruction reward
          (quittingPunishmentValue reward) (quittingRewardBound reward)
          anchor.owner p hp0 hp1) := by
  let terminalDebt :=
    ∑ who, quittingPositiveSingletonDebtCap reward who
  let scale := (Fintype.card ι : ℝ) * quittingRewardBound reward
  have hdebtPos : 0 < terminalDebt := by
    exact anchor.terminalAggregateDebt_pos
  have hdebtLt : terminalDebt < scale := by
    exact anchor.terminalAggregateDebt_lt_card_mul_rewardBound witness
  have hscale : 0 < scale := hdebtPos.trans hdebtLt
  let p := terminalDebt / scale
  have hp0 : 0 < p := div_pos hdebtPos hscale
  have hp1 : p < 1 := (div_lt_one hscale).2 hdebtLt
  have hfunds : scale * p = terminalDebt := by
    dsimp [p]
    field_simp
  have hownerCap :
      quittingFiniteNashBellmanPathDynamicDebt
          reward (anchor.last + 1) anchor.path anchor.owner 0 ≤
        quittingPositiveSingletonDebtCap reward anchor.owner :=
    quittingFiniteNashBellmanPathDynamicDebt_le_cap
      reward (anchor.last + 1) anchor.path anchor.path_mem anchor.owner 0
        (by omega)
  have hcap : 0 < quittingPositiveSingletonDebtCap reward anchor.owner :=
    anchor.ownerDebt_pos.trans_le hownerCap
  have hfarkas := positiveSingletonDebtCap_oneOwnerFarkas
    (reward := reward) (quittingPunishmentValue reward)
      (quittingRewardBound reward) anchor.owner p hp0 hp1 hcap
  exact ⟨p, hp0, hp1, by simpa [scale, terminalDebt] using hfunds,
    hfarkas⟩

end QuittingAggregateCalibratedTerminalAnchor

end GameTheory

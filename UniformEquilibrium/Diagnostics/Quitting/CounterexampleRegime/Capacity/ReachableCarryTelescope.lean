/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime
import UniformEquilibrium.Quitting.Debt.Dynamic.ReachableCarryTelescope

/-!
# Counterexample-capacity instances of the finite carry telescope

The production telescope assumes exactly a finite-prefix charge bound. These
three adapters discharge that premise from a counterexample regime for the
canonical aggregate-calibrated terminal anchor.
-/

noncomputable section

namespace GameTheory

open Math.ChargedPathBudget Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

open QuittingFiniteDynamicDebtAdmissibleChronology

/-- Aggregate-calibrated specialization of the intrinsic finite-chain carry
telescope.  Each cutoff is handled on its own selected minimizer, so no
cross-cutoff nesting is needed.  The terminal exact-D cap must still be paid
by the global admissible remaining-capacity account at that same terminal
state. -/
theorem aggregateCalibratedAnchor_initialDebt_le_admissibleCapacity_of_far
    (regime : QuittingCounterexampleRegime reward)
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)
    (hfar :
      QuittingFiniteDynamicDebtAdmissibleChronology.debt
          (reward := reward) anchor.path (anchor.last + 1) ≤
        QuittingFiniteDynamicDebtAdmissibleChronology.aggregateCapacityAccount
          anchor.path anchor.path_mem hpunishment (anchor.last + 1)) :
    QuittingFiniteDynamicDebtAdmissibleChronology.debt
        (reward := reward) anchor.path 0 ≤
      QuittingFiniteDynamicDebtAdmissibleChronology.aggregateCapacityAccount
        anchor.path anchor.path_mem hpunishment 0 :=
  QuittingFiniteDynamicDebtAdmissibleChronology.debt_zero_le_aggregateCapacityAccount_zero_of_far
      anchor.path anchor.path_mem hpunishment regime.prefixCharge_le hfar

/-- Aggregate-calibrated zero-cap specialization. -/
theorem aggregateCalibratedAnchor_initialDebt_le_admissibleCapacity_of_terminalCap_eq_zero
    (regime : QuittingCounterexampleRegime reward)
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)
    (hterminalCap : ∀ who,
      quittingPositiveSingletonDebtCap reward who = 0) :
    QuittingFiniteDynamicDebtAdmissibleChronology.debt
        (reward := reward) anchor.path 0 ≤
      QuittingFiniteDynamicDebtAdmissibleChronology.aggregateCapacityAccount
        anchor.path anchor.path_mem hpunishment 0 :=
  debt_zero_le_aggregateCapacityAccount_zero_of_terminalCap_eq_zero
      anchor.path anchor.path_mem hpunishment regime.prefixCharge_le
        hterminalCap

/-- Aggregate-calibrated incoming-path consumer. -/
theorem aggregateCalibratedAnchor_initialDebt_le_admissibleCapacity_of_incomingPath
    (regime : QuittingCounterexampleRegime reward)
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)
    {sourceState : QuittingPunishmentFloorAdmissibleState reward}
    (segment : (quittingPunishmentFloorAdmissibleChargedRelation reward).Path
      sourceState
      (quittingFiniteDynamicDebtAdmissibleState anchor.path anchor.path_mem
        hpunishment (anchor.last + 1)))
    (hpays :
      QuittingFiniteDynamicDebtAdmissibleChronology.debt
          (reward := reward) anchor.path (anchor.last + 1) ≤
        (Fintype.card ι : ℝ) * quittingRewardBound reward *
          segment.chargeSum) :
    QuittingFiniteDynamicDebtAdmissibleChronology.debt
        (reward := reward) anchor.path 0 ≤
      QuittingFiniteDynamicDebtAdmissibleChronology.aggregateCapacityAccount
        anchor.path anchor.path_mem hpunishment 0 :=
  debt_zero_le_aggregateCapacityAccount_zero_of_incomingPath
      anchor.path anchor.path_mem hpunishment regime.prefixCharge_le segment
        hpays

end GameTheory

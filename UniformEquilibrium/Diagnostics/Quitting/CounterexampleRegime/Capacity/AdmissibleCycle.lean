/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime
import UniformEquilibrium.Quitting.Bellman.Finite.PositiveAdmissibleCycle

/-!
# Positive admissible cycles against the counterexample regime

The generic positive-cycle and positive-return consumers live in
`UniformEquilibrium.Quitting.Bellman.Finite.PositiveAdmissibleCycle`.  This
diagnostic adapter retains the regime-specific zero-cycle consequence.
-/

noncomputable section

namespace GameTheory

open Math.ChargedPathBudget

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingCounterexampleRegime

private abbrev AdmissibleRelation :=
  quittingPunishmentFloorAdmissibleChargedRelation reward

/-- Every closed path in the full floor-admissible predecessor relation has
zero charge inside a counterexample regime. -/
theorem admissible_cycle_chargeSum_eq_zero
    (regime : QuittingCounterexampleRegime reward)
    {state : QuittingPunishmentFloorAdmissibleState reward}
    (cycle : AdmissibleRelation.Path state state) :
    cycle.chargeSum = 0 := by
  have hbudget : AdmissibleRelation.HasFiniteBudget :=
    quittingPunishmentFloorAdmissible_hasFiniteBudget_of_finitePrefixChargeBound
      regime.prefixCharge_le
  have hnotPositive : ¬ 0 < cycle.chargeSum := by
    intro hpositive
    exact AdmissibleRelation.not_hasFiniteBudget_of_positive_cycle
      cycle hpositive hbudget
  exact le_antisymm (le_of_not_gt hnotPositive) cycle.chargeSum_nonneg

end QuittingCounterexampleRegime

end GameTheory

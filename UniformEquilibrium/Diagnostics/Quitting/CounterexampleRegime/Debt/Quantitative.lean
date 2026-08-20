/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime
import UniformEquilibrium.Quitting.Debt.Dynamic.OptimizedDynamicDebtBounds

/-!
# Quantitative restrictions on the quitting counterexample regime

The terminal exploitability gap of a counterexample regime bounds every
optimized exact-debt value from below and the largest positive singleton debt
cap from above. It also survives in a specific coordinate of a projective
exact-debt tail with a summable opponent clock.
-/

noncomputable section

namespace GameTheory

open Filter

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingCounterexampleRegime

/-- The regime's terminal margin is below every optimized exact-debt value. -/
theorem terminalGap_le_finiteMinMaxDynamicDebt
    (regime : QuittingCounterexampleRegime reward) (cutoff : ℕ) :
    regime.terminalGap ≤
      @quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt ι _ _
        regime.nonempty_players reward cutoff :=
  terminalExploitabilityGap_le_finiteMinMaxDynamicDebt
    reward regime.terminalExploitability cutoff

/-- The regime's terminal margin is below the limiting exact-debt
obstruction. -/
theorem terminalGap_le_iInf_minMaxDynamicDebt
    (regime : QuittingCounterexampleRegime reward) :
    regime.terminalGap ≤ ⨅ cutoff : ℕ,
      @quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt ι _ _
        regime.nonempty_players reward cutoff :=
  terminalExploitabilityGap_le_iInf_finiteMinMaxDynamicDebt
    reward regime.terminalExploitability

/-- The limiting optimized exact-debt obstruction is positive. -/
theorem iInf_minMaxDynamicDebt_pos_of_terminalGap
    (regime : QuittingCounterexampleRegime reward) :
    0 < ⨅ cutoff : ℕ,
      @quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt ι _ _
        regime.nonempty_players reward cutoff :=
  regime.terminalGap_pos.trans_le
    regime.terminalGap_le_iInf_minMaxDynamicDebt

/-- The terminal margin is bounded by the largest positive singleton reward. -/
theorem terminalGap_le_maxPositiveSingletonDebtCap
    (regime : QuittingCounterexampleRegime reward) :
    regime.terminalGap ≤ @quittingMaxPositiveSingletonDebtCap ι _
      regime.nonempty_players reward := by
  letI : Nonempty ι := regime.nonempty_players
  exact (regime.terminalGap_le_finiteMinMaxDynamicDebt 0).trans
    (quittingFiniteMinMaxDynamicDebt_le_maxPositiveSingletonDebtCap reward 0)

/-- A counterexample regime forces a player to have a strictly positive own
reward at their singleton quitting terminal. -/
theorem maxPositiveSingletonDebtCap_pos
    (regime : QuittingCounterexampleRegime reward) :
    0 < @quittingMaxPositiveSingletonDebtCap ι _
      regime.nonempty_players reward := by
  letI : Nonempty ι := regime.nonempty_players
  exact regime.terminalGap_pos.trans_le
    regime.terminalGap_le_maxPositiveSingletonDebtCap

/-- The regime has a projective exact-debt tail with one owner whose initial
debt is at least the terminal exploitability gap and whose opponent clock is
summable. -/
theorem exists_terminalGapDynamicDebtTail
    (regime : QuittingCounterexampleRegime reward) :
    ∃ (limit : ℕ → QuittingDebtPoint ι) (subseq : ℕ → ℕ) (who : ι),
      StrictMono subseq ∧
      Tendsto
        ((fun cutoff ↦ @quittingFiniteMinMaxDynamicDebtTail ι _ _
            regime.nonempty_players reward cutoff) ∘ subseq)
          atTop (nhds limit) ∧
      (∀ time, limit time ∈ quittingDebtBox reward) ∧
      (∀ time, IsQuittingDynamicDebtEdge reward
        (limit time) (limit (time + 1))) ∧
      regime.terminalGap ≤ (limit 0).2 who ∧
      Summable (quittingOpponentClockCharge
        (quittingDynamicDebtTailRoots limit) who) := by
  letI : Nonempty ι := regime.nonempty_players
  exact exists_projectiveDynamicDebtTail_of_pos_le_iInf_minMax
    reward regime.terminalGap_pos
      regime.terminalGap_le_iInf_minMaxDynamicDebt

end QuittingCounterexampleRegime

end GameTheory

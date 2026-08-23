/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityWitness
import UniformEquilibrium.Quitting.Debt.Dynamic.OptimizedDynamicDebtBounds

/-!
# Quantitative restrictions on the quitting terminal exploitability witness

The terminal exploitability gap of a terminal exploitability witness bounds every
optimized exact-debt value from below and the largest positive singleton debt
cap from above. It also survives in a specific coordinate of a projective
exact-debt tail with a summable opponent clock.
-/

noncomputable section

namespace GameTheory

open Filter

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingTerminalExploitabilityWitness

/-- The regime's terminal margin is below every optimized exact-debt value. -/
theorem terminalGap_le_finiteMinMaxDynamicDebt
    (witness : QuittingTerminalExploitabilityWitness reward) (cutoff : ℕ) :
    witness.terminalGap ≤
      @quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt ι _ _
        witness.nonempty_players reward cutoff :=
  terminalExploitabilityGap_le_finiteMinMaxDynamicDebt
    reward witness.terminalExploitability cutoff

/-- The regime's terminal margin is below the limiting exact-debt
obstruction. -/
theorem terminalGap_le_iInf_minMaxDynamicDebt
    (witness : QuittingTerminalExploitabilityWitness reward) :
    witness.terminalGap ≤ ⨅ cutoff : ℕ,
      @quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt ι _ _
        witness.nonempty_players reward cutoff :=
  terminalExploitabilityGap_le_iInf_finiteMinMaxDynamicDebt
    reward witness.terminalExploitability

/-- The limiting optimized exact-debt obstruction is positive. -/
theorem iInf_minMaxDynamicDebt_pos_of_terminalGap
    (witness : QuittingTerminalExploitabilityWitness reward) :
    0 < ⨅ cutoff : ℕ,
      @quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt ι _ _
        witness.nonempty_players reward cutoff :=
  witness.terminalGap_pos.trans_le
    witness.terminalGap_le_iInf_minMaxDynamicDebt

/-- The terminal margin is bounded by the largest positive singleton reward. -/
theorem terminalGap_le_maxPositiveSingletonDebtCap
    (witness : QuittingTerminalExploitabilityWitness reward) :
    witness.terminalGap ≤ @quittingMaxPositiveSingletonDebtCap ι _
      witness.nonempty_players reward := by
  letI : Nonempty ι := witness.nonempty_players
  exact (witness.terminalGap_le_finiteMinMaxDynamicDebt 0).trans
    (quittingFiniteMinMaxDynamicDebt_le_maxPositiveSingletonDebtCap reward 0)

/-- A terminal exploitability witness forces a player to have a strictly positive own
reward at their singleton quitting terminal. -/
theorem maxPositiveSingletonDebtCap_pos
    (witness : QuittingTerminalExploitabilityWitness reward) :
    0 < @quittingMaxPositiveSingletonDebtCap ι _
      witness.nonempty_players reward := by
  letI : Nonempty ι := witness.nonempty_players
  exact witness.terminalGap_pos.trans_le
    witness.terminalGap_le_maxPositiveSingletonDebtCap

/-- The regime has a projective exact-debt tail with one owner whose initial
debt is at least the terminal exploitability gap and whose opponent clock is
summable. -/
theorem exists_terminalGapDynamicDebtTail
    (witness : QuittingTerminalExploitabilityWitness reward) :
    ∃ (limit : ℕ → QuittingDebtPoint ι) (subseq : ℕ → ℕ) (who : ι),
      StrictMono subseq ∧
      Tendsto
        ((fun cutoff ↦ @quittingFiniteMinMaxDynamicDebtTail ι _ _
            witness.nonempty_players reward cutoff) ∘ subseq)
          atTop (nhds limit) ∧
      (∀ time, limit time ∈ quittingDebtBox reward) ∧
      (∀ time, IsQuittingDynamicDebtEdge reward
        (limit time) (limit (time + 1))) ∧
      witness.terminalGap ≤ (limit 0).2 who ∧
      Summable (quittingOpponentClockCharge
        (quittingDynamicDebtTailRoots limit) who) := by
  letI : Nonempty ι := witness.nonempty_players
  exact exists_projectiveDynamicDebtTail_of_pos_le_iInf_minMax
    reward witness.terminalGap_pos
      witness.terminalGap_le_iInf_minMaxDynamicDebt

end QuittingTerminalExploitabilityWitness

end GameTheory

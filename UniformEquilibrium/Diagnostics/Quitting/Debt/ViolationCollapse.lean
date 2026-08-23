/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Debt.PunishmentFloorTailBridge
import UniformEquilibrium.Quitting.Debt.Dynamic.PunishmentFloorViolation

/-!
# Violation collapse for the counterexample tail

The production floor-violation theorem makes any boxed exact-debt tail with
a floor violation and a positive debt coordinate summably absorbing. Applied
to the optimized counterexample tail, it eliminates the violation horn of the
tail/prefix alternative and forces summable joint absorption.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## The regime's extracted tail has summable absorption -/

namespace QuittingTerminalExploitabilityWitness

/-- **Unconditional collapse of the carrier alternative.**  The projectively
extracted optimized exact-debt tail of a terminal exploitability witness has summable
joint absorption charge, unconditionally.

The regime's carrier alternative offers either summable joint absorption or
an eventual coordinatewise punishment-floor violation; but the extracted tail
carries an owner whose initial debt is at least the positive terminal gap, so
the violation horn collapses onto the summable horn by the violation-collapse
theorem.  In particular the extracted roots converge coordinatewise to
all-Continue. -/
theorem exists_terminalGapDynamicDebtTail_summableAbsorption
    (witness : QuittingTerminalExploitabilityWitness reward) :
    ∃ (limit : ℕ → QuittingDebtPoint ι) (subseq : ℕ → ℕ) (who : ι),
      StrictMono subseq ∧
      Tendsto
        ((fun cutoff ↦ @quittingFiniteMinMaxDynamicDebtTail
          ι _ _ witness.nonempty_players reward cutoff) ∘
          subseq) atTop (nhds limit) ∧
      (∀ time, limit time ∈ quittingDebtBox reward) ∧
      (∀ time, IsQuittingDynamicDebtEdge reward
        (limit time) (limit (time + 1))) ∧
      witness.terminalGap ≤ (limit 0).2 who ∧
      Summable (quittingOpponentClockCharge
        (quittingDynamicDebtTailRoots limit) who) ∧
      Summable (quittingDynamicDebtTailAbsorptionCharge limit) := by
  letI : Nonempty ι := witness.nonempty_players
  obtain ⟨limit, subseq, who, hsubseq, hlimit, hbox, hedge, hdebt, hclock⟩ :=
    witness.exists_terminalGapDynamicDebtTail
  refine ⟨limit, subseq, who, hsubseq, hlimit, hbox, hedge, hdebt, hclock, ?_⟩
  rcases witness.summable_dynamicDebtTailAbsorptionCharge_or_eventually_floorViolation
      limit hbox hedge with hsummable | hviolation
  · exact hsummable
  · obtain ⟨start, hstart⟩ := hviolation
    obtain ⟨player, hplayer⟩ := hstart start le_rfl
    exact
      summable_dynamicDebtTailAbsorptionCharge_of_floorViolation_of_positiveDebt
        limit hbox hedge ⟨start, player, hplayer⟩
        ⟨0, who, lt_of_lt_of_le witness.terminalGap_pos hdebt⟩

end QuittingTerminalExploitabilityWitness

end GameTheory

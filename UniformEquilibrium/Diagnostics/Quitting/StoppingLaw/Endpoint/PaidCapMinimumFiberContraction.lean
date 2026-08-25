/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.PaidCapPortExactTrichotomy

/-!
# Minimum-fiber contraction for paid cap ports

The motion estimate and absorption budget of a paid cap port combine with
global minimality to bound its cap displacement by the source's excess total
debt.  On the exact minimum fiber the stronger absorption budget itself
vanishes, so every selected root is all Continue and the port is literally
inert.  No terminal-exploitability or equilibrium-nonexistence hypothesis is
needed.

This is a quantitative boundary contraction, not a regeneration theorem.
It does not realize the limiting carrier point as a behavioral profile or
make strict real-valued debt descent well founded.
-/

noncomputable section

namespace GameTheory

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

namespace QuittingPaidCapLiftedSource

variable (source : QuittingPaidCapLiftedSource reward)

/-- Complete cap-root absorption is paid by the source's total-debt excess
above the global minimum. -/
theorem minimum_mul_totalAbsorption_le_excess
    (port : source.SummablePort) :
    quittingTerminalSemanticDebtSum source.minimum *
          source.totalAbsorption ≤
      source.initialDebt -
        quittingTerminalSemanticDebtSum source.minimum := by
  have hcharge := source.minimum_mul_totalAbsorption_le_debtDrop port
  have hlimitLower :
      quittingTerminalSemanticDebtSum source.minimum ≤
        quittingTerminalSemanticDebtSum port.semanticPort.limit :=
    source.minimum_le port.semanticPort.limit port.semanticPort.limit_mem
  exact hcharge.trans (sub_le_sub_left hlimitLower source.initialDebt)

/-- Division by the positive minimum debt gives a direct complete-absorption
bound on neighborhoods of the minimum fiber. -/
theorem totalAbsorption_le_excess_div_minimum
    (port : source.SummablePort) :
    source.totalAbsorption ≤
      (source.initialDebt -
          quittingTerminalSemanticDebtSum source.minimum) /
        quittingTerminalSemanticDebtSum source.minimum := by
  apply (le_div_iff₀ source.minimum_pos).2
  simpa [mul_comm] using source.minimum_mul_totalAbsorption_le_excess port

/-- Cap displacement is paid by the source's total-debt excess above the
global minimum.  This form avoids division by the positive minimum debt. -/
theorem minimum_mul_capDisplacement_le_twoRewardBound_mul_excess
    (port : source.SummablePort) :
    quittingTerminalSemanticDebtSum source.minimum *
          source.capDisplacement port ≤
      2 * quittingRewardBound reward *
        (source.initialDebt -
          quittingTerminalSemanticDebtSum source.minimum) := by
  have hmotion := source.capDisplacement_le_two_mul_totalAbsorption port
  have hscaledMotion :
      quittingTerminalSemanticDebtSum source.minimum *
            source.capDisplacement port ≤
        quittingTerminalSemanticDebtSum source.minimum *
          (2 * quittingRewardBound reward * source.totalAbsorption) :=
    mul_le_mul_of_nonneg_left hmotion source.minimum_pos.le
  have hcharge := source.minimum_mul_totalAbsorption_le_debtDrop port
  have hlimitLower :
      quittingTerminalSemanticDebtSum source.minimum ≤
        quittingTerminalSemanticDebtSum port.semanticPort.limit :=
    source.minimum_le port.semanticPort.limit port.semanticPort.limit_mem
  have hdrop :
      source.initialDebt -
          quittingTerminalSemanticDebtSum port.semanticPort.limit ≤
        source.initialDebt -
          quittingTerminalSemanticDebtSum source.minimum :=
    sub_le_sub_left hlimitLower source.initialDebt
  calc
    quittingTerminalSemanticDebtSum source.minimum *
          source.capDisplacement port ≤
        quittingTerminalSemanticDebtSum source.minimum *
          (2 * quittingRewardBound reward * source.totalAbsorption) :=
      hscaledMotion
    _ = 2 * quittingRewardBound reward *
          (quittingTerminalSemanticDebtSum source.minimum *
            source.totalAbsorption) := by ring
    _ ≤ 2 * quittingRewardBound reward *
          (source.initialDebt -
            quittingTerminalSemanticDebtSum port.semanticPort.limit) :=
      mul_le_mul_of_nonneg_left hcharge
        (mul_nonneg (by norm_num) (quittingRewardBound_nonneg reward))
    _ ≤ 2 * quittingRewardBound reward *
          (source.initialDebt -
            quittingTerminalSemanticDebtSum source.minimum) :=
      mul_le_mul_of_nonneg_left hdrop
        (mul_nonneg (by norm_num) (quittingRewardBound_nonneg reward))

/-- Division by the positive minimum debt gives the direct displacement
bound used on neighborhoods of the minimum fiber. -/
theorem capDisplacement_le_twoRewardBound_mul_excess_div_minimum
    (port : source.SummablePort) :
    source.capDisplacement port ≤
      (2 * quittingRewardBound reward *
          (source.initialDebt -
            quittingTerminalSemanticDebtSum source.minimum)) /
        quittingTerminalSemanticDebtSum source.minimum := by
  apply (le_div_iff₀ source.minimum_pos).2
  simpa [mul_comm] using
    source.minimum_mul_capDisplacement_le_twoRewardBound_mul_excess port

/-- Every cap port based at an actual point of the global minimum-debt fiber
has zero cap displacement.  No exploitability or equilibrium assumption is
needed. -/
theorem capDisplacement_eq_zero_of_initialDebt_eq_minimum
    (port : source.SummablePort)
    (hfiber : source.initialDebt =
      quittingTerminalSemanticDebtSum source.minimum) :
    source.capDisplacement port = 0 := by
  have hbound :=
    source.minimum_mul_capDisplacement_le_twoRewardBound_mul_excess port
  rw [hfiber, sub_self, mul_zero] at hbound
  have hdisplacement := source.capDisplacement_nonneg port
  nlinarith [source.minimum_pos]

/-- The complete absorption budget vanishes at an actual point of the global
minimum-debt fiber.  This is stronger than excluding the positive-charge arm
through a terminal exploitability witness. -/
theorem totalAbsorption_eq_zero_of_initialDebt_eq_minimum
    (port : source.SummablePort)
    (hfiber : source.initialDebt =
      quittingTerminalSemanticDebtSum source.minimum) :
    source.totalAbsorption = 0 := by
  have hcharge := source.minimum_mul_totalAbsorption_le_excess port
  rw [hfiber, sub_self] at hcharge
  have habsorption := source.totalAbsorption_nonneg
  nlinarith [source.minimum_pos]

/-- Every paid cap port based at an actual point of the global minimum-debt
fiber is literally inert.  No terminal gap or equilibrium-nonexistence
hypothesis is needed. -/
theorem inertStall_of_initialDebt_eq_minimum
    (port : source.SummablePort)
    (hfiber : source.initialDebt =
      quittingTerminalSemanticDebtSum source.minimum) :
    InertStall source port :=
  source.inertStall_of_totalAbsorption_eq_zero port
    (source.totalAbsorption_eq_zero_of_initialDebt_eq_minimum port hfiber)

end QuittingPaidCapLiftedSource

end GameTheory

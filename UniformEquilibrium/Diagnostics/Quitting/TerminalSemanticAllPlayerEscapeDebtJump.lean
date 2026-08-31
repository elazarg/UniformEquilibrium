/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAllPlayerEscapeAccount

/-!
# Terminal-law escape and the total-debt jump

The first terminal-law escape account has an exact total-debt identity.  The
debt of the reconstructed marginal-law profile minus the target debt equals
the escaped social reward moment minus the total target-to-reconstructed cap
drop.  This is an oriented equality, not a sign, minimum, attainment, terminal
Nash, Fin4, downstream-consumer, or uniform-equilibrium result.
-/

noncomputable section

namespace GameTheory

open Filter MeasureTheory Set StochasticGame
open _root_.Math.Probability _root_.Math.ProbabilityMassFunction
open scoped BigOperators ENNReal Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

namespace QuittingTerminalSemanticEscapeAccount

omit [Nontrivial ι] in
/-- The reconstructed pair's debt change is exactly escaped social reward
moment minus the sum of target-to-reconstructed cap drops.  This is an
oriented algebraic account; it asserts no sign for either term. -/
theorem debtSum_sub_target_eq_escapeSocialReward_sub_capDropSum
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {target : QuittingTerminalSemanticPair ι}
    {selected : QuittingTerminalSemanticSelectedLawLimit reward target}
    (account : QuittingTerminalSemanticEscapeAccount reward target selected) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingCompactStoppingLawProfile reward selected.laws)) -
        quittingTerminalSemanticDebtSum target =
      (∑ terminal, quittingTerminalEscapeMass reward selected.laws
          account.mass terminal * ∑ player, reward terminal player) -
        ∑ player, (target.2 player -
          quittingContinuationBestResponseValue reward
            (quittingCompactStoppingLawProfile reward selected.laws) player) := by
  let profile := quittingCompactStoppingLawProfile reward selected.laws
  let escape := fun terminal =>
    quittingTerminalEscapeMass reward selected.laws account.mass terminal
  unfold quittingTerminalSemanticDebtSum quittingTerminalSemanticDebt
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ player,
        (((quittingTerminalSemanticPair reward profile).2 player -
            (quittingTerminalSemanticPair reward profile).1 player) -
          (target.2 player - target.1 player))) =
        ∑ player, (((target.1 player -
            quittingTerminalPayoff reward profile player) -
          (target.2 player -
            quittingContinuationBestResponseValue reward profile player))) := by
      apply Finset.sum_congr rfl
      intro player _
      simp only [quittingTerminalSemanticPair]
      ring
    _ = ∑ player, (((∑ terminal, escape terminal * reward terminal player) -
          (target.2 player -
            quittingContinuationBestResponseValue reward profile player))) := by
      apply Finset.sum_congr rfl
      intro player _
      rw [← account.escapedRewardMoment_eq player]
    _ = (∑ player, ∑ terminal,
          escape terminal * reward terminal player) -
        ∑ player, (target.2 player -
          quittingContinuationBestResponseValue reward profile player) := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ terminal, escape terminal * ∑ player, reward terminal player) -
        ∑ player, (target.2 player -
          quittingContinuationBestResponseValue reward profile player) := by
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro terminal _
      exact (Finset.mul_sum Finset.univ
        (fun player => reward terminal player) (escape terminal)).symm
    _ = _ := by rfl

end QuittingTerminalSemanticEscapeAccount

end GameTheory

/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Debt.Dynamic.CyclePinnedDebt

/-!
# Terminal-continuation mismatch under endpoint rebasing

An arbitrary terminal continuation uses mismatch against that endpoint, not
the fixed positive-singleton zero-boundary debt cap.  The canonical upper box
face erases this mismatch, and a concrete realized cyclic continuation can do
the same even when the zero endpoint has positive mismatch.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The constant reward-bound endpoint dominates every singleton own reward,
so endpoint-rebased terminal mismatch is identically zero there. -/
theorem quittingTerminalContinuationMismatch_rewardBound_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingTerminalContinuationMismatch reward
        (fun _ ↦ quittingRewardBound reward) who = 0 := by
  apply quittingTerminalContinuationMismatch_eq_zero_of_singleton_le
  intro owner
  exact le_trans (le_abs_self _)
    (abs_reward_le_quittingRewardBound reward
      (quittingSingletonTerminal owner) owner)

/-- Consequently the aggregate endpoint-rebased terminal debt at the upper
box face is zero, regardless of the positive zero-boundary debt cap. -/
theorem sum_quittingTerminalContinuationMismatch_rewardBound_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (∑ who, quittingTerminalContinuationMismatch reward
      (fun _ ↦ quittingRewardBound reward) who) = 0 := by
  apply Finset.sum_eq_zero
  intro who _
  exact quittingTerminalContinuationMismatch_rewardBound_eq_zero reward who

namespace QuittingCapacityNearMaximizerRebaseRegression

open QuittingBoundedSurgeryDescentCounterexample

/-- A concrete exact rebasing regression.  In the bounded-surgery table the
zero endpoint carries strictly positive terminal mismatch for player `false`,
while the realized absorbing stationary continuation carries zero mismatch.
Thus even rebasing to an actual cyclic continuation need not preserve the
positive zero-boundary debt. -/
theorem realizedEndpoint_can_erase_positive_zeroBoundaryMismatch
    (a : ℝ) (ha0 : 0 < a) :
    ∃ terminal : Payoff Bool,
      IsQuittingCyclicContinuation
          (QuittingBoundedSurgeryDescentCounterexample.reward a) terminal ∧
        0 < quittingTerminalContinuationMismatch
          (QuittingBoundedSurgeryDescentCounterexample.reward a) 0 false ∧
        quittingTerminalContinuationMismatch
          (QuittingBoundedSurgeryDescentCounterexample.reward a) terminal false = 0 := by
  refine ⟨stationaryValue a, stationaryValue_isQuittingCyclicContinuation a ha0,
    ?_, quittingTerminalContinuationMismatch_stationaryValue a false⟩
  rw [quittingTerminalContinuationMismatch_zero,
    positiveSingletonDebtCap_false a ha0]
  exact ha0

end QuittingCapacityNearMaximizerRebaseRegression

end GameTheory

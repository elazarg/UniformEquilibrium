/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.ExactSuccessorClosure

/-! # A payoff-level exact self-loop with no live terminal completion -/

noncomputable section

namespace GameTheory.AllMinusOneLiveBoundary

open GameTheory StochasticGame Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def reward (_ : {S : Finset ι // S.Nonempty}) : Payoff ι := fun _ => -1

def phantom : Payoff ι := fun _ => 1

omit [Nonempty ι] in
theorem allContinue_successor :
    quittingRootSuccessorPayoff (reward (ι := ι)) (phantom (ι := ι))
      quittingAllContinueRoot = phantom := by
  funext who
  rw [quittingRootSuccessorPayoff_eq_endpointMix]
  simp [quittingAllContinueRoot, phantom]

omit [Nonempty ι] in
theorem allContinue_exactRootNash :
    IsεQuittingRootNash (reward (ι := ι)) (phantom (ι := ι)) 0
      quittingAllContinueRoot := by
  rw [isZeroQuittingRootNash_allContinue_iff_singleton_le]
  intro who
  simp [reward, phantom]

omit [DecidableEq ι] [Nonempty ι] in
theorem terminalPayoff_nonpos
    (profile : (quittingGame (reward (ι := ι))).BehaviorProfile) (who : ι) :
    quittingTerminalPayoff (reward (ι := ι)) profile who ≤ 0 := by
  unfold quittingTerminalPayoff
  apply Finset.sum_nonpos
  intro terminal _
  exact mul_nonpos_of_nonneg_of_nonpos
    (quittingAbsorbedMassLimit_nonneg (reward (ι := ι)) profile terminal)
    (by simp [reward])

theorem phantom_not_uniformEquilibriumPayoff :
    ¬ (quittingGame (reward (ι := ι))).IsUniformEquilibriumPayoff none
      (phantom (ι := ι)) := by
  intro huniform
  obtain ⟨profile, _, hclose⟩ :=
    exists_terminalNash_terminalPayoff_close_of_isUniformEquilibriumPayoff
      (reward (ι := ι)) (phantom (ι := ι)) huniform
      (by norm_num : (0 : ℝ) < 1 / 2)
  let who : ι := Classical.choice inferInstance
  have hnonpos := terminalPayoff_nonpos profile who
  have := hclose who
  simp [phantom] at this
  have hlower := (abs_le.mp this).1
  linarith

end GameTheory.AllMinusOneLiveBoundary

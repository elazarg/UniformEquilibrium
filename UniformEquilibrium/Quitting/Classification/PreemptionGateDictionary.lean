/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.PreemptionCycle
import UniformEquilibrium.Quitting.Classification.LCP.NormalCore

/-!
# The preemption/gate-matrix dictionary

The strict solo-preemption relation and the LCP gate's canonical normalized
solo matrix encode the same inequalities.  A player `other` preempts `owner`
at margin `gap` exactly when the gate entry at recipient `other` and quitter
`owner` is at most `-gap`.

Consequently, every vertex of a nonnegative-margin solo-preemption cycle lies
in the normal core.  The in-cycle predecessor supplies a permanent
distinct witness at every normal-layer deletion.
-/

noncomputable section

namespace GameTheory

open QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The canonical gate entry is the corresponding solo-reward difference. -/
theorem normalizedSoloMatrix_eq_soloReward_sub
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who owner : ι) :
    normalizedSoloMatrix reward who owner =
      quittingSoloReward reward owner who - quittingSoloReward reward who who := by
  unfold normalizedSoloMatrix
  rw [normalized_singletonMatrix_eq_quittingSingletonMatrix]
  rfl

/-- Strict solo preemption at margin `gap` is exactly a gate entry at most
`-gap` at recipient `other` and quitter `owner`. -/
theorem quittingSoloPreempts_iff_normalizedSoloMatrix_le_neg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (gap : ℝ) (owner other : ι) :
    QuittingSoloPreempts reward gap owner other ↔
      other ≠ owner ∧ normalizedSoloMatrix reward other owner ≤ -gap := by
  rw [normalizedSoloMatrix_eq_soloReward_sub]
  unfold QuittingSoloPreempts
  constructor
  · rintro ⟨hne, hle⟩
    exact ⟨hne, by linarith⟩
  · rintro ⟨hne, hle⟩
    exact ⟨hne, by linarith⟩

namespace QuittingSoloPreemptionCycle

/-- Along a strict preemption cycle, every consecutive gate entry is at most
`-gap`. -/
theorem normalizedSoloMatrix_le_neg
    {gap : ℝ} (cycle : QuittingSoloPreemptionCycle reward gap) (time : ℕ) :
    normalizedSoloMatrix reward (cycle.vertex (time + 1)) (cycle.vertex time) ≤
      -gap :=
  ((quittingSoloPreempts_iff_normalizedSoloMatrix_le_neg reward gap
      (cycle.vertex time) (cycle.vertex (time + 1))).1 (cycle.edge time)).2

/-- Every vertex of a nonnegative-margin strict preemption cycle survives all
normal-layer deletions. -/
theorem vertex_mem_normalCore
    {gap : ℝ} (hgap : 0 ≤ gap)
    (cycle : QuittingSoloPreemptionCycle reward gap) (time : ℕ) :
    cycle.vertex time ∈ normalCore (normalizedSoloMatrix reward) := by
  classical
  refine (mem_normalCore (normalizedSoloMatrix reward) (cycle.vertex time)).2
    fun layer => ?_
  induction layer generalizing time with
  | zero => simp [normalLayer]
  | succ layer ih =>
      have hperiod := cycle.period_pos
      set previous := time + cycle.period - 1 with hprevious
      have hsucc : previous + 1 = time + cycle.period := by omega
      have hvertex : cycle.vertex (previous + 1) = cycle.vertex time := by
        rw [hsucc, cycle.vertex_periodic]
      have hedge := cycle.edge previous
      have hentry : normalizedSoloMatrix reward (cycle.vertex time)
          (cycle.vertex previous) ≤ 0 := by
        have hneg := cycle.normalizedSoloMatrix_le_neg previous
        rw [hvertex] at hneg
        linarith
      have hne : cycle.vertex previous ≠ cycle.vertex time := by
        rw [← hvertex]
        exact hedge.1.symm
      exact (mem_normalLayer_succ (normalizedSoloMatrix reward) layer
          (cycle.vertex time)).2
        ⟨ih time, cycle.vertex previous, ih previous, hne, hentry⟩

end QuittingSoloPreemptionCycle

end GameTheory

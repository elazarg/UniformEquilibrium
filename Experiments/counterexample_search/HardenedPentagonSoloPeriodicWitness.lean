/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.AnchoredSoloPeriodic
import Experiments.counterexample_search.HardenedPentagonCyclicEquilibrium

/-!
# The hardened pentagon is an exact anchored solo-periodic profile

`GameTheory.IsExactAnchoredSoloPeriodic` is satisfied
by the period-five schedule `(0, 3, 1, 4, 2)` at constant hazard `1/2` on
`GameTheory.HardenedPentagonCyclicEquilibrium.hardenedReward`.

This is a bounded checked instance on one table.  It records that the class of
exact anchored solo-periodic profiles is inhabited, so that an infeasibility
statement for that class on a particular table is a statement about that
table.
-/

noncomputable section

namespace GameTheory

namespace HardenedPentagonCyclicEquilibrium

/-- The anchored cyclic on-path value of the pentagon schedule is the block's
own displayed value at every phase, not only at the start. -/
theorem quittingAnchoredCyclicOnPathValue_eq_phaseValue (phase : Fin 5) :
    quittingAnchoredCyclicOnPathValue hardenedReward schedule hazard
        hazard_nonneg hazard_le_one phase = phaseValue (Fin.castSucc phase) := by
  have hvalue := eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff_of_absorbing
    hardenedReward (quittingCyclicContinuationBlockCycle 4 hardenedBlock)
    (quittingCyclicContinuationBlockValue 4 hardenedBlock)
    (quittingCyclicContinuationBlock_policy hardenedReward target 4 hardenedBlock
      hardenedBlock_isQuittingCyclicContinuationBlock)
    (quittingCyclicContinuationBlock_prod_continueMass_lt_one hardenedReward target
      4 hardenedBlock hardenedBlock_isQuittingCyclicContinuationBlock)
  unfold quittingAnchoredCyclicOnPathValue
  rw [← quittingCyclicContinuationBlockCycle_eq_anchoredCyclicCycle, ← hvalue]
  rfl

/-- The displayed value one cyclic step ahead agrees with the block's
successor row: the last displayed row repeats the origin. -/
theorem phaseValue_castSucc_finRotate (phase : Fin 5) :
    phaseValue (Fin.castSucc (finRotate 5 phase)) = phaseValue (Fin.succ phase) := by
  fin_cases phase <;> rfl

/-- **The class of exact anchored solo-periodic profiles is inhabited.** -/
theorem hardened_isExactAnchoredSoloPeriodic :
    IsExactAnchoredSoloPeriodic hardenedReward schedule hazard
      hazard_nonneg hazard_le_one := by
  intro phase
  have hroot : quittingAnchoredCyclicCycle schedule hazard hazard_nonneg
      hazard_le_one phase = phaseRoot phase := rfl
  rw [hroot, quittingAnchoredCyclicOnPathValue_eq_phaseValue,
    phaseValue_castSucc_finRotate]
  exact phaseRoot_isZeroEndpointNash phase

theorem hazard_pos (phase : Fin 5) : 0 < hazard phase := by
  norm_num [hazard]

theorem hazard_lt_one (phase : Fin 5) : hazard phase < 1 := by
  norm_num [hazard]

/-- An exact anchored solo-periodic profile exists whose hazards are all
interior, on some four-or-more-player table. -/
theorem exists_interior_isExactAnchoredSoloPeriodic :
    ∃ (m : ℕ) (_ : NeZero m)
      (reward : {S : Finset RegularTournamentFiveSeed.Player // S.Nonempty} →
        Payoff RegularTournamentFiveSeed.Player)
      (w : Fin m → RegularTournamentFiveSeed.Player) (hazard : Fin m → ℝ)
      (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1),
      (∀ k, 0 < hazard k) ∧ (∀ k, hazard k < 1) ∧
        IsExactAnchoredSoloPeriodic reward w hazard h0 h1 :=
  ⟨5, inferInstance, hardenedReward, schedule, hazard, hazard_nonneg, hazard_le_one,
    hazard_pos, hazard_lt_one, hardened_isExactAnchoredSoloPeriodic⟩

end HardenedPentagonCyclicEquilibrium

end GameTheory

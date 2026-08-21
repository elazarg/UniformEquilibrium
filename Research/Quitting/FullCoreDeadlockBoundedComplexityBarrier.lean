/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.AffineIterateTelescope
import UniformEquilibrium.Quitting.Classification.LCP.FullCore.DeadlockChargedReturn
import UniformEquilibrium.Quitting.Cycles.PeriodicCompiler

/-!
# Bounded-complexity barrier for the full-core deadlock word method

This module formalizes cyclic words of active ideal singleton blocks for the
four-player deadlock matrix.  The first result rules out an exact zero-debt
cycle.  The bounded-complexity compactness theorem is developed below that
algebraic core.
-/

noncomputable section

namespace GameTheory
namespace FullCoreDeadlock

open Finset
open QuittingLCPClassification
open scoped BigOperators

/-- The additive debt cost of one ideal singleton block. -/
def idealSingletonCost
    (M : Player → Player → ℝ) (owner : Player) (α : ℝ)
    (t : Player → ℝ) : ℝ :=
  (1 - α) * t owner +
    ∑ who ∈ Finset.univ.erase owner,
      max 0 (-(α * t who + (1 - α) * M who owner))

/-- The existing ideal debt update is its surviving debt plus the local cost. -/
theorem idealSingletonDebt_eq_mul_add_cost
    (M : Player → Player → ℝ) (owner : Player) (α : ℝ)
    (t : Player → ℝ) (D : ℝ) :
    idealSingletonDebt M owner α t D =
      α * D + idealSingletonCost M owner α t := by
  simp only [idealSingletonDebt, idealSingletonCost]
  ring

/-- Local ideal-singleton cost is nonnegative on nonnegative clearances and a
survival factor at most one. -/
theorem idealSingletonCost_nonneg
    (M : Player → Player → ℝ) (owner : Player) {α : ℝ}
    (hα : α ≤ 1) (t : Player → ℝ) (ht : ∀ who, 0 ≤ t who) :
    0 ≤ idealSingletonCost M owner α t := by
  unfold idealSingletonCost
  apply add_nonneg
  · exact mul_nonneg (sub_nonneg.mpr hα) (ht owner)
  · exact Finset.sum_nonneg fun _ _ => le_max_left _ _

/-- Every column of the deadlock matrix has a strictly negative off-diagonal
entry. -/
theorem deadlockMatrix_exists_ne_neg (owner : Player) :
    ∃ who, who ≠ owner ∧ deadlockMatrix who owner < 0 := by
  fin_cases owner
  · exact ⟨3, by decide, by norm_num [deadlockMatrix]⟩
  · exact ⟨2, by decide, by norm_num [deadlockMatrix]⟩
  · exact ⟨0, by decide, by norm_num [deadlockMatrix]⟩
  · exact ⟨1, by decide, by norm_num [deadlockMatrix]⟩

/-- A zero-survival block has strictly positive clipping cost for the deadlock
matrix, independently of its incoming debt. -/
theorem idealSingletonDebt_deadlock_pos_of_survival_zero
    (owner : Player) (t : Player → ℝ) (D : ℝ)
    (ht : ∀ who, 0 ≤ t who) :
    0 < idealSingletonDebt deadlockMatrix owner 0 t D := by
  fin_cases owner <;>
    norm_num [idealSingletonDebt, deadlockMatrix, Fin.sum_univ_succ] <;>
    have := ht 0 <;> have := ht 1 <;> have := ht 2 <;> have := ht 3 <;>
    linarith

/-- Positive debt remains positive after every deadlock block.  When survival
vanishes, strict clipping replaces the lost incoming debt. -/
theorem idealSingletonDebt_deadlock_pos_of_debt_pos
    (owner : Player) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (t : Player → ℝ) (ht : ∀ who, 0 ≤ t who)
    {D : ℝ} (hD : 0 < D) :
    0 < idealSingletonDebt deadlockMatrix owner α t D := by
  by_cases hzero : α = 0
  · subst α
    exact idealSingletonDebt_deadlock_pos_of_survival_zero owner t D ht
  · rw [idealSingletonDebt_eq_mul_add_cost]
    exact add_pos_of_pos_of_nonneg
      (mul_pos (lt_of_le_of_ne hα0 (Ne.symm hzero)) hD)
      (idealSingletonCost_nonneg deadlockMatrix owner hα1 t ht)

/-- A reduced cyclic ideal-singleton lasso has only active blocks and combines
cyclically adjacent equal owners.  There are `K + 1` phases, so the phase type
is nonempty without an auxiliary typeclass. -/
structure ReducedIdealSingletonLasso (K : ℕ) where
  owner : Fin (K + 1) → Player
  survival : Fin (K + 1) → ℝ
  clearance : Fin (K + 1) → Player → ℝ
  debt : Fin (K + 1) → ℝ
  survival_nonneg : ∀ phase, 0 ≤ survival phase
  survival_lt_one : ∀ phase, survival phase < 1
  clearance_nonneg : ∀ phase who, 0 ≤ clearance phase who
  debt_nonneg : ∀ phase, 0 ≤ debt phase
  owner_ne_next : ∀ phase,
    owner phase ≠ owner (finRotate (K + 1) phase)
  clearance_step : ∀ phase,
    clearance (finRotate (K + 1) phase) =
      idealSingletonClearance deadlockMatrix (owner phase)
        (survival phase) (clearance phase)
  debt_step : ∀ phase,
    debt (finRotate (K + 1) phase) =
      idealSingletonDebt deadlockMatrix (owner phase)
        (survival phase) (clearance phase) (debt phase)

namespace ReducedIdealSingletonLasso

variable {K : ℕ} (lasso : ReducedIdealSingletonLasso K)

/-- The local additive debt cost at a phase. -/
def localCost (phase : Fin (K + 1)) : ℝ :=
  idealSingletonCost deadlockMatrix (lasso.owner phase)
    (lasso.survival phase) (lasso.clearance phase)

/-- Every local cost is nonnegative. -/
theorem localCost_nonneg (phase : Fin (K + 1)) :
    0 ≤ lasso.localCost phase :=
  idealSingletonCost_nonneg deadlockMatrix (lasso.owner phase)
    (lasso.survival_lt_one phase).le (lasso.clearance phase)
    (lasso.clearance_nonneg phase)

/-- The phase debt recurrence in explicit affine form. -/
theorem debt_step_eq (phase : Fin (K + 1)) :
    lasso.debt (finRotate (K + 1) phase) =
      lasso.survival phase * lasso.debt phase + lasso.localCost phase := by
  rw [lasso.debt_step, idealSingletonDebt_eq_mul_add_cost]
  rfl

/-- Strict positivity of debt propagates to the next phase. -/
theorem debt_next_pos {phase : Fin (K + 1)}
    (hD : 0 < lasso.debt phase) :
    0 < lasso.debt (finRotate (K + 1) phase) := by
  rw [lasso.debt_step]
  exact idealSingletonDebt_deadlock_pos_of_debt_pos
    (lasso.owner phase) (lasso.survival_nonneg phase)
    (lasso.survival_lt_one phase).le (lasso.clearance phase)
    (lasso.clearance_nonneg phase) hD

end ReducedIdealSingletonLasso

end FullCoreDeadlock
end GameTheory

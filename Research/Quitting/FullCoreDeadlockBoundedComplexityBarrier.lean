/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.AffineIterateTelescope
import MathUE.CyclicContraction
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
  · exact ⟨3, by decide, by norm_num [deadlockMatrix,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three]⟩
  · exact ⟨2, by decide, by norm_num [deadlockMatrix,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three]⟩
  · exact ⟨0, by decide, by norm_num [deadlockMatrix,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three]⟩
  · exact ⟨1, by decide, by norm_num [deadlockMatrix,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three]⟩

/-- Every off-diagonal entry of the deadlock matrix is nonzero. -/
theorem deadlockMatrix_ne_zero_of_ne {who owner : Player}
    (hne : who ≠ owner) :
    deadlockMatrix who owner ≠ 0 := by
  fin_cases who <;> fin_cases owner <;>
    norm_num [deadlockMatrix] at hne ⊢

/-- A zero-survival block has strictly positive clipping cost for the deadlock
matrix, independently of its incoming debt. -/
theorem idealSingletonDebt_deadlock_pos_of_survival_zero
    (owner : Player) (t : Player → ℝ) (D : ℝ)
    (ht : ∀ who, 0 ≤ t who) :
    0 < idealSingletonDebt deadlockMatrix owner 0 t D := by
  obtain ⟨who, hwho, hnegative⟩ := deadlockMatrix_exists_ne_neg owner
  have hmem : who ∈ Finset.univ.erase owner :=
    Finset.mem_erase.mpr ⟨hwho, Finset.mem_univ who⟩
  have hterm :
      0 < max 0 (-deadlockMatrix who owner) := by
    rw [max_eq_right (neg_nonneg.mpr hnegative.le)]
    exact neg_pos.mpr hnegative
  have hsum :
      max 0 (-deadlockMatrix who owner) ≤
        ∑ other ∈ Finset.univ.erase owner,
          max 0 (-deadlockMatrix other owner) := by
    exact Finset.single_le_sum
      (fun other _ => le_max_left (0 : ℝ) _) hmem
  rw [idealSingletonDebt_eq_mul_add_cost]
  simp only [zero_mul, zero_add, idealSingletonCost, sub_zero, one_mul]
  have howner := ht owner
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

/-- Algebraic core of the three-block descent.  The hypotheses are the
unclipped coordinate equations of the owner word `0, 3, 2`. -/
theorem deadlock_three_block_ratio_lt
    {α0 α3 α2 x A y1 y2 z1 z0 x' A' : ℝ}
    (hα0 : 0 < α0) (hα3 : 0 < α3) (hα2 : 0 < α2)
    (hA : 0 < A)
    (hbalance0 : α0 * A = 1 - α0)
    (hy1 : y1 = α0 * x + 2 * (1 - α0))
    (hy2 : y2 = 2 * (1 - α0))
    (hbalance3 : α3 * y2 = 1 - α3)
    (hz1 : z1 = α3 * y1 - 3 * (1 - α3))
    (hz1Nonneg : 0 ≤ z1)
    (hz0 : z0 = 3 * (1 - α3))
    (hbalance2 : α2 * z0 = 1 - α2)
    (hx' : x' = α2 * z1 + (1 - α2))
    (hA' : A' = 1 - α2) :
    x' / A' < x / A := by
  have hy1Form : y1 = α0 * (x + 2 * A) := by
    rw [hy1, ← hbalance0]
    ring
  have hy2Form : y2 = 2 * α0 * A := by
    rw [hy2, ← hbalance0]
    ring
  have hbalance3Form : 1 - α3 = 2 * α3 * α0 * A := by
    rw [← hbalance3, hy2Form]
    ring
  have hz1Form : z1 = α3 * α0 * (x - 4 * A) := by
    rw [hz1, hy1Form, hbalance3Form]
    ring
  have hz0Form : z0 = 6 * α3 * α0 * A := by
    rw [hz0, hbalance3Form]
    ring
  have hbalance2Form : 1 - α2 = 6 * α2 * α3 * α0 * A := by
    rw [← hbalance2, hz0Form]
    ring
  have hxForm : x' = α2 * α3 * α0 * (x + 2 * A) := by
    rw [hx', hz1Form, hbalance2Form]
    ring
  have hAForm : A' = 6 * α2 * α3 * α0 * A := by
    rw [hA', hbalance2Form]
  have hxLower : 4 * A ≤ x := by
    rw [hz1Form] at hz1Nonneg
    by_contra hnot
    have hlt : x - 4 * A < 0 := sub_neg.mpr (lt_of_not_ge hnot)
    have hfactor : 0 < α3 * α0 := mul_pos hα3 hα0
    have hneg := mul_neg_of_pos_of_neg hfactor hlt
    linarith
  have hratio : x' / A' = (x + 2 * A) / (6 * A) := by
    rw [hxForm, hAForm]
    field_simp [ne_of_gt hα0, ne_of_gt hα3, ne_of_gt hα2, ne_of_gt hA]
    ring
  rw [hratio]
  apply (div_lt_div_iff₀ (mul_pos (by norm_num) hA) hA).2
  nlinarith

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

/-- Positive debt persists along every finite segment of the cyclic orbit. -/
theorem debt_iterate_pos {phase : Fin (K + 1)}
    (hD : 0 < lasso.debt phase) :
    ∀ steps, 0 < lasso.debt ((finRotate (K + 1))^[steps] phase) := by
  intro steps
  induction steps with
  | zero => simpa using hD
  | succ steps ih =>
      rw [Function.iterate_succ_apply']
      exact lasso.debt_next_pos ih

/-- At a zero-debt phase the following phase also has zero debt.  Otherwise
strict positivity would persist around the remaining cycle and return to the
zero phase. -/
theorem debt_next_eq_zero_of_eq_zero {phase : Fin (K + 1)}
    (hzero : lasso.debt phase = 0) :
    lasso.debt (finRotate (K + 1) phase) = 0 := by
  apply le_antisymm
  · by_contra hnot
    have hnextPos : 0 < lasso.debt (finRotate (K + 1) phase) := by
      exact lt_of_not_ge hnot
    have hpersist := lasso.debt_iterate_pos hnextPos K
    have hreturn :
        ((finRotate (K + 1))^[K]) (finRotate (K + 1) phase) = phase := by
      simpa [Function.iterate_succ_apply] using
        (Math.iterate_finRotate_period phase)
    rw [hreturn, hzero] at hpersist
    exact (lt_irrefl 0) hpersist
  · exact lasso.debt_nonneg _

/-- Zero debt at one phase forces zero debt at every phase of the reduced
cycle. -/
theorem debt_eq_zero_of_debt_zero
    (hzero : lasso.debt (0 : Fin (K + 1)) = 0)
    (phase : Fin (K + 1)) :
    lasso.debt phase = 0 := by
  have horbit : ∀ steps,
      lasso.debt ((finRotate (K + 1))^[steps] (0 : Fin (K + 1))) = 0 := by
    intro steps
    induction steps with
    | zero => simpa using hzero
    | succ steps ih =>
        rw [Function.iterate_succ_apply']
        exact lasso.debt_next_eq_zero_of_eq_zero ih
  obtain ⟨steps, _, hreach⟩ :=
    Math.exists_iterate_finRotate_eq (0 : Fin (K + 1)) phase
  rw [← hreach]
  exact horbit steps

/-- Under a zero-debt cycle every local additive cost vanishes. -/
theorem localCost_eq_zero_of_debt_zero
    (hzero : lasso.debt (0 : Fin (K + 1)) = 0)
    (phase : Fin (K + 1)) :
    lasso.localCost phase = 0 := by
  have hsource := lasso.debt_eq_zero_of_debt_zero hzero phase
  have htarget := lasso.debt_eq_zero_of_debt_zero hzero
    (finRotate (K + 1) phase)
  rw [lasso.debt_step_eq, hsource, zero_mul, zero_add] at htarget
  exact htarget

/-- Under a zero-debt cycle every survival factor is strictly positive. -/
theorem survival_pos_of_debt_zero
    (hzero : lasso.debt (0 : Fin (K + 1)) = 0)
    (phase : Fin (K + 1)) :
    0 < lasso.survival phase := by
  have hnonneg := lasso.survival_nonneg phase
  apply lt_of_le_of_ne hnonneg
  intro hsurvival
  have htarget := lasso.debt_eq_zero_of_debt_zero hzero
    (finRotate (K + 1) phase)
  have hpositive := idealSingletonDebt_deadlock_pos_of_survival_zero
    (lasso.owner phase) (lasso.clearance phase) (lasso.debt phase)
    (lasso.clearance_nonneg phase)
  rw [← hsurvival, ← lasso.debt_step] at hpositive
  rw [htarget] at hpositive
  exact (lt_irrefl 0) hpositive

/-- At zero total debt, the active owner's incoming clearance vanishes. -/
theorem owner_clearance_eq_zero_of_debt_zero
    (hzero : lasso.debt (0 : Fin (K + 1)) = 0)
    (phase : Fin (K + 1)) :
    lasso.clearance phase (lasso.owner phase) = 0 := by
  have hcost := lasso.localCost_eq_zero_of_debt_zero hzero phase
  have hfactor : 0 < 1 - lasso.survival phase :=
    sub_pos.mpr (lasso.survival_lt_one phase)
  have hownerNonneg :
      0 ≤ (1 - lasso.survival phase) *
        lasso.clearance phase (lasso.owner phase) :=
    mul_nonneg hfactor.le (lasso.clearance_nonneg phase _)
  have hsumNonneg :
      0 ≤ ∑ who ∈ Finset.univ.erase (lasso.owner phase),
        max 0 (-(lasso.survival phase * lasso.clearance phase who +
          (1 - lasso.survival phase) *
            deadlockMatrix who (lasso.owner phase))) :=
    Finset.sum_nonneg fun _ _ => le_max_left _ _
  unfold localCost idealSingletonCost at hcost
  have hmul :
      (1 - lasso.survival phase) *
          lasso.clearance phase (lasso.owner phase) = 0 := by
    linarith
  rcases mul_eq_zero.mp hmul with hfactorZero | hclearance
  · exact (ne_of_gt hfactor hfactorZero).elim
  · exact hclearance

/-- At zero total debt no opponent coordinate is clipped by an active block. -/
theorem noClip_of_debt_zero
    (hzero : lasso.debt (0 : Fin (K + 1)) = 0)
    (phase : Fin (K + 1)) {who : Player}
    (hwho : who ≠ lasso.owner phase) :
    0 ≤ lasso.survival phase * lasso.clearance phase who +
      (1 - lasso.survival phase) *
        deadlockMatrix who (lasso.owner phase) := by
  let term := lasso.survival phase * lasso.clearance phase who +
    (1 - lasso.survival phase) * deadlockMatrix who (lasso.owner phase)
  let total := ∑ other ∈ Finset.univ.erase (lasso.owner phase),
    max 0 (-(lasso.survival phase * lasso.clearance phase other +
      (1 - lasso.survival phase) *
        deadlockMatrix other (lasso.owner phase)))
  have hcost := lasso.localCost_eq_zero_of_debt_zero hzero phase
  have hownerNonneg :
      0 ≤ (1 - lasso.survival phase) *
        lasso.clearance phase (lasso.owner phase) :=
    mul_nonneg (sub_nonneg.mpr (lasso.survival_lt_one phase).le)
      (lasso.clearance_nonneg phase _)
  have htotalNonneg : 0 ≤ total := by
    dsimp only [total]
    exact Finset.sum_nonneg fun _ _ => le_max_left _ _
  have htotalZero : total = 0 := by
    unfold localCost idealSingletonCost at hcost
    dsimp only [total]
    linarith
  have hmem : who ∈ Finset.univ.erase (lasso.owner phase) :=
    Finset.mem_erase.mpr ⟨hwho, Finset.mem_univ who⟩
  have htermNonneg : 0 ≤ max 0 (-term) := le_max_left _ _
  have htermLe : max 0 (-term) ≤ total := by
    dsimp only [term, total]
    exact Finset.single_le_sum
      (fun other _ => le_max_left (0 : ℝ) _) hmem
  have htermZero : max 0 (-term) = 0 := by
    apply le_antisymm
    · simpa [htotalZero] using htermLe
    · exact htermNonneg
  have hnegative : -term ≤ 0 := by
    calc
      -term ≤ max 0 (-term) := le_max_right _ _
      _ = 0 := htermZero
  dsimp only [term] at hnegative ⊢
  linarith

/-- With zero debt, every nonowner cap update is the unclipped affine
formula. -/
theorem clearance_step_eq_affine_of_ne
    (hzero : lasso.debt (0 : Fin (K + 1)) = 0)
    (phase : Fin (K + 1)) {who : Player}
    (hwho : who ≠ lasso.owner phase) :
    lasso.clearance (finRotate (K + 1) phase) who =
      lasso.survival phase * lasso.clearance phase who +
        (1 - lasso.survival phase) *
          deadlockMatrix who (lasso.owner phase) := by
  have hstep := congrFun (lasso.clearance_step phase) who
  have hnoClip := lasso.noClip_of_debt_zero hzero phase hwho
  simpa [idealSingletonClearance, hwho, max_eq_right hnoClip] using hstep

/-- An ideal singleton block leaves its owner's clearance unchanged. -/
theorem clearance_step_owner_eq (phase : Fin (K + 1)) :
    lasso.clearance (finRotate (K + 1) phase) (lasso.owner phase) =
      lasso.clearance phase (lasso.owner phase) := by
  have hstep := congrFun (lasso.clearance_step phase) (lasso.owner phase)
  simpa [idealSingletonClearance] using hstep

/-- Consecutive owners in a zero-debt cycle have the strict sign orientation
`M[next,current] < 0 < M[current,next]`. -/
theorem owner_transition_signs_of_debt_zero
    (hzero : lasso.debt (0 : Fin (K + 1)) = 0)
    (phase : Fin (K + 1)) :
    deadlockMatrix
        (lasso.owner (finRotate (K + 1) phase))
        (lasso.owner phase) < 0 ∧
      0 < deadlockMatrix
        (lasso.owner phase)
        (lasso.owner (finRotate (K + 1) phase)) := by
  let next := finRotate (K + 1) phase
  let currentOwner := lasso.owner phase
  let nextOwner := lasso.owner next
  have hownerNe : currentOwner ≠ nextOwner := by
    simpa only [currentOwner, nextOwner, next] using lasso.owner_ne_next phase
  have hnextNe : nextOwner ≠ currentOwner := hownerNe.symm
  have hcurrentZero :=
    lasso.owner_clearance_eq_zero_of_debt_zero hzero phase
  have hnextZero :=
    lasso.owner_clearance_eq_zero_of_debt_zero hzero next
  have hstepNext := congrFun (lasso.clearance_step phase) nextOwner
  have hnextEquation :
      lasso.survival phase * lasso.clearance phase nextOwner +
          (1 - lasso.survival phase) *
            deadlockMatrix nextOwner currentOwner = 0 := by
    change lasso.clearance next nextOwner = _ at hstepNext
    rw [hnextZero] at hstepNext
    simp only [idealSingletonClearance, hnextNe, if_false] at hstepNext
    have hnoClip := lasso.noClip_of_debt_zero hzero phase hnextNe
    change 0 ≤ lasso.survival phase * lasso.clearance phase nextOwner +
      (1 - lasso.survival phase) *
        deadlockMatrix nextOwner currentOwner at hnoClip
    have hle :
        lasso.survival phase * lasso.clearance phase nextOwner +
            (1 - lasso.survival phase) *
              deadlockMatrix nextOwner currentOwner ≤ 0 := by
      calc
        _ ≤ max 0
            (lasso.survival phase * lasso.clearance phase nextOwner +
              (1 - lasso.survival phase) *
                deadlockMatrix nextOwner currentOwner) := le_max_right _ _
        _ = 0 := hstepNext.symm
    exact le_antisymm hle hnoClip
  have hnegative : deadlockMatrix nextOwner currentOwner < 0 := by
    have hmatrixNe := deadlockMatrix_ne_zero_of_ne hnextNe
    by_contra hnot
    have hmatrixNonneg : 0 ≤ deadlockMatrix nextOwner currentOwner :=
      le_of_not_gt hnot
    have hmatrixPos : 0 < deadlockMatrix nextOwner currentOwner :=
      lt_of_le_of_ne hmatrixNonneg (Ne.symm hmatrixNe)
    have hfactor : 0 < 1 - lasso.survival phase :=
      sub_pos.mpr (lasso.survival_lt_one phase)
    have hrightPos := mul_pos hfactor hmatrixPos
    have hleftNonneg := mul_nonneg (lasso.survival_nonneg phase)
      (lasso.clearance_nonneg phase nextOwner)
    nlinarith
  have hstepCurrent := congrFun (lasso.clearance_step phase) currentOwner
  have hcurrentNextZero : lasso.clearance next currentOwner = 0 := by
    change lasso.clearance next currentOwner = _ at hstepCurrent
    simp only [idealSingletonClearance, if_pos rfl] at hstepCurrent
    rw [hstepCurrent, hcurrentZero]
  have hnoClipNext := lasso.noClip_of_debt_zero hzero next hownerNe
  change 0 ≤ lasso.survival next * lasso.clearance next currentOwner +
      (1 - lasso.survival next) *
        deadlockMatrix currentOwner nextOwner at hnoClipNext
  rw [hcurrentNextZero, mul_zero, zero_add] at hnoClipNext
  have hpositive : 0 < deadlockMatrix currentOwner nextOwner := by
    have hmatrixNe := deadlockMatrix_ne_zero_of_ne hownerNe
    have hfactor : 0 < 1 - lasso.survival next :=
      sub_pos.mpr (lasso.survival_lt_one next)
    have hmatrixNonneg : 0 ≤ deadlockMatrix currentOwner nextOwner := by
      by_contra hnot
      have hmatrixNeg : deadlockMatrix currentOwner nextOwner < 0 :=
        lt_of_not_ge hnot
      have hproductNeg := mul_neg_of_pos_of_neg hfactor hmatrixNeg
      linarith
    exact lt_of_le_of_ne hmatrixNonneg (Ne.symm hmatrixNe)
  simpa only [currentOwner, nextOwner, next] using ⟨hnegative, hpositive⟩

/-- The only consecutive-owner transitions compatible with zero debt are the
four directed edges displayed in the mathematical proof. -/
theorem owner_transition_of_debt_zero
    (hzero : lasso.debt (0 : Fin (K + 1)) = 0)
    (phase : Fin (K + 1)) :
    (lasso.owner phase = 0 ∧
        lasso.owner (finRotate (K + 1) phase) = 3) ∨
      (lasso.owner phase = 1 ∧
        lasso.owner (finRotate (K + 1) phase) = 2) ∨
      (lasso.owner phase = 2 ∧
        lasso.owner (finRotate (K + 1) phase) = 0) ∨
      (lasso.owner phase = 3 ∧
        lasso.owner (finRotate (K + 1) phase) = 2) := by
  have hsign := lasso.owner_transition_signs_of_debt_zero hzero phase
  fin_cases hcurrent : lasso.owner phase <;>
    fin_cases hnext : lasso.owner (finRotate (K + 1) phase) <;>
    norm_num [deadlockMatrix, hcurrent, hnext] at hsign ⊢

/-- Deterministic successor map forced by the four allowed owner transitions. -/
def forcedOwnerNext : Player → Player := ![3, 2, 0, 2]

/-- The owner word of a zero-debt lasso follows `forcedOwnerNext`. -/
theorem owner_next_eq_forcedOwnerNext
    (hzero : lasso.debt (0 : Fin (K + 1)) = 0)
    (phase : Fin (K + 1)) :
    lasso.owner (finRotate (K + 1) phase) =
      forcedOwnerNext (lasso.owner phase) := by
  rcases lasso.owner_transition_of_debt_zero hzero phase with
    h | h | h | h <;>
    simp [forcedOwnerNext, h.1, h.2]

/-- Every zero-debt owner cycle contains an owner-`0` phase. -/
theorem exists_owner_zero_of_debt_zero
    (hzero : lasso.debt (0 : Fin (K + 1)) = 0) :
    ∃ phase, lasso.owner phase = 0 := by
  let phase0 : Fin (K + 1) := 0
  let phase1 := finRotate (K + 1) phase0
  let phase2 := finRotate (K + 1) phase1
  have hstep0 := lasso.owner_next_eq_forcedOwnerNext hzero phase0
  have hstep1 := lasso.owner_next_eq_forcedOwnerNext hzero phase1
  change lasso.owner phase1 = forcedOwnerNext (lasso.owner phase0) at hstep0
  change lasso.owner phase2 = forcedOwnerNext (lasso.owner phase1) at hstep1
  fin_cases howner : lasso.owner phase0
  · exact ⟨phase0, howner⟩
  · refine ⟨phase2, ?_⟩
    simp [howner, forcedOwnerNext] at hstep0
    simp [hstep0, forcedOwnerNext] at hstep1
    exact hstep1
  · refine ⟨phase1, ?_⟩
    simpa [howner, forcedOwnerNext] using hstep0
  · refine ⟨phase2, ?_⟩
    simp [howner, forcedOwnerNext] at hstep0
    simp [hstep0, forcedOwnerNext] at hstep1
    exact hstep1

/-- Every owner-`0` phase in a zero-debt lasso is preceded by owner `2`. -/
theorem owner_prev_eq_two_of_owner_zero
    (hzero : lasso.debt (0 : Fin (K + 1)) = 0)
    {phase : Fin (K + 1)} (howner : lasso.owner phase = 0) :
    lasso.owner ((finRotate (K + 1)).symm phase) = 2 := by
  let previous := (finRotate (K + 1)).symm phase
  have hnext : finRotate (K + 1) previous = phase :=
    (finRotate (K + 1)).apply_symm_apply phase
  have htransition := lasso.owner_transition_of_debt_zero hzero previous
  change lasso.owner previous = 2
  rw [hnext, howner] at htransition
  rcases htransition with h | h | h | h <;> simp_all

/-- At an owner-`0` phase the old owner-`2` coordinate also vanishes, so the
clearance vector has the form `(0,x,0,A)`. -/
theorem clearance_two_eq_zero_of_owner_zero
    (hzero : lasso.debt (0 : Fin (K + 1)) = 0)
    {phase : Fin (K + 1)} (howner : lasso.owner phase = 0) :
    lasso.clearance phase 2 = 0 := by
  let previous := (finRotate (K + 1)).symm phase
  have hpreviousOwner :=
    lasso.owner_prev_eq_two_of_owner_zero hzero howner
  have hpreviousZero :=
    lasso.owner_clearance_eq_zero_of_debt_zero hzero previous
  have hstep := congrFun (lasso.clearance_step previous) 2
  have hnext : finRotate (K + 1) previous = phase :=
    (finRotate (K + 1)).apply_symm_apply phase
  change lasso.clearance phase 2 = 0
  rw [← hnext, hstep]
  simp [idealSingletonClearance, hpreviousOwner, hpreviousZero]

/-- Three forced zero-cost blocks strictly decrease the projective ratio
`t₁ / t₃` between successive owner-`0` phases. -/
theorem owner_zero_three_step_ratio_lt
    (hzero : lasso.debt (0 : Fin (K + 1)) = 0)
    {phase0 : Fin (K + 1)} (howner0 : lasso.owner phase0 = 0) :
    let phase1 := finRotate (K + 1) phase0
    let phase2 := finRotate (K + 1) phase1
    let phase3 := finRotate (K + 1) phase2
    lasso.clearance phase3 1 / lasso.clearance phase3 3 <
      lasso.clearance phase0 1 / lasso.clearance phase0 3 := by
  let phase1 := finRotate (K + 1) phase0
  let phase2 := finRotate (K + 1) phase1
  let phase3 := finRotate (K + 1) phase2
  have howner1 : lasso.owner phase1 = 3 := by
    have h := lasso.owner_next_eq_forcedOwnerNext hzero phase0
    change lasso.owner phase1 = forcedOwnerNext (lasso.owner phase0) at h
    simpa [howner0, forcedOwnerNext] using h
  have howner2 : lasso.owner phase2 = 2 := by
    have h := lasso.owner_next_eq_forcedOwnerNext hzero phase1
    change lasso.owner phase2 = forcedOwnerNext (lasso.owner phase1) at h
    simpa [howner1, forcedOwnerNext] using h
  have howner3 : lasso.owner phase3 = 0 := by
    have h := lasso.owner_next_eq_forcedOwnerNext hzero phase2
    change lasso.owner phase3 = forcedOwnerNext (lasso.owner phase2) at h
    simpa [howner2, forcedOwnerNext] using h
  have hzero0 := lasso.owner_clearance_eq_zero_of_debt_zero hzero phase0
  have hzero1 := lasso.owner_clearance_eq_zero_of_debt_zero hzero phase1
  have hzero2 := lasso.owner_clearance_eq_zero_of_debt_zero hzero phase2
  have hzero3 := lasso.owner_clearance_eq_zero_of_debt_zero hzero phase3
  have htwo0 := lasso.clearance_two_eq_zero_of_owner_zero hzero howner0
  rw [howner0] at hzero0
  rw [howner1] at hzero1
  rw [howner2] at hzero2
  rw [howner3] at hzero3
  let α0 := lasso.survival phase0
  let α3 := lasso.survival phase1
  let α2 := lasso.survival phase2
  let x := lasso.clearance phase0 1
  let A := lasso.clearance phase0 3
  let y1 := lasso.clearance phase1 1
  let y2 := lasso.clearance phase1 2
  let z1 := lasso.clearance phase2 1
  let z0 := lasso.clearance phase2 0
  let x' := lasso.clearance phase3 1
  let A' := lasso.clearance phase3 3
  have hbalance0 : α0 * A = 1 - α0 := by
    have h := lasso.clearance_step_eq_affine_of_ne hzero phase0
      (who := 3) (by simpa [howner0])
    change lasso.clearance phase1 3 = _ at h
    rw [hzero1] at h
    norm_num [α0, A, howner0, deadlockMatrix] at h ⊢
    linarith
  have hA : 0 < A := by
    have hα0lt := lasso.survival_lt_one phase0
    change lasso.survival phase0 < 1 at hα0lt
    change lasso.survival phase0 * lasso.clearance phase0 3 =
      1 - lasso.survival phase0 at hbalance0
    change 0 < lasso.clearance phase0 3
    by_contra hnot
    have hAle : lasso.clearance phase0 3 ≤ 0 := le_of_not_gt hnot
    have hAnonneg := lasso.clearance_nonneg phase0 3
    have hAzero : lasso.clearance phase0 3 = 0 := le_antisymm hAle hAnonneg
    rw [hAzero, mul_zero] at hbalance0
    linarith
  have hy1 : y1 = α0 * x + 2 * (1 - α0) := by
    have h := lasso.clearance_step_eq_affine_of_ne hzero phase0
      (who := 1) (by simpa [howner0])
    change lasso.clearance phase1 1 = _ at h
    norm_num [α0, x, y1, howner0, deadlockMatrix] at h ⊢
    exact h
  have hy2 : y2 = 2 * (1 - α0) := by
    have h := lasso.clearance_step_eq_affine_of_ne hzero phase0
      (who := 2) (by simpa [howner0])
    change lasso.clearance phase1 2 = _ at h
    rw [htwo0] at h
    norm_num [α0, y2, howner0, deadlockMatrix] at h ⊢
    ring_nf at h ⊢
    exact h
  have hbalance3 : α3 * y2 = 1 - α3 := by
    have h := lasso.clearance_step_eq_affine_of_ne hzero phase1
      (who := 2) (by simpa [howner1])
    change lasso.clearance phase2 2 = _ at h
    rw [hzero2] at h
    norm_num [α3, y2, howner1, deadlockMatrix] at h ⊢
    linarith
  have hz1 : z1 = α3 * y1 - 3 * (1 - α3) := by
    have h := lasso.clearance_step_eq_affine_of_ne hzero phase1
      (who := 1) (by simpa [howner1])
    change lasso.clearance phase2 1 = _ at h
    norm_num [α3, y1, z1, howner1, deadlockMatrix] at h ⊢
    exact h
  have hphase1Zero0 : lasso.clearance phase1 0 = 0 := by
    have h := lasso.clearance_step_owner_eq phase0
    rw [howner0] at h
    change lasso.clearance phase1 0 = lasso.clearance phase0 0 at h
    rw [h, hzero0]
  have hz0 : z0 = 3 * (1 - α3) := by
    have h := lasso.clearance_step_eq_affine_of_ne hzero phase1
      (who := 0) (by simpa [howner1])
    change lasso.clearance phase2 0 = _ at h
    rw [hphase1Zero0] at h
    norm_num [α3, z0, howner1, deadlockMatrix] at h ⊢
    ring_nf at h ⊢
    exact h
  have hbalance2 : α2 * z0 = 1 - α2 := by
    have h := lasso.clearance_step_eq_affine_of_ne hzero phase2
      (who := 0) (by simpa [howner2])
    change lasso.clearance phase3 0 = _ at h
    rw [hzero3] at h
    norm_num [α2, z0, howner2, deadlockMatrix] at h ⊢
    linarith
  have hx' : x' = α2 * z1 + (1 - α2) := by
    have h := lasso.clearance_step_eq_affine_of_ne hzero phase2
      (who := 1) (by simpa [howner2])
    change lasso.clearance phase3 1 = _ at h
    norm_num [α2, z1, x', howner2, deadlockMatrix] at h ⊢
    exact h
  have hphase2Zero3 : lasso.clearance phase2 3 = 0 := by
    have h := lasso.clearance_step_owner_eq phase1
    rw [howner1] at h
    change lasso.clearance phase2 3 = lasso.clearance phase1 3 at h
    rw [h, hzero1]
  have hA' : A' = 1 - α2 := by
    have h := lasso.clearance_step_eq_affine_of_ne hzero phase2
      (who := 3) (by simpa [howner2])
    change lasso.clearance phase3 3 = _ at h
    rw [hphase2Zero3] at h
    norm_num [α2, A', howner2, deadlockMatrix] at h ⊢
    ring_nf at h ⊢
    exact h
  exact deadlock_three_block_ratio_lt
    (lasso.survival_pos_of_debt_zero hzero phase0)
    (lasso.survival_pos_of_debt_zero hzero phase1)
    (lasso.survival_pos_of_debt_zero hzero phase2) hA
    hbalance0 hy1 hy2 hbalance3 hz1
    (lasso.clearance_nonneg phase2 1) hz0 hbalance2 hx' hA'

/-- Three forced owner transitions starting from owner `0` return to owner
`0`. -/
theorem owner_three_steps_eq_zero_of_owner_zero
    (hzero : lasso.debt (0 : Fin (K + 1)) = 0)
    {phase0 : Fin (K + 1)} (howner0 : lasso.owner phase0 = 0) :
    lasso.owner
      (finRotate (K + 1)
        (finRotate (K + 1) (finRotate (K + 1) phase0))) = 0 := by
  let phase1 := finRotate (K + 1) phase0
  let phase2 := finRotate (K + 1) phase1
  let phase3 := finRotate (K + 1) phase2
  have howner1 : lasso.owner phase1 = 3 := by
    have h := lasso.owner_next_eq_forcedOwnerNext hzero phase0
    change lasso.owner phase1 = forcedOwnerNext (lasso.owner phase0) at h
    simpa [howner0, forcedOwnerNext] using h
  have howner2 : lasso.owner phase2 = 2 := by
    have h := lasso.owner_next_eq_forcedOwnerNext hzero phase1
    change lasso.owner phase2 = forcedOwnerNext (lasso.owner phase1) at h
    simpa [howner1, forcedOwnerNext] using h
  have howner3 : lasso.owner phase3 = 0 := by
    have h := lasso.owner_next_eq_forcedOwnerNext hzero phase2
    change lasso.owner phase3 = forcedOwnerNext (lasso.owner phase2) at h
    simpa [howner2, forcedOwnerNext] using h
  exact howner3

/-- Phases whose active owner is player `0`. -/
def ownerZeroPhases : Finset (Fin (K + 1)) :=
  Finset.univ.filter fun phase => lasso.owner phase = 0

/-- A hypothetical zero-debt cycle has at least one owner-`0` phase. -/
theorem ownerZeroPhases_nonempty
    (hzero : lasso.debt (0 : Fin (K + 1)) = 0) :
    lasso.ownerZeroPhases.Nonempty := by
  obtain ⟨phase, howner⟩ := lasso.exists_owner_zero_of_debt_zero hzero
  exact ⟨phase, by simp [ownerZeroPhases, howner]⟩

/-- **No exact zero-debt reduced lasso.**  Minimize the projective ratio
`t₁ / t₃` over owner-`0` phases.  Three forced blocks return to another
owner-`0` phase with a strictly smaller ratio, a contradiction. -/
theorem debt_zero_impossible :
    lasso.debt (0 : Fin (K + 1)) ≠ 0 := by
  intro hzero
  obtain ⟨phase0, hphase0, hminimal⟩ := Finset.exists_min_image
    lasso.ownerZeroPhases
    (fun phase => lasso.clearance phase 1 / lasso.clearance phase 3)
    (lasso.ownerZeroPhases_nonempty hzero)
  have howner0 : lasso.owner phase0 = 0 :=
    (Finset.mem_filter.mp hphase0).2
  let phase1 := finRotate (K + 1) phase0
  let phase2 := finRotate (K + 1) phase1
  let phase3 := finRotate (K + 1) phase2
  have howner3 : lasso.owner phase3 = 0 := by
    simpa only [phase1, phase2, phase3] using
      lasso.owner_three_steps_eq_zero_of_owner_zero hzero howner0
  have hphase3 : phase3 ∈ lasso.ownerZeroPhases := by
    simp [ownerZeroPhases, howner3]
  have hle := hminimal phase3 hphase3
  have hlt :
      lasso.clearance phase3 1 / lasso.clearance phase3 3 <
        lasso.clearance phase0 1 / lasso.clearance phase0 3 := by
    simpa only [phase1, phase2, phase3] using
      lasso.owner_zero_three_step_ratio_lt hzero howner0
  exact (not_lt_of_ge hle) hlt

/-- Every reduced ideal-singleton lasso has strictly positive debt at every
phase. -/
theorem debt_pos (phase : Fin (K + 1)) :
    0 < lasso.debt phase := by
  have hzero : lasso.debt (0 : Fin (K + 1)) ≠ 0 :=
    lasso.debt_zero_impossible
  have hbase : 0 < lasso.debt (0 : Fin (K + 1)) :=
    lt_of_le_of_ne (lasso.debt_nonneg 0) (Ne.symm hzero)
  obtain ⟨steps, _, hreach⟩ :=
    Math.exists_iterate_finRotate_eq (0 : Fin (K + 1)) phase
  rw [← hreach]
  exact lasso.debt_iterate_pos hbase steps

end ReducedIdealSingletonLasso

end FullCoreDeadlock
end GameTheory

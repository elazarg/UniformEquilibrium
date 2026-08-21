/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.FullCore.DeadlockGlobalContraction

/-!
# A sharper contraction in the full-core deadlock family

This file records a second exact singleton return for the displayed
full-core deadlock matrix.  Its four blocks have owners and survivals
`(3, 4/5)`, `(1, 15/16)`, `(2, 4/7)`, and `(0, 19/24)`.  The return has
survival coefficient `19/56` and fixed total debt `7771/416472`.

Two further zero-additive-charge blocks lower the realized carrier debt to
`1227/96755`.  The result is a local quantitative certificate for this
completion family; it is not a claim that the minimum debt is positive.
-/

noncomputable section

namespace GameTheory
namespace FullCoreDeadlock

open Filter Finset
open QuittingLCPClassification
open IdealSingletonBlockApproximation
open IdealSingletonCarrierBridge
open scoped Topology

/-! ## Exact cap and debt data -/

def sharperBase : Player → ℝ := ![0, 407 / 536, 5 / 12, 11 / 84]

def sharperAfterThree : Player → ℝ :=
  ![3 / 5, 1 / 134, 2 / 15, 11 / 84]

def sharperAfterOne : Player → ℝ :=
  ![3 / 4, 1 / 134, 0, 0]

def sharperAfterTwo : Player → ℝ := ![0, 29 / 67, 0, 3 / 7]

theorem sharperBase_nonneg : ∀ who, 0 ≤ sharperBase who := by
  intro who
  fin_cases who <;>
    norm_num [sharperBase, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three]

theorem sharperFirst_clearance :
    idealSingletonClearance deadlockMatrix 3 (4 / 5) sharperBase =
      sharperAfterThree := by
  funext who
  fin_cases who <;>
    norm_num [idealSingletonClearance, deadlockMatrix, sharperBase,
      sharperAfterThree, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three] <;> decide

theorem sharperSecond_clearance :
    idealSingletonClearance deadlockMatrix 1 (15 / 16) sharperAfterThree =
      sharperAfterOne := by
  funext who
  fin_cases who <;>
    norm_num [idealSingletonClearance, deadlockMatrix, sharperAfterThree,
      sharperAfterOne, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three]

theorem sharperThird_clearance :
    idealSingletonClearance deadlockMatrix 2 (4 / 7) sharperAfterOne =
      sharperAfterTwo := by
  funext who
  fin_cases who <;>
    norm_num [idealSingletonClearance, deadlockMatrix, sharperAfterOne,
      sharperAfterTwo, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three] <;> decide

theorem sharperFourth_clearance :
    idealSingletonClearance deadlockMatrix 0 (19 / 24) sharperAfterTwo =
      sharperBase := by
  funext who
  fin_cases who <;>
    norm_num [idealSingletonClearance, deadlockMatrix, sharperAfterTwo,
      sharperBase, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three]

theorem sharperFirst_debt (D : ℝ) :
    idealSingletonDebt deadlockMatrix 3 (4 / 5) sharperBase D =
      (4 / 5) * D + 11 / 420 := by
  norm_num [idealSingletonDebt, deadlockMatrix, sharperBase,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]

theorem sharperSecond_debt (D : ℝ) :
    idealSingletonDebt deadlockMatrix 1 (15 / 16) sharperAfterThree D =
      (15 / 16) * D + 1 / 2144 + 1 / 448 := by
  norm_num [idealSingletonDebt, deadlockMatrix, sharperAfterThree,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]

theorem sharperThird_debt (D : ℝ) :
    idealSingletonDebt deadlockMatrix 2 (4 / 7) sharperAfterOne D =
      (4 / 7) * D := by
  norm_num [idealSingletonDebt, deadlockMatrix, sharperAfterOne,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]

theorem sharperFourth_debt (D : ℝ) :
    idealSingletonDebt deadlockMatrix 0 (19 / 24) sharperAfterTwo D =
      (19 / 24) * D := by
  norm_num [idealSingletonDebt, deadlockMatrix, sharperAfterTwo,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]

/-! ## The sharper semantic return -/

def sharperReturn
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (pair : QuittingTerminalSemanticPair Player) :
    QuittingTerminalSemanticPair Player :=
  idealSingletonSemanticPair reward 0 (19 / 24)
    (idealSingletonSemanticPair reward 2 (4 / 7)
      (idealSingletonSemanticPair reward 1 (15 / 16)
        (idealSingletonSemanticPair reward 3 (4 / 5) pair)))

theorem sharperReturn_mem_carrier
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (pair : QuittingTerminalSemanticPair Player)
    (hclearance : ∀ who, 0 ≤ capClearance reward pair.2 who)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    sharperReturn reward pair ∈ quittingTerminalSemanticCarrier reward := by
  let pair₁ := idealSingletonSemanticPair reward 3 (4 / 5) pair
  let pair₂ := idealSingletonSemanticPair reward 1 (15 / 16) pair₁
  let pair₃ := idealSingletonSemanticPair reward 2 (4 / 7) pair₂
  have hpair₁ : pair₁ ∈ quittingTerminalSemanticCarrier reward :=
    idealSingletonSemanticPair_mem_carrier reward pair 3 (4 / 5)
      (by norm_num) (by norm_num) hclearance hpair
  have hclearance₁ : ∀ who, 0 ≤ capClearance reward pair₁.2 who :=
    capClearance_idealSingletonSemanticPair_nonneg reward pair 3 (4 / 5)
      hclearance
  have hpair₂ : pair₂ ∈ quittingTerminalSemanticCarrier reward :=
    idealSingletonSemanticPair_mem_carrier reward pair₁ 1 (15 / 16)
      (by norm_num) (by norm_num) hclearance₁ hpair₁
  have hclearance₂ : ∀ who, 0 ≤ capClearance reward pair₂.2 who :=
    capClearance_idealSingletonSemanticPair_nonneg reward pair₁ 1 (15 / 16)
      hclearance₁
  have hpair₃ : pair₃ ∈ quittingTerminalSemanticCarrier reward :=
    idealSingletonSemanticPair_mem_carrier reward pair₂ 2 (4 / 7)
      (by norm_num) (by norm_num) hclearance₂ hpair₂
  have hclearance₃ : ∀ who, 0 ≤ capClearance reward pair₃.2 who :=
    capClearance_idealSingletonSemanticPair_nonneg reward pair₂ 2 (4 / 7)
      hclearance₂
  exact idealSingletonSemanticPair_mem_carrier reward pair₃ 0 (19 / 24)
    (by norm_num) (by norm_num) hclearance₃ hpair₃

theorem capClearance_sharperReturn
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (pair : QuittingTerminalSemanticPair Player)
    (hmatrix : IsFullCoreDeadlockCompletion reward)
    (hclearance : capClearance reward pair.2 = sharperBase) :
    capClearance reward (sharperReturn reward pair).2 = sharperBase := by
  unfold sharperReturn
  rw [capClearance_idealSingletonSemanticPair,
    capClearance_idealSingletonSemanticPair,
    capClearance_idealSingletonSemanticPair,
    capClearance_idealSingletonSemanticPair,
    hmatrix, hclearance, sharperFirst_clearance, sharperSecond_clearance,
    sharperThird_clearance, sharperFourth_clearance]

theorem debtSum_sharperReturn
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (pair : QuittingTerminalSemanticPair Player)
    (hmatrix : IsFullCoreDeadlockCompletion reward)
    (hclearance : capClearance reward pair.2 = sharperBase) :
    quittingTerminalSemanticDebtSum (sharperReturn reward pair) =
      (19 / 56) * quittingTerminalSemanticDebtSum pair +
        7771 / 630336 := by
  let pair₁ := idealSingletonSemanticPair reward 3 (4 / 5) pair
  let pair₂ := idealSingletonSemanticPair reward 1 (15 / 16) pair₁
  let pair₃ := idealSingletonSemanticPair reward 2 (4 / 7) pair₂
  have hcap₁ : capClearance reward pair₁.2 = sharperAfterThree := by
    dsimp only [pair₁]
    rw [capClearance_idealSingletonSemanticPair, hmatrix, hclearance,
      sharperFirst_clearance]
  have hcap₂ : capClearance reward pair₂.2 = sharperAfterOne := by
    dsimp only [pair₂]
    rw [capClearance_idealSingletonSemanticPair, hmatrix, hcap₁,
      sharperSecond_clearance]
  have hcap₃ : capClearance reward pair₃.2 = sharperAfterTwo := by
    dsimp only [pair₃]
    rw [capClearance_idealSingletonSemanticPair, hmatrix, hcap₂,
      sharperThird_clearance]
  have hdebt₁ : quittingTerminalSemanticDebtSum pair₁ =
      (4 / 5) * quittingTerminalSemanticDebtSum pair + 11 / 420 := by
    dsimp only [pair₁]
    rw [idealSingletonSemanticPair_debtSum, hmatrix, hclearance,
      sharperFirst_debt]
  have hdebt₂ : quittingTerminalSemanticDebtSum pair₂ =
      (15 / 16) * quittingTerminalSemanticDebtSum pair₁ + 1 / 2144 + 1 / 448 := by
    dsimp only [pair₂]
    rw [idealSingletonSemanticPair_debtSum, hmatrix, hcap₁,
      sharperSecond_debt]
  have hdebt₃ : quittingTerminalSemanticDebtSum pair₃ =
      (4 / 7) * quittingTerminalSemanticDebtSum pair₂ := by
    dsimp only [pair₃]
    rw [idealSingletonSemanticPair_debtSum, hmatrix, hcap₂,
      sharperThird_debt]
  unfold sharperReturn
  rw [idealSingletonSemanticPair_debtSum, hmatrix, hcap₃,
    sharperFourth_debt, hdebt₃, hdebt₂, hdebt₁]
  ring

def sharperCapReturn (t : Player → ℝ) : Player → ℝ :=
  idealSingletonClearance deadlockMatrix 0 (19 / 24)
    (idealSingletonClearance deadlockMatrix 2 (4 / 7)
      (idealSingletonClearance deadlockMatrix 1 (15 / 16)
        (idealSingletonClearance deadlockMatrix 3 (4 / 5) t)))

theorem sharperCapReturn_sharperBase :
    sharperCapReturn sharperBase = sharperBase := by
  unfold sharperCapReturn
  rw [sharperFirst_clearance, sharperSecond_clearance,
    sharperThird_clearance, sharperFourth_clearance]

def sharperCoordinateFactor : Player → ℝ :=
  ![3 / 7, 38 / 105, 19 / 32, 95 / 224]

theorem sharperCoordinateFactor_nonneg (who : Player) :
    0 ≤ sharperCoordinateFactor who := by
  fin_cases who <;> norm_num [sharperCoordinateFactor]

theorem sharperCoordinateFactor_lt_one (who : Player) :
    sharperCoordinateFactor who < 1 := by
  fin_cases who <;> norm_num [sharperCoordinateFactor]

private def sharperFactor (owner who : Player) (α : ℝ) : ℝ :=
  if who = owner then 1 else α

private theorem sharperFactor_nonneg
    (owner who : Player) {α : ℝ} (hα : 0 ≤ α) :
    0 ≤ sharperFactor owner who α := by
  unfold sharperFactor
  split <;> positivity

private theorem sharperFactor_product (who : Player) :
    sharperFactor 0 who (19 / 24) * sharperFactor 2 who (4 / 7) *
        sharperFactor 1 who (15 / 16) * sharperFactor 3 who (4 / 5) =
      sharperCoordinateFactor who := by
  fin_cases who <;>
    norm_num [sharperFactor, sharperCoordinateFactor, Fin.ext_iff]

theorem sharperCapReturn_coordinate_contraction
    (t s : Player → ℝ) (who : Player) :
    |sharperCapReturn t who - sharperCapReturn s who| ≤
      sharperCoordinateFactor who * |t who - s who| := by
  let t₁ := idealSingletonClearance deadlockMatrix 3 (4 / 5) t
  let s₁ := idealSingletonClearance deadlockMatrix 3 (4 / 5) s
  let t₂ := idealSingletonClearance deadlockMatrix 1 (15 / 16) t₁
  let s₂ := idealSingletonClearance deadlockMatrix 1 (15 / 16) s₁
  let t₃ := idealSingletonClearance deadlockMatrix 2 (4 / 7) t₂
  let s₃ := idealSingletonClearance deadlockMatrix 2 (4 / 7) s₂
  have h₁ : |t₁ who - s₁ who| ≤
      sharperFactor 3 who (4 / 5) * |t who - s who| := by
    simpa [t₁, s₁, sharperFactor] using
      abs_idealSingletonClearance_sub_le deadlockMatrix 3 (4 / 5)
        (by norm_num) t s who
  have h₂ : |t₂ who - s₂ who| ≤
      sharperFactor 1 who (15 / 16) * |t₁ who - s₁ who| := by
    simpa [t₂, s₂, sharperFactor] using
      abs_idealSingletonClearance_sub_le deadlockMatrix 1 (15 / 16)
        (by norm_num) t₁ s₁ who
  have h₃ : |t₃ who - s₃ who| ≤
      sharperFactor 2 who (4 / 7) * |t₂ who - s₂ who| := by
    simpa [t₃, s₃, sharperFactor] using
      abs_idealSingletonClearance_sub_le deadlockMatrix 2 (4 / 7)
        (by norm_num) t₂ s₂ who
  have h₄ :
      |idealSingletonClearance deadlockMatrix 0 (19 / 24) t₃ who -
          idealSingletonClearance deadlockMatrix 0 (19 / 24) s₃ who| ≤
        sharperFactor 0 who (19 / 24) * |t₃ who - s₃ who| := by
    simpa [sharperFactor] using
      abs_idealSingletonClearance_sub_le deadlockMatrix 0 (19 / 24)
        (by norm_num) t₃ s₃ who
  have hf₁ := sharperFactor_nonneg 3 who (by norm_num : (0 : ℝ) ≤ 4 / 5)
  have hf₂ := sharperFactor_nonneg 1 who (by norm_num : (0 : ℝ) ≤ 15 / 16)
  have hf₃ := sharperFactor_nonneg 2 who (by norm_num : (0 : ℝ) ≤ 4 / 7)
  have hf₄ := sharperFactor_nonneg 0 who (by norm_num : (0 : ℝ) ≤ 19 / 24)
  unfold sharperCapReturn
  change
    |idealSingletonClearance deadlockMatrix 0 (19 / 24) t₃ who -
      idealSingletonClearance deadlockMatrix 0 (19 / 24) s₃ who| ≤ _
  calc
    _ ≤ sharperFactor 0 who (19 / 24) * |t₃ who - s₃ who| := h₄
    _ ≤ sharperFactor 0 who (19 / 24) *
        (sharperFactor 2 who (4 / 7) * |t₂ who - s₂ who|) :=
      mul_le_mul_of_nonneg_left h₃ hf₄
    _ ≤ sharperFactor 0 who (19 / 24) *
        (sharperFactor 2 who (4 / 7) *
          (sharperFactor 1 who (15 / 16) * |t₁ who - s₁ who|)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left h₂ hf₃) hf₄
    _ ≤ sharperFactor 0 who (19 / 24) *
        (sharperFactor 2 who (4 / 7) *
          (sharperFactor 1 who (15 / 16) *
            (sharperFactor 3 who (4 / 5) * |t who - s who|))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h₁ hf₂) hf₃) hf₄
    _ = (sharperFactor 0 who (19 / 24) *
        sharperFactor 2 who (4 / 7) * sharperFactor 1 who (15 / 16) *
        sharperFactor 3 who (4 / 5)) * |t who - s who| := by ring
    _ = sharperCoordinateFactor who * |t who - s who| := by
      rw [sharperFactor_product who]

theorem capClearance_sharperReturn_eq_sharperCapReturn
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (pair : QuittingTerminalSemanticPair Player)
    (hmatrix : IsFullCoreDeadlockCompletion reward) :
    capClearance reward (sharperReturn reward pair).2 =
      sharperCapReturn (capClearance reward pair.2) := by
  unfold sharperReturn sharperCapReturn
  rw [capClearance_idealSingletonSemanticPair,
    capClearance_idealSingletonSemanticPair,
    capClearance_idealSingletonSemanticPair,
    capClearance_idealSingletonSemanticPair, hmatrix]

/-! ## Fixed pair and carrier realization -/

def sharperFixedPrescribed
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player) :
    Payoff Player := fun who =>
      19 / 148 * reward (quittingProjectiveSingletonTerminal 3) who +
      19 / 444 * reward (quittingProjectiveSingletonTerminal 1) who +
      19 / 37 * reward (quittingProjectiveSingletonTerminal 2) who +
      35 / 111 * reward (quittingProjectiveSingletonTerminal 0) who

def sharperFixedPair
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player) :
    QuittingTerminalSemanticPair Player :=
  (sharperFixedPrescribed reward,
    fun who => ownSingleton reward who + sharperBase who)

@[simp] theorem capClearance_sharperFixedPair
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player) :
    capClearance reward (sharperFixedPair reward).2 = sharperBase := by
  funext who
  simp [sharperFixedPair, capClearance]

theorem sharperReturn_prescribed
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (pair : QuittingTerminalSemanticPair Player) (who : Player) :
    (sharperReturn reward pair).1 who =
      (19 / 56) * pair.1 who + (37 / 56) *
        sharperFixedPrescribed reward who := by
  unfold sharperReturn sharperFixedPrescribed
  simp only [idealSingletonSemanticPair]
  ring

theorem sharperReturn_sharperFixedPair
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (hmatrix : IsFullCoreDeadlockCompletion reward) :
    sharperReturn reward (sharperFixedPair reward) =
      sharperFixedPair reward := by
  apply Prod.ext
  · funext who
    rw [sharperReturn_prescribed]
    simp [sharperFixedPair]
    ring
  · have hcap := capClearance_sharperReturn reward (sharperFixedPair reward)
      hmatrix
      (capClearance_sharperFixedPair reward)
    funext who
    have hwho := congrFun hcap who
    unfold capClearance at hwho
    change (sharperReturn reward (sharperFixedPair reward)).2 who =
      ownSingleton reward who + sharperBase who
    linarith [hwho]

theorem sharperReturn_cap_nonneg
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (pair : QuittingTerminalSemanticPair Player)
    (hclearance : ∀ who, 0 ≤ capClearance reward pair.2 who) :
    ∀ who, 0 ≤ capClearance reward (sharperReturn reward pair).2 who := by
  unfold sharperReturn
  apply capClearance_idealSingletonSemanticPair_nonneg
  apply capClearance_idealSingletonSemanticPair_nonneg
  apply capClearance_idealSingletonSemanticPair_nonneg
  apply capClearance_idealSingletonSemanticPair_nonneg
  exact hclearance

def sharperReturnOrbit
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (start : QuittingTerminalSemanticPair Player) :
    ℕ → QuittingTerminalSemanticPair Player
  | 0 => start
  | n + 1 => sharperReturn reward (sharperReturnOrbit reward start n)

theorem sharperReturnOrbit_mem_and_nonneg
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (start : QuittingTerminalSemanticPair Player)
    (hstartMem : start ∈ quittingTerminalSemanticCarrier reward)
    (hstartNonneg : ∀ who, 0 ≤ capClearance reward start.2 who) :
    ∀ n,
      sharperReturnOrbit reward start n ∈
          quittingTerminalSemanticCarrier reward ∧
      ∀ who, 0 ≤ capClearance reward
        (sharperReturnOrbit reward start n).2 who := by
  intro n
  induction n with
  | zero => exact ⟨hstartMem, hstartNonneg⟩
  | succ n ih =>
      rw [sharperReturnOrbit]
      exact ⟨sharperReturn_mem_carrier reward _ ih.2 ih.1,
        sharperReturn_cap_nonneg reward _ ih.2⟩

theorem sharperReturnOrbit_prescribed
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (start : QuittingTerminalSemanticPair Player)
    (n : ℕ) (who : Player) :
    (sharperReturnOrbit reward start n).1 who =
      (19 / 56) ^ n *
          (start.1 who - sharperFixedPrescribed reward who) +
        sharperFixedPrescribed reward who := by
  induction n with
  | zero => simp [sharperReturnOrbit]
  | succ n ih =>
      rw [sharperReturnOrbit, sharperReturn_prescribed, ih, pow_succ]
      ring

theorem sharperReturnOrbit_cap_error_le
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (start : QuittingTerminalSemanticPair Player)
    (hmatrix : IsFullCoreDeadlockCompletion reward)
    (n : ℕ) (who : Player) :
    |capClearance reward (sharperReturnOrbit reward start n).2 who -
        sharperBase who| ≤
      (sharperCoordinateFactor who) ^ n *
        |capClearance reward start.2 who - sharperBase who| := by
  induction n with
  | zero => simp [sharperReturnOrbit]
  | succ n ih =>
      have hstep := sharperCapReturn_coordinate_contraction
        (capClearance reward (sharperReturnOrbit reward start n).2)
        sharperBase who
      rw [sharperCapReturn_sharperBase] at hstep
      rw [sharperReturnOrbit,
        capClearance_sharperReturn_eq_sharperCapReturn reward _ hmatrix]
      calc
        _ ≤ sharperCoordinateFactor who *
            |capClearance reward (sharperReturnOrbit reward start n).2 who -
              sharperBase who| := hstep
        _ ≤ sharperCoordinateFactor who *
            ((sharperCoordinateFactor who) ^ n *
            |capClearance reward start.2 who - sharperBase who|) :=
          mul_le_mul_of_nonneg_left ih
            (sharperCoordinateFactor_nonneg who)
        _ = (sharperCoordinateFactor who) ^ (n + 1) *
            |capClearance reward start.2 who - sharperBase who| := by
          rw [pow_succ]
          ring

theorem sharperReturnOrbit_tendsto_sharperFixedPair
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (start : QuittingTerminalSemanticPair Player)
    (hmatrix : IsFullCoreDeadlockCompletion reward) :
    Tendsto (sharperReturnOrbit reward start) atTop
      (𝓝 (sharperFixedPair reward)) := by
  apply Filter.Tendsto.prodMk_nhds
  · apply tendsto_pi_nhds.2
    intro who
    have hpow : Tendsto (fun n : ℕ => (19 / 56 : ℝ) ^ n)
        atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hlimit : Tendsto (fun n : ℕ =>
        (19 / 56 : ℝ) ^ n *
            (start.1 who - sharperFixedPrescribed reward who) +
          sharperFixedPrescribed reward who)
        atTop (𝓝 (sharperFixedPrescribed reward who)) := by
      simpa using (hpow.mul_const
        (start.1 who - sharperFixedPrescribed reward who)).add_const
          (sharperFixedPrescribed reward who)
    exact hlimit.congr' (Eventually.of_forall fun n =>
      (sharperReturnOrbit_prescribed reward start n who).symm)
  · apply tendsto_pi_nhds.2
    intro who
    have hpow : Tendsto
        (fun n : ℕ => (sharperCoordinateFactor who) ^ n)
        atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one
        (sharperCoordinateFactor_nonneg who)
        (sharperCoordinateFactor_lt_one who)
    let bound := fun n : ℕ => (sharperCoordinateFactor who) ^ n *
      |capClearance reward start.2 who - sharperBase who|
    have hbound : Tendsto bound atTop (𝓝 0) := by
      simpa [bound] using hpow.mul_const
        |capClearance reward start.2 who - sharperBase who|
    have hdiff : Tendsto (fun n =>
        capClearance reward (sharperReturnOrbit reward start n).2 who -
          sharperBase who) atTop (𝓝 0) := by
      apply Math.tendsto_zero_of_abs_le_of_tendsto_zero _ bound hbound
      exact Eventually.of_forall fun n =>
        sharperReturnOrbit_cap_error_le reward start hmatrix n who
    have hcap : Tendsto (fun n =>
        capClearance reward (sharperReturnOrbit reward start n).2 who)
        atTop (𝓝 (sharperBase who)) := by
      simpa using hdiff.add_const (sharperBase who)
    have hcontinuation := hcap.add_const (ownSingleton reward who)
    simpa [capClearance, sharperFixedPair, add_comm] using hcontinuation

theorem sharperFixedPair_mem_carrier
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (hmatrix : IsFullCoreDeadlockCompletion reward) :
    sharperFixedPair reward ∈ quittingTerminalSemanticCarrier reward := by
  apply isClosed_closure.mem_of_tendsto
    (sharperReturnOrbit_tendsto_sharperFixedPair reward
      (quittingNeverBoundarySemanticPair reward) hmatrix)
  exact Eventually.of_forall fun n =>
    (sharperReturnOrbit_mem_and_nonneg reward
      (quittingNeverBoundarySemanticPair reward)
      (genericNever_mem_carrier reward)
      (genericNever_capClearance_nonneg reward) n).1

theorem sharperFixedPair_debtSum
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (hmatrix : IsFullCoreDeadlockCompletion reward) :
    quittingTerminalSemanticDebtSum (sharperFixedPair reward) =
      7771 / 416472 := by
  have hreturn := debtSum_sharperReturn reward (sharperFixedPair reward)
    hmatrix (capClearance_sharperFixedPair reward)
  rw [sharperReturn_sharperFixedPair reward hmatrix] at hreturn
  linarith

def sharperAfterZeroOwner : Player → ℝ := ![0, 121 / 134, 3 / 5, 0]

def sharperEndpoint : Player → ℝ :=
  ![363 / 523, 0, 601 / 2615, 0]

theorem sharperZeroOwner_clearance :
    idealSingletonClearance deadlockMatrix 0 (84 / 95) sharperBase =
      sharperAfterZeroOwner := by
  funext who
  fin_cases who <;>
    norm_num [idealSingletonClearance, deadlockMatrix, sharperBase,
      sharperAfterZeroOwner, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three]

theorem sharperEndpoint_clearance :
    idealSingletonClearance deadlockMatrix 3 (402 / 523)
        sharperAfterZeroOwner = sharperEndpoint := by
  funext who
  fin_cases who <;>
    norm_num [idealSingletonClearance, deadlockMatrix,
      sharperAfterZeroOwner, sharperEndpoint, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    decide

theorem sharperZeroOwner_debt (D : ℝ) :
    idealSingletonDebt deadlockMatrix 0 (84 / 95) sharperBase D =
      (84 / 95) * D := by
  norm_num [idealSingletonDebt, deadlockMatrix, sharperBase,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]

theorem sharperEndpoint_debt (D : ℝ) :
    idealSingletonDebt deadlockMatrix 3 (402 / 523) sharperAfterZeroOwner D =
      (402 / 523) * D := by
  norm_num [idealSingletonDebt, deadlockMatrix, sharperAfterZeroOwner,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]

theorem IsFullCoreDeadlockCompletion.exists_carrierPair_debtSum_eq_sharperBound
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (hcompletion : IsFullCoreDeadlockCompletion reward) :
    ∃ pair ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair = 1227 / 96755 := by
  let pair₀ := sharperFixedPair reward
  let pair₁ := idealSingletonSemanticPair reward 0 (84 / 95) pair₀
  let pair₂ := idealSingletonSemanticPair reward 3 (402 / 523) pair₁
  have hpair₀ : pair₀ ∈ quittingTerminalSemanticCarrier reward :=
    sharperFixedPair_mem_carrier reward hcompletion
  have hnonneg₀ : ∀ who, 0 ≤ capClearance reward pair₀.2 who := by
    rw [capClearance_sharperFixedPair]
    exact sharperBase_nonneg
  have hpair₁ : pair₁ ∈ quittingTerminalSemanticCarrier reward :=
    idealSingletonSemanticPair_mem_carrier reward pair₀ 0 (84 / 95)
      (by norm_num) (by norm_num) hnonneg₀ hpair₀
  have hcap₁ : capClearance reward pair₁.2 = sharperAfterZeroOwner := by
    dsimp only [pair₁]
    rw [capClearance_idealSingletonSemanticPair, hcompletion,
      capClearance_sharperFixedPair, sharperZeroOwner_clearance]
  have hnonneg₁ : ∀ who, 0 ≤ capClearance reward pair₁.2 who := by
    rw [hcap₁]
    intro who
    fin_cases who <;>
      norm_num [sharperAfterZeroOwner, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
  have hpair₂ : pair₂ ∈ quittingTerminalSemanticCarrier reward :=
    idealSingletonSemanticPair_mem_carrier reward pair₁ 3 (402 / 523)
      (by norm_num) (by norm_num) hnonneg₁ hpair₁
  have hcap₂ : capClearance reward pair₂.2 = sharperEndpoint := by
    dsimp only [pair₂]
    rw [capClearance_idealSingletonSemanticPair, hcompletion, hcap₁,
      sharperEndpoint_clearance]
  have hdebt₁ : quittingTerminalSemanticDebtSum pair₁ =
      (84 / 95) * quittingTerminalSemanticDebtSum pair₀ := by
    dsimp only [pair₁]
    rw [idealSingletonSemanticPair_debtSum, hcompletion,
      capClearance_sharperFixedPair, sharperZeroOwner_debt]
  have hdebt₂ : quittingTerminalSemanticDebtSum pair₂ =
      (402 / 523) * quittingTerminalSemanticDebtSum pair₁ := by
    dsimp only [pair₂]
    rw [idealSingletonSemanticPair_debtSum, hcompletion, hcap₁,
      sharperEndpoint_debt]
  refine ⟨pair₂, hpair₂, ?_⟩
  rw [hdebt₂, hdebt₁, sharperFixedPair_debtSum reward hcompletion]
  norm_num

theorem IsFullCoreDeadlockCompletion.globalDebtFloor_le_sharperBound
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (hcompletion : IsFullCoreDeadlockCompletion reward)
    (δ : ℝ)
    (hfloor : ∀ pair ∈ quittingTerminalSemanticCarrier reward,
      δ ≤ quittingTerminalSemanticDebtSum pair) :
    δ ≤ 1227 / 96755 := by
  obtain ⟨pair, hpair, hdebt⟩ :=
    hcompletion.exists_carrierPair_debtSum_eq_sharperBound
  rw [← hdebt]
  exact hfloor pair hpair

/-! ## Local singleton first-order obstruction -/

def singletonFirstOrderDebtCost (t : Player → ℝ) (owner : Player) : ℝ :=
  t owner + ∑ who ∈ Finset.univ.erase owner,
    max 0 (-(t who + deadlockMatrix who owner))

theorem sharperEndpoint_singletonFirstOrderDebtCost (owner : Player) :
    singletonFirstOrderDebtCost sharperEndpoint owner =
      ![886 / 523, 9859 / 2615, 1401 / 2615, 9859 / 2615] owner := by
  fin_cases owner <;>
    norm_num [singletonFirstOrderDebtCost, deadlockMatrix, sharperEndpoint,
      Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three]

theorem sharperEndpoint_singletonFirstOrderDebtCost_ge
    (owner : Player) :
    601 / 2615 ≤ singletonFirstOrderDebtCost sharperEndpoint owner := by
  rw [sharperEndpoint_singletonFirstOrderDebtCost]
  fin_cases owner <;> norm_num

theorem sharperEndpoint_singletonMixture_cost_ge
    (u : Player → ℝ) (hu : ∀ owner, 0 ≤ u owner)
    (hsum : ∑ owner, u owner = 1) :
    601 / 2615 ≤ ∑ owner,
      u owner * singletonFirstOrderDebtCost sharperEndpoint owner := by
  calc
    601 / 2615 = ∑ owner, (601 / 2615) * u owner := by
      rw [← Finset.mul_sum, hsum]
      norm_num
    _ ≤ ∑ owner,
        singletonFirstOrderDebtCost sharperEndpoint owner * u owner := by
      apply Finset.sum_le_sum
      intro owner howner
      exact mul_le_mul_of_nonneg_right
        (sharperEndpoint_singletonFirstOrderDebtCost_ge owner) (hu owner)
    _ = ∑ owner,
        u owner * singletonFirstOrderDebtCost sharperEndpoint owner := by
      apply Finset.sum_congr rfl
      intro owner howner
      ring

def singletonFirstOrderClearanceDrift
    (t : Player → ℝ) (owner who : Player) : ℝ :=
  if who = owner then 0 else deadlockMatrix who owner - t who

theorem sharperEndpoint_tangent_coordinate_one
    (u : Player → ℝ) :
    ∑ owner, u owner * singletonFirstOrderClearanceDrift
      sharperEndpoint owner 1 =
      2 * u 0 + u 2 - 3 * u 3 := by
  simp [Fin.sum_univ_succ, singletonFirstOrderClearanceDrift,
    deadlockMatrix, sharperEndpoint, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

theorem sharperEndpoint_tangent_coordinate_three
    (u : Player → ℝ) :
    ∑ owner, u owner * singletonFirstOrderClearanceDrift
      sharperEndpoint owner 3 =
      -u 0 - 2 * u 1 + u 2 := by
  simp [Fin.sum_univ_succ, singletonFirstOrderClearanceDrift,
    deadlockMatrix, sharperEndpoint, Matrix.cons_val_zero,
    Matrix.cons_val_three]
  ring

end FullCoreDeadlock
end GameTheory

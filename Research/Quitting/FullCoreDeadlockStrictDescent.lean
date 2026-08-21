/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.FullCoreDeadlockDebtBound

/-!
# Strict descent below the full-core deadlock fixed return

The integrated charged return supplies, for every completion of the displayed
four-player deadlock singleton matrix, an actual terminal-semantic carrier
point of total debt `1 / 14`.  That point is not a minimum.

Starting from its clearance `(3/4, 0, 1/4, 0)`, the following six ideal
singleton blocks have exact rational data:

```
(owner, survival) =
  (2, 9/11), (3, 17/18), (1, 11/12),
  (2, 9/16), (0, 16/23), (3, 23/30).
```

Every block is a limit of genuine finite positive-hazard prefixes, hence
preserves the actual compact carrier.  The resulting carrier point has total
semantic debt

`3391 / 110880 < 1 / 32`.

Thus every global semantic debt floor, and every terminal exploitability gap,
for every completion of this singleton matrix is at most `1 / 32`.

No lower bound, optimality statement, or vanishing-debt conclusion is claimed.
-/

noncomputable section

namespace GameTheory
namespace FullCoreDeadlock

open Finset
open QuittingLCPClassification
open IdealSingletonBlockApproximation
open IdealSingletonCarrierBridge

/-! ## The exact cap word -/

def strictDescentClearanceOne : Player → ℝ :=
  ![19 / 44, 2 / 11, 1 / 4, 2 / 11]

def strictDescentClearanceTwo : Player → ℝ :=
  ![455 / 792, 1 / 198, 13 / 72, 2 / 11]

def strictDescentClearanceThree : Player → ℝ :=
  ![671 / 864, 1 / 198, 0, 0]

def strictDescentClearanceFour : Player → ℝ :=
  ![0, 155 / 352, 0, 7 / 16]

def strictDescentClearanceFive : Player → ℝ :=
  ![0, 463 / 506, 14 / 23, 0]

def strictDescentClearanceSix : Player → ℝ :=
  ![7 / 10, 1 / 660, 7 / 30, 0]

private theorem strictDescentClearanceOne_eq :
    idealSingletonClearance deadlockMatrix 2 (9 / 11) chargedBase =
      strictDescentClearanceOne := by
  funext who
  fin_cases who <;>
    norm_num [idealSingletonClearance, deadlockMatrix, chargedBase,
      strictDescentClearanceOne, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three] <;>
    decide

private theorem strictDescentClearanceTwo_eq :
    idealSingletonClearance deadlockMatrix 3 (17 / 18)
        strictDescentClearanceOne =
      strictDescentClearanceTwo := by
  funext who
  fin_cases who <;>
    norm_num [idealSingletonClearance, deadlockMatrix,
      strictDescentClearanceOne, strictDescentClearanceTwo,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three] <;>
    decide

private theorem strictDescentClearanceThree_eq :
    idealSingletonClearance deadlockMatrix 1 (11 / 12)
        strictDescentClearanceTwo =
      strictDescentClearanceThree := by
  funext who
  fin_cases who <;>
    norm_num [idealSingletonClearance, deadlockMatrix,
      strictDescentClearanceTwo, strictDescentClearanceThree,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three] <;>
    decide

private theorem strictDescentClearanceFour_eq :
    idealSingletonClearance deadlockMatrix 2 (9 / 16)
        strictDescentClearanceThree =
      strictDescentClearanceFour := by
  funext who
  fin_cases who <;>
    norm_num [idealSingletonClearance, deadlockMatrix,
      strictDescentClearanceThree, strictDescentClearanceFour,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three] <;>
    decide

private theorem strictDescentClearanceFive_eq :
    idealSingletonClearance deadlockMatrix 0 (16 / 23)
        strictDescentClearanceFour =
      strictDescentClearanceFive := by
  funext who
  fin_cases who <;>
    norm_num [idealSingletonClearance, deadlockMatrix,
      strictDescentClearanceFour, strictDescentClearanceFive,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three] <;>
    decide

private theorem strictDescentClearanceSix_eq :
    idealSingletonClearance deadlockMatrix 3 (23 / 30)
        strictDescentClearanceFive =
      strictDescentClearanceSix := by
  funext who
  fin_cases who <;>
    norm_num [idealSingletonClearance, deadlockMatrix,
      strictDescentClearanceFive, strictDescentClearanceSix,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three] <;>
    decide

/-! ## Exact debt charges -/

private theorem strictDescentDebtOne (D : ℝ) :
    idealSingletonDebt deadlockMatrix 2 (9 / 11) chargedBase D =
      (9 / 11) * D + 1 / 22 := by
  norm_num [idealSingletonDebt, deadlockMatrix, chargedBase,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]

private theorem strictDescentDebtTwo (D : ℝ) :
    idealSingletonDebt deadlockMatrix 3 (17 / 18)
        strictDescentClearanceOne D =
      (17 / 18) * D + 1 / 99 := by
  norm_num [idealSingletonDebt, deadlockMatrix,
    strictDescentClearanceOne, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem strictDescentDebtThree (D : ℝ) :
    idealSingletonDebt deadlockMatrix 1 (11 / 12)
        strictDescentClearanceTwo D =
      (11 / 12) * D + 5 / 3168 := by
  norm_num [idealSingletonDebt, deadlockMatrix,
    strictDescentClearanceTwo, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem strictDescentDebtFour (D : ℝ) :
    idealSingletonDebt deadlockMatrix 2 (9 / 16)
        strictDescentClearanceThree D =
      (9 / 16) * D + 1 / 1536 := by
  norm_num [idealSingletonDebt, deadlockMatrix,
    strictDescentClearanceThree, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem strictDescentDebtFive (D : ℝ) :
    idealSingletonDebt deadlockMatrix 0 (16 / 23)
        strictDescentClearanceFour D =
      (16 / 23) * D := by
  norm_num [idealSingletonDebt, deadlockMatrix,
    strictDescentClearanceFour, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem strictDescentDebtSix (D : ℝ) :
    idealSingletonDebt deadlockMatrix 3 (23 / 30)
        strictDescentClearanceFive D =
      (23 / 30) * D := by
  norm_num [idealSingletonDebt, deadlockMatrix,
    strictDescentClearanceFive, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]

/-! ## Semantic realization -/

/-- The six-block semantic word, started at the universally realized charged
fixed pair. -/
def strictDescentPair
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player) :
    QuittingTerminalSemanticPair Player :=
  idealSingletonSemanticPair reward 3 (23 / 30)
    (idealSingletonSemanticPair reward 0 (16 / 23)
      (idealSingletonSemanticPair reward 2 (9 / 16)
        (idealSingletonSemanticPair reward 1 (11 / 12)
          (idealSingletonSemanticPair reward 3 (17 / 18)
            (idealSingletonSemanticPair reward 2 (9 / 11)
              (chargedFixedPair reward))))))

/-- The six-block word stays inside the actual compact terminal-semantic
carrier for every completion of the deadlock singleton matrix. -/
theorem strictDescentPair_mem_carrier
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (hcompletion : IsFullCoreDeadlockCompletion reward) :
    strictDescentPair reward ∈ quittingTerminalSemanticCarrier reward := by
  let pair₀ := chargedFixedPair reward
  let pair₁ := idealSingletonSemanticPair reward 2 (9 / 11) pair₀
  let pair₂ := idealSingletonSemanticPair reward 3 (17 / 18) pair₁
  let pair₃ := idealSingletonSemanticPair reward 1 (11 / 12) pair₂
  let pair₄ := idealSingletonSemanticPair reward 2 (9 / 16) pair₃
  let pair₅ := idealSingletonSemanticPair reward 0 (16 / 23) pair₄
  have hpair₀ : pair₀ ∈ quittingTerminalSemanticCarrier reward := by
    exact chargedFixedPair_mem_carrier reward hcompletion
  have hclearance₀ : ∀ who, 0 ≤ capClearance reward pair₀.2 who := by
    rw [show capClearance reward pair₀.2 = chargedBase by
      exact capClearance_chargedFixedPair reward]
    exact chargedBase_nonneg
  have hpair₁ : pair₁ ∈ quittingTerminalSemanticCarrier reward := by
    exact idealSingletonSemanticPair_mem_carrier reward pair₀ 2 (9 / 11)
      (by norm_num) (by norm_num) hclearance₀ hpair₀
  have hclearance₁ : ∀ who, 0 ≤ capClearance reward pair₁.2 who :=
    capClearance_idealSingletonSemanticPair_nonneg reward pair₀ 2 (9 / 11)
      hclearance₀
  have hpair₂ : pair₂ ∈ quittingTerminalSemanticCarrier reward := by
    exact idealSingletonSemanticPair_mem_carrier reward pair₁ 3 (17 / 18)
      (by norm_num) (by norm_num) hclearance₁ hpair₁
  have hclearance₂ : ∀ who, 0 ≤ capClearance reward pair₂.2 who :=
    capClearance_idealSingletonSemanticPair_nonneg reward pair₁ 3 (17 / 18)
      hclearance₁
  have hpair₃ : pair₃ ∈ quittingTerminalSemanticCarrier reward := by
    exact idealSingletonSemanticPair_mem_carrier reward pair₂ 1 (11 / 12)
      (by norm_num) (by norm_num) hclearance₂ hpair₂
  have hclearance₃ : ∀ who, 0 ≤ capClearance reward pair₃.2 who :=
    capClearance_idealSingletonSemanticPair_nonneg reward pair₂ 1 (11 / 12)
      hclearance₂
  have hpair₄ : pair₄ ∈ quittingTerminalSemanticCarrier reward := by
    exact idealSingletonSemanticPair_mem_carrier reward pair₃ 2 (9 / 16)
      (by norm_num) (by norm_num) hclearance₃ hpair₃
  have hclearance₄ : ∀ who, 0 ≤ capClearance reward pair₄.2 who :=
    capClearance_idealSingletonSemanticPair_nonneg reward pair₃ 2 (9 / 16)
      hclearance₃
  have hpair₅ : pair₅ ∈ quittingTerminalSemanticCarrier reward := by
    exact idealSingletonSemanticPair_mem_carrier reward pair₄ 0 (16 / 23)
      (by norm_num) (by norm_num) hclearance₄ hpair₄
  have hclearance₅ : ∀ who, 0 ≤ capClearance reward pair₅.2 who :=
    capClearance_idealSingletonSemanticPair_nonneg reward pair₄ 0 (16 / 23)
      hclearance₄
  have hpair₆ := idealSingletonSemanticPair_mem_carrier reward pair₅ 3
    (23 / 30) (by norm_num) (by norm_num) hclearance₅ hpair₅
  simpa [strictDescentPair, pair₀, pair₁, pair₂, pair₃, pair₄, pair₅] using
    hpair₆

/-- Exact clearance of the six-block carrier point. -/
theorem capClearance_strictDescentPair
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (hcompletion : IsFullCoreDeadlockCompletion reward) :
    capClearance reward (strictDescentPair reward).2 =
      strictDescentClearanceSix := by
  unfold strictDescentPair
  rw [capClearance_idealSingletonSemanticPair,
    capClearance_idealSingletonSemanticPair,
    capClearance_idealSingletonSemanticPair,
    capClearance_idealSingletonSemanticPair,
    capClearance_idealSingletonSemanticPair,
    capClearance_idealSingletonSemanticPair,
    hcompletion, capClearance_chargedFixedPair,
    strictDescentClearanceOne_eq, strictDescentClearanceTwo_eq,
    strictDescentClearanceThree_eq, strictDescentClearanceFour_eq,
    strictDescentClearanceFive_eq, strictDescentClearanceSix_eq]

/-- Exact total debt after the six-block descent. -/
theorem strictDescentPair_debtSum
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (hcompletion : IsFullCoreDeadlockCompletion reward) :
    quittingTerminalSemanticDebtSum (strictDescentPair reward) =
      3391 / 110880 := by
  let pair₀ := chargedFixedPair reward
  let pair₁ := idealSingletonSemanticPair reward 2 (9 / 11) pair₀
  let pair₂ := idealSingletonSemanticPair reward 3 (17 / 18) pair₁
  let pair₃ := idealSingletonSemanticPair reward 1 (11 / 12) pair₂
  let pair₄ := idealSingletonSemanticPair reward 2 (9 / 16) pair₃
  let pair₅ := idealSingletonSemanticPair reward 0 (16 / 23) pair₄
  have hcap₁ : capClearance reward pair₁.2 =
      strictDescentClearanceOne := by
    dsimp only [pair₁, pair₀]
    rw [capClearance_idealSingletonSemanticPair, hcompletion,
      capClearance_chargedFixedPair, strictDescentClearanceOne_eq]
  have hcap₂ : capClearance reward pair₂.2 =
      strictDescentClearanceTwo := by
    dsimp only [pair₂]
    rw [capClearance_idealSingletonSemanticPair, hcompletion, hcap₁,
      strictDescentClearanceTwo_eq]
  have hcap₃ : capClearance reward pair₃.2 =
      strictDescentClearanceThree := by
    dsimp only [pair₃]
    rw [capClearance_idealSingletonSemanticPair, hcompletion, hcap₂,
      strictDescentClearanceThree_eq]
  have hcap₄ : capClearance reward pair₄.2 =
      strictDescentClearanceFour := by
    dsimp only [pair₄]
    rw [capClearance_idealSingletonSemanticPair, hcompletion, hcap₃,
      strictDescentClearanceFour_eq]
  have hcap₅ : capClearance reward pair₅.2 =
      strictDescentClearanceFive := by
    dsimp only [pair₅]
    rw [capClearance_idealSingletonSemanticPair, hcompletion, hcap₄,
      strictDescentClearanceFive_eq]
  have hdebt₁ : quittingTerminalSemanticDebtSum pair₁ = 8 / 77 := by
    dsimp only [pair₁, pair₀]
    rw [idealSingletonSemanticPair_debtSum, hcompletion,
      capClearance_chargedFixedPair, strictDescentDebtOne,
      chargedFixedPair_debtSum reward hcompletion]
    norm_num
  have hdebt₂ : quittingTerminalSemanticDebtSum pair₂ = 25 / 231 := by
    dsimp only [pair₂]
    rw [idealSingletonSemanticPair_debtSum, hcompletion, hcap₁,
      strictDescentDebtTwo, hdebt₁]
    norm_num
  have hdebt₃ : quittingTerminalSemanticDebtSum pair₃ = 745 / 7392 := by
    dsimp only [pair₃]
    rw [idealSingletonSemanticPair_debtSum, hcompletion, hcap₂,
      strictDescentDebtThree, hdebt₂]
    norm_num
  have hdebt₄ : quittingTerminalSemanticDebtSum pair₄ = 3391 / 59136 := by
    dsimp only [pair₄]
    rw [idealSingletonSemanticPair_debtSum, hcompletion, hcap₃,
      strictDescentDebtFour, hdebt₃]
    norm_num
  have hdebt₅ : quittingTerminalSemanticDebtSum pair₅ = 3391 / 85008 := by
    dsimp only [pair₅]
    rw [idealSingletonSemanticPair_debtSum, hcompletion, hcap₄,
      strictDescentDebtFive, hdebt₄]
    norm_num
  unfold strictDescentPair
  rw [idealSingletonSemanticPair_debtSum, hcompletion, hcap₅,
    strictDescentDebtSix, hdebt₅]
  norm_num

/-- The new point is a strict descent from the integrated `1 / 14` fixed
return. -/
theorem strictDescentPair_debtSum_lt_one_fourteenth
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (hcompletion : IsFullCoreDeadlockCompletion reward) :
    quittingTerminalSemanticDebtSum (strictDescentPair reward) < 1 / 14 := by
  rw [strictDescentPair_debtSum reward hcompletion]
  norm_num

/-- Every completion has an actual carrier point with the exact smaller debt. -/
theorem IsFullCoreDeadlockCompletion.exists_carrierPair_debtSum_eq_strictDescent
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (hcompletion : IsFullCoreDeadlockCompletion reward) :
    ∃ pair ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair = 3391 / 110880 := by
  exact ⟨strictDescentPair reward,
    strictDescentPair_mem_carrier reward hcompletion,
    strictDescentPair_debtSum reward hcompletion⟩

/-- Exact improved upper bound on every global terminal-semantic debt floor. -/
theorem IsFullCoreDeadlockCompletion.globalDebtFloor_le_strictDescent
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (hcompletion : IsFullCoreDeadlockCompletion reward)
    (δ : ℝ)
    (hfloor : ∀ pair ∈ quittingTerminalSemanticCarrier reward,
      δ ≤ quittingTerminalSemanticDebtSum pair) :
    δ ≤ 3391 / 110880 := by
  rw [← strictDescentPair_debtSum reward hcompletion]
  exact hfloor (strictDescentPair reward)
    (strictDescentPair_mem_carrier reward hcompletion)

/-- Clean corollary: every global debt floor is strictly below `1 / 32`. -/
theorem IsFullCoreDeadlockCompletion.globalDebtFloor_le_one_thirty_second
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (hcompletion : IsFullCoreDeadlockCompletion reward)
    (δ : ℝ)
    (hfloor : ∀ pair ∈ quittingTerminalSemanticCarrier reward,
      δ ≤ quittingTerminalSemanticDebtSum pair) :
    δ ≤ 1 / 32 := by
  exact (hcompletion.globalDebtFloor_le_strictDescent δ hfloor).trans
    (by norm_num)

/-! ## Terminal exploitability consequences -/

/-- Every terminal exploitability gap for the completion is at most the exact
debt of the strict-descent carrier point. -/
theorem HasTerminalExploitabilityGap.fullCoreDeadlock_le_strictDescent
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    {gap : ℝ} (hexploit : HasTerminalExploitabilityGap reward gap)
    (hcompletion : IsFullCoreDeadlockCompletion reward) :
    gap ≤ 3391 / 110880 := by
  apply hcompletion.globalDebtFloor_le_strictDescent
  intro pair hpair
  exact terminalExploitabilityGap_le_terminalSemanticDebtSum_of_mem_carrier
    reward pair hexploit hpair

/-- Clean terminal-gap corollary. -/
theorem HasTerminalExploitabilityGap.fullCoreDeadlock_le_one_thirty_second
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    {gap : ℝ} (hexploit : HasTerminalExploitabilityGap reward gap)
    (hcompletion : IsFullCoreDeadlockCompletion reward) :
    gap ≤ 1 / 32 := by
  exact (hexploit.fullCoreDeadlock_le_strictDescent hcompletion).trans
    (by norm_num)

/-- The stored gap of a counterexample regime obeys the same exact bound. -/
theorem QuittingCounterexampleRegime.fullCoreDeadlock_terminalGap_le_strictDescent
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (regime : QuittingCounterexampleRegime reward)
    (hcompletion : IsFullCoreDeadlockCompletion reward) :
    regime.terminalGap ≤ 3391 / 110880 := by
  exact regime.terminalExploitability.fullCoreDeadlock_le_strictDescent
    hcompletion

/-- Clean stored-gap corollary. -/
theorem QuittingCounterexampleRegime.fullCoreDeadlock_terminalGap_le_one_thirty_second
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (regime : QuittingCounterexampleRegime reward)
    (hcompletion : IsFullCoreDeadlockCompletion reward) :
    regime.terminalGap ≤ 1 / 32 := by
  exact regime.terminalExploitability.fullCoreDeadlock_le_one_thirty_second
    hcompletion

end FullCoreDeadlock
end GameTheory

/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.IdealSingletonCarrierBridge
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryTailSemanticReduction

/-!
# A carrier-realized charged return for the four-player deadlock matrix

Question 193 isolated the full-core singleton comparison matrix

```
  0   3  -1   3
  2   0   1  -3
  2  -2   0  -1
 -1  -2   1   0
```

and a four-block cap-clearance return whose total-debt map is
`D ↦ (2 / 9) * D + 1 / 18`.  The remaining qualification in that calculation
was semantic: its base clearance `(3/4, 0, 1/4, 0)` had not been placed in the
actual compact terminal-semantic carrier.

This file closes that qualification.  Starting at zero clearance, two ideal
singleton blocks reach the charged-return base exactly:

```
(0, 0, 0, 0)
  -- owner 0, survival 2/3 --> (0, 2/3, 2/3, 0)
  -- owner 3, survival 3/4 --> (3/4, 0, 1/4, 0).
```

Each ideal block is a limit of genuine finite positive-hazard prefixes, so the
base lies in the actual carrier whenever the zero-clearance starting pair does.
The four-block return can then be iterated inside the carrier.  Its debt tends
to the exact fixed point `1/14`; consequently every global terminal-semantic
debt floor for such a reward completion is at most `1/14`.

The result does not prove that the floor is zero.  It removes the reachability
caveat from the charged return and turns the local calculation into a genuine
global carrier bound.
-/

noncomputable section

namespace GameTheory
namespace FullCoreDeadlockChargedReturn

open Filter Finset
open QuittingLCPClassification
open IdealSingletonCarrierBridge

abbrev Player := Fin 4

/-- The full-core matrix from the deadlock branch of Question 193. -/
def deadlockMatrix : Player → Player → ℝ :=
  ![![0, 3, -1, 3],
    ![2, 0, 1, -3],
    ![2, -2, 0, -1],
    ![-1, -2, 1, 0]]

@[simp] theorem deadlockMatrix_diagonal (who : Player) :
    deadlockMatrix who who = 0 := by
  fin_cases who <;> rfl

/-- A concrete rational reward completion.  Every own-singleton payoff is
one, singleton differences are `deadlockMatrix`, and larger coalitions pay
zero. -/
def reward : {S : Finset Player // S.Nonempty} → Payoff Player :=
  fun S who =>
    if S.1.card = 1 then
      1 + ∑ owner ∈ S.1, deadlockMatrix who owner
    else 0

@[simp] theorem reward_singleton (owner who : Player) :
    reward (quittingProjectiveSingletonTerminal owner) who =
      1 + deadlockMatrix who owner := by
  simp [reward, quittingProjectiveSingletonTerminal]

private theorem quittingSingletonTerminal_eq_projective (owner : Player) :
    quittingSingletonTerminal owner =
      quittingProjectiveSingletonTerminal owner := by
  apply Subtype.ext
  rfl

@[simp] theorem reward_quittingSingleton (owner who : Player) :
    reward (quittingSingletonTerminal owner) who =
      1 + deadlockMatrix who owner := by
  rw [quittingSingletonTerminal_eq_projective, reward_singleton]

/-- The completion has exactly the prescribed normalized singleton matrix. -/
theorem normalizedSoloMatrix_reward :
    normalizedSoloMatrix reward = deadlockMatrix := by
  funext who owner
  rw [normalizedSoloMatrix_eq_projectiveLCPMatrix]
  unfold quittingProjectiveLCPMatrix
  rw [reward_singleton, reward_singleton, deadlockMatrix_diagonal]
  ring

/-- Zero cap clearance. -/
def zeroClearance : Player → ℝ := ![0, 0, 0, 0]

/-- The intermediate point in the two-block reach. -/
def reachIntermediate : Player → ℝ := ![0, 2 / 3, 2 / 3, 0]

/-- The base of the charged four-block return. -/
def chargedBase : Player → ℝ := ![3 / 4, 0, 1 / 4, 0]

/-- First intermediate point of the charged return. -/
def returnFirst : Player → ℝ := ![1, 0, 0, 0]

/-- Second intermediate point of the charged return. -/
def returnSecond : Player → ℝ := ![0, 1 / 2, 0, 1 / 2]

/-- Third intermediate point of the charged return. -/
def returnThird : Player → ℝ := ![0, 1, 2 / 3, 0]

theorem zeroClearance_nonneg : ∀ who, 0 ≤ zeroClearance who := by
  intro who
  fin_cases who <;> norm_num [zeroClearance]

theorem chargedBase_nonneg : ∀ who, 0 ≤ chargedBase who := by
  intro who
  fin_cases who <;> norm_num [chargedBase]

/-! ## Exact cap-clearance reach -/

/-- The first ideal block sends zero clearance to the displayed intermediate
point. -/
theorem firstReach_clearance :
    idealSingletonClearance deadlockMatrix 0 (2 / 3) zeroClearance =
      reachIntermediate := by
  funext who
  fin_cases who <;>
    norm_num [idealSingletonClearance, deadlockMatrix, zeroClearance,
      reachIntermediate]

/-- The second ideal block reaches the charged-return base. -/
theorem secondReach_clearance :
    idealSingletonClearance deadlockMatrix 3 (3 / 4) reachIntermediate =
      chargedBase := by
  funext who
  fin_cases who <;>
    norm_num [idealSingletonClearance, deadlockMatrix, reachIntermediate,
      chargedBase]

/-! ## Exact charged return -/

/-- First cap step of the return. -/
theorem returnFirst_clearance :
    idealSingletonClearance deadlockMatrix 1 (8 / 9) chargedBase =
      returnFirst := by
  funext who
  fin_cases who <;>
    norm_num [idealSingletonClearance, deadlockMatrix, chargedBase,
      returnFirst]

/-- Second cap step of the return. -/
theorem returnSecond_clearance :
    idealSingletonClearance deadlockMatrix 2 (1 / 2) returnFirst =
      returnSecond := by
  funext who
  fin_cases who <;>
    norm_num [idealSingletonClearance, deadlockMatrix, returnFirst,
      returnSecond]

/-- Third cap step of the return. -/
theorem returnThird_clearance :
    idealSingletonClearance deadlockMatrix 0 (2 / 3) returnSecond =
      returnThird := by
  funext who
  fin_cases who <;>
    norm_num [idealSingletonClearance, deadlockMatrix, returnSecond,
      returnThird]

/-- Final cap step returns exactly to the base. -/
theorem returnBase_clearance :
    idealSingletonClearance deadlockMatrix 3 (3 / 4) returnThird =
      chargedBase := by
  funext who
  fin_cases who <;>
    norm_num [idealSingletonClearance, deadlockMatrix, returnThird,
      chargedBase]

/-- The first return block has the unique additive charge `2/9`, in
coordinate three. -/
theorem returnFirst_debt (D : ℝ) :
    idealSingletonDebt deadlockMatrix 1 (8 / 9) chargedBase D =
      (8 / 9) * D + 2 / 9 := by
  norm_num [idealSingletonDebt, deadlockMatrix, chargedBase,
    Fin.sum_univ_succ]
  ring

/-- The second return block is zero-cost. -/
theorem returnSecond_debt (D : ℝ) :
    idealSingletonDebt deadlockMatrix 2 (1 / 2) returnFirst D =
      (1 / 2) * D := by
  apply idealSingletonDebt_eq_mul_of_zeroCost
  · rfl
  · intro who hwho
    fin_cases who <;>
      norm_num [deadlockMatrix, returnFirst] at *

/-- The third return block is zero-cost. -/
theorem returnThird_debt (D : ℝ) :
    idealSingletonDebt deadlockMatrix 0 (2 / 3) returnSecond D =
      (2 / 3) * D := by
  apply idealSingletonDebt_eq_mul_of_zeroCost
  · rfl
  · intro who hwho
    fin_cases who <;>
      norm_num [deadlockMatrix, returnSecond] at *

/-- The final return block is zero-cost. -/
theorem returnBase_debt (D : ℝ) :
    idealSingletonDebt deadlockMatrix 3 (3 / 4) returnThird D =
      (3 / 4) * D := by
  apply idealSingletonDebt_eq_mul_of_zeroCost
  · rfl
  · intro who hwho
    fin_cases who <;>
      norm_num [deadlockMatrix, returnThird] at *

/-! ## Semantic realization -/

/-- The two-block semantic map which reaches the charged-return base. -/
def reachChargedBase
    (reward' : {S : Finset Player // S.Nonempty} → Payoff Player)
    (pair : QuittingTerminalSemanticPair Player) :
    QuittingTerminalSemanticPair Player :=
  idealSingletonSemanticPair reward' 3 (3 / 4)
    (idealSingletonSemanticPair reward' 0 (2 / 3) pair)

/-- The four-block charged semantic return. -/
def chargedReturn
    (reward' : {S : Finset Player // S.Nonempty} → Payoff Player)
    (pair : QuittingTerminalSemanticPair Player) :
    QuittingTerminalSemanticPair Player :=
  idealSingletonSemanticPair reward' 3 (3 / 4)
    (idealSingletonSemanticPair reward' 0 (2 / 3)
      (idealSingletonSemanticPair reward' 2 (1 / 2)
        (idealSingletonSemanticPair reward' 1 (8 / 9) pair)))

/-- The two-block reach preserves the actual compact semantic carrier. -/
theorem reachChargedBase_mem_carrier
    (reward' : {S : Finset Player // S.Nonempty} → Payoff Player)
    (pair : QuittingTerminalSemanticPair Player)
    (hclearance : ∀ who, 0 ≤ capClearance reward' pair.2 who)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward') :
    reachChargedBase reward' pair ∈
      quittingTerminalSemanticCarrier reward' := by
  have hfirst := idealSingletonSemanticPair_mem_carrier reward' pair 0
    (2 / 3) (by norm_num) (by norm_num) hclearance hpair
  have hfirstClearance :=
    capClearance_idealSingletonSemanticPair_nonneg reward' pair 0 (2 / 3)
      hclearance
  exact idealSingletonSemanticPair_mem_carrier reward'
    (idealSingletonSemanticPair reward' 0 (2 / 3) pair) 3 (3 / 4)
    (by norm_num) (by norm_num) hfirstClearance hfirst

/-- Under the displayed singleton matrix, the two-block semantic reach has
exactly the charged-base clearance. -/
theorem capClearance_reachChargedBase
    (reward' : {S : Finset Player // S.Nonempty} → Payoff Player)
    (pair : QuittingTerminalSemanticPair Player)
    (hmatrix : normalizedSoloMatrix reward' = deadlockMatrix)
    (hclearance : capClearance reward' pair.2 = zeroClearance) :
    capClearance reward' (reachChargedBase reward' pair).2 = chargedBase := by
  unfold reachChargedBase
  rw [capClearance_idealSingletonSemanticPair,
    capClearance_idealSingletonSemanticPair, hmatrix, hclearance,
    firstReach_clearance, secondReach_clearance]

/-- The charged return preserves the actual carrier. -/
theorem chargedReturn_mem_carrier
    (reward' : {S : Finset Player // S.Nonempty} → Payoff Player)
    (pair : QuittingTerminalSemanticPair Player)
    (hclearance : ∀ who, 0 ≤ capClearance reward' pair.2 who)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward') :
    chargedReturn reward' pair ∈ quittingTerminalSemanticCarrier reward' := by
  let pair₁ := idealSingletonSemanticPair reward' 1 (8 / 9) pair
  let pair₂ := idealSingletonSemanticPair reward' 2 (1 / 2) pair₁
  let pair₃ := idealSingletonSemanticPair reward' 0 (2 / 3) pair₂
  have hpair₁ : pair₁ ∈ quittingTerminalSemanticCarrier reward' :=
    idealSingletonSemanticPair_mem_carrier reward' pair 1 (8 / 9)
      (by norm_num) (by norm_num) hclearance hpair
  have hclearance₁ : ∀ who, 0 ≤ capClearance reward' pair₁.2 who :=
    capClearance_idealSingletonSemanticPair_nonneg reward' pair 1 (8 / 9)
      hclearance
  have hpair₂ : pair₂ ∈ quittingTerminalSemanticCarrier reward' :=
    idealSingletonSemanticPair_mem_carrier reward' pair₁ 2 (1 / 2)
      (by norm_num) (by norm_num) hclearance₁ hpair₁
  have hclearance₂ : ∀ who, 0 ≤ capClearance reward' pair₂.2 who :=
    capClearance_idealSingletonSemanticPair_nonneg reward' pair₁ 2 (1 / 2)
      hclearance₁
  have hpair₃ : pair₃ ∈ quittingTerminalSemanticCarrier reward' :=
    idealSingletonSemanticPair_mem_carrier reward' pair₂ 0 (2 / 3)
      (by norm_num) (by norm_num) hclearance₂ hpair₂
  have hclearance₃ : ∀ who, 0 ≤ capClearance reward' pair₃.2 who :=
    capClearance_idealSingletonSemanticPair_nonneg reward' pair₂ 0 (2 / 3)
      hclearance₂
  exact idealSingletonSemanticPair_mem_carrier reward' pair₃ 3 (3 / 4)
    (by norm_num) (by norm_num) hclearance₃ hpair₃

/-- On the charged-base fibre, one semantic return comes back to the same cap
clearance. -/
theorem capClearance_chargedReturn
    (reward' : {S : Finset Player // S.Nonempty} → Payoff Player)
    (pair : QuittingTerminalSemanticPair Player)
    (hmatrix : normalizedSoloMatrix reward' = deadlockMatrix)
    (hclearance : capClearance reward' pair.2 = chargedBase) :
    capClearance reward' (chargedReturn reward' pair).2 = chargedBase := by
  unfold chargedReturn
  rw [capClearance_idealSingletonSemanticPair,
    capClearance_idealSingletonSemanticPair,
    capClearance_idealSingletonSemanticPair,
    capClearance_idealSingletonSemanticPair,
    hmatrix, hclearance, returnFirst_clearance, returnSecond_clearance,
    returnThird_clearance, returnBase_clearance]

/-- Exact total-debt return map on the charged-base fibre. -/
theorem debtSum_chargedReturn
    (reward' : {S : Finset Player // S.Nonempty} → Payoff Player)
    (pair : QuittingTerminalSemanticPair Player)
    (hmatrix : normalizedSoloMatrix reward' = deadlockMatrix)
    (hclearance : capClearance reward' pair.2 = chargedBase) :
    quittingTerminalSemanticDebtSum (chargedReturn reward' pair) =
      (2 / 9) * quittingTerminalSemanticDebtSum pair + 1 / 18 := by
  let pair₁ := idealSingletonSemanticPair reward' 1 (8 / 9) pair
  let pair₂ := idealSingletonSemanticPair reward' 2 (1 / 2) pair₁
  let pair₃ := idealSingletonSemanticPair reward' 0 (2 / 3) pair₂
  have hcap₁ : capClearance reward' pair₁.2 = returnFirst := by
    dsimp only [pair₁]
    rw [capClearance_idealSingletonSemanticPair, hmatrix, hclearance,
      returnFirst_clearance]
  have hcap₂ : capClearance reward' pair₂.2 = returnSecond := by
    dsimp only [pair₂]
    rw [capClearance_idealSingletonSemanticPair, hmatrix, hcap₁,
      returnSecond_clearance]
  have hcap₃ : capClearance reward' pair₃.2 = returnThird := by
    dsimp only [pair₃]
    rw [capClearance_idealSingletonSemanticPair, hmatrix, hcap₂,
      returnThird_clearance]
  have hdebt₁ : quittingTerminalSemanticDebtSum pair₁ =
      (8 / 9) * quittingTerminalSemanticDebtSum pair + 2 / 9 := by
    dsimp only [pair₁]
    rw [idealSingletonSemanticPair_debtSum, hmatrix, hclearance,
      returnFirst_debt]
  have hdebt₂ : quittingTerminalSemanticDebtSum pair₂ =
      (1 / 2) * quittingTerminalSemanticDebtSum pair₁ := by
    dsimp only [pair₂]
    rw [idealSingletonSemanticPair_debtSum, hmatrix, hcap₁,
      returnSecond_debt]
  have hdebt₃ : quittingTerminalSemanticDebtSum pair₃ =
      (2 / 3) * quittingTerminalSemanticDebtSum pair₂ := by
    dsimp only [pair₃]
    rw [idealSingletonSemanticPair_debtSum, hmatrix, hcap₂,
      returnThird_debt]
  unfold chargedReturn
  rw [idealSingletonSemanticPair_debtSum, hmatrix, hcap₃,
    returnBase_debt, hdebt₃, hdebt₂, hdebt₁]
  ring

/-! ## Iteration and the global `1/14` bound -/

/-- Recursive orbit of the charged return. -/
def chargedReturnOrbit
    (reward' : {S : Finset Player // S.Nonempty} → Payoff Player)
    (start : QuittingTerminalSemanticPair Player) :
    ℕ → QuittingTerminalSemanticPair Player
  | 0 => start
  | n + 1 => chargedReturn reward' (chargedReturnOrbit reward' start n)

/-- Every orbit point remains in the carrier, retains the charged-base cap,
and has the exact affine-iteration debt formula. -/
theorem chargedReturnOrbit_mem_cap_debt
    (reward' : {S : Finset Player // S.Nonempty} → Payoff Player)
    (start : QuittingTerminalSemanticPair Player)
    (hmatrix : normalizedSoloMatrix reward' = deadlockMatrix)
    (hstartCap : capClearance reward' start.2 = chargedBase)
    (hstart : start ∈ quittingTerminalSemanticCarrier reward') :
    ∀ n,
      chargedReturnOrbit reward' start n ∈
          quittingTerminalSemanticCarrier reward' ∧
      capClearance reward' (chargedReturnOrbit reward' start n).2 =
          chargedBase ∧
      quittingTerminalSemanticDebtSum (chargedReturnOrbit reward' start n) =
        1 / 14 + (2 / 9) ^ n *
          (quittingTerminalSemanticDebtSum start - 1 / 14) := by
  intro n
  induction n with
  | zero =>
      exact ⟨hstart, hstartCap, by simp [chargedReturnOrbit]⟩
  | succ n ih =>
      have hclearance : ∀ who, 0 ≤ capClearance reward'
          (chargedReturnOrbit reward' start n).2 who := by
        rw [ih.2.1]
        exact chargedBase_nonneg
      have hmem := chargedReturn_mem_carrier reward'
        (chargedReturnOrbit reward' start n) hclearance ih.1
      have hcap := capClearance_chargedReturn reward'
        (chargedReturnOrbit reward' start n) hmatrix ih.2.1
      have hdebt := debtSum_chargedReturn reward'
        (chargedReturnOrbit reward' start n) hmatrix ih.2.1
      rw [ih.2.2] at hdebt
      refine ⟨hmem, hcap, ?_⟩
      rw [chargedReturnOrbit]
      rw [hdebt]
      rw [pow_succ]
      ring

/-- The orbit debt converges to the exact fixed point `1/14`. -/
theorem chargedReturnOrbit_debt_tendsto
    (reward' : {S : Finset Player // S.Nonempty} → Payoff Player)
    (start : QuittingTerminalSemanticPair Player)
    (hmatrix : normalizedSoloMatrix reward' = deadlockMatrix)
    (hstartCap : capClearance reward' start.2 = chargedBase)
    (hstart : start ∈ quittingTerminalSemanticCarrier reward') :
    Tendsto (fun n => quittingTerminalSemanticDebtSum
        (chargedReturnOrbit reward' start n)) atTop (𝓝 (1 / 14)) := by
  have horbit := chargedReturnOrbit_mem_cap_debt reward' start hmatrix
    hstartCap hstart
  have hpow : Tendsto (fun n : ℕ => (2 / 9 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlimit := (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => (1 / 14 : ℝ)) atTop (𝓝 (1 / 14))).add
    (hpow.mul_const
      (quittingTerminalSemanticDebtSum start - 1 / 14))
  exact hlimit.congr' (Eventually.of_forall fun n => (horbit n).2.2.symm)

/-- Any global debt floor is bounded by the charged-return fixed point once a
zero-clearance carrier state exists. -/
theorem globalDebtFloor_le_one_fourteenth
    (reward' : {S : Finset Player // S.Nonempty} → Payoff Player)
    (zeroStart : QuittingTerminalSemanticPair Player)
    (hmatrix : normalizedSoloMatrix reward' = deadlockMatrix)
    (hzeroCap : capClearance reward' zeroStart.2 = zeroClearance)
    (hzeroStart : zeroStart ∈ quittingTerminalSemanticCarrier reward')
    (δ : ℝ)
    (hfloor : ∀ pair ∈ quittingTerminalSemanticCarrier reward',
      δ ≤ quittingTerminalSemanticDebtSum pair) :
    δ ≤ 1 / 14 := by
  let start := reachChargedBase reward' zeroStart
  have hstart : start ∈ quittingTerminalSemanticCarrier reward' := by
    apply reachChargedBase_mem_carrier reward' zeroStart
    · rw [hzeroCap]
      exact zeroClearance_nonneg
    · exact hzeroStart
  have hstartCap : capClearance reward' start.2 = chargedBase := by
    exact capClearance_reachChargedBase reward' zeroStart hmatrix hzeroCap
  have htendsto := chargedReturnOrbit_debt_tendsto reward' start hmatrix
    hstartCap hstart
  by_contra hnot
  have hlt : (1 / 14 : ℝ) < δ := lt_of_not_ge hnot
  have heventually : ∀ᶠ n in atTop,
      quittingTerminalSemanticDebtSum
        (chargedReturnOrbit reward' start n) < δ :=
    (tendsto_order.1 htendsto).2 δ hlt
  obtain ⟨N, hN⟩ := eventually_atTop.1 heventually
  have hle := hfloor (chargedReturnOrbit reward' start N)
    (chargedReturnOrbit_mem_cap_debt reward' start hmatrix hstartCap hstart N).1
  linarith [hN N (le_refl N)]

/-! ## Concrete reward completion -/

/-- The Never boundary of the concrete completion has zero cap clearance. -/
theorem never_capClearance :
    capClearance reward (quittingNeverBoundarySemanticPair reward).2 =
      zeroClearance := by
  funext who
  fin_cases who <;>
    norm_num [capClearance, ownSingleton, quittingNeverBoundarySemanticPair,
      reward_singleton, reward_quittingSingleton, deadlockMatrix,
      zeroClearance]

/-- The Never boundary has total debt four, so the `1/14` bound is not merely
the initial boundary value. -/
theorem never_debtSum :
    quittingTerminalSemanticDebtSum
      (quittingNeverBoundarySemanticPair reward) = 4 := by
  simp [quittingTerminalSemanticDebtSum, quittingTerminalSemanticDebt,
    quittingNeverBoundarySemanticPair, reward_quittingSingleton,
    deadlockMatrix, Fin.sum_univ_succ]

/-- The Never semantic pair belongs to the compact carrier. -/
theorem never_mem_carrier :
    quittingNeverBoundarySemanticPair reward ∈
      quittingTerminalSemanticCarrier reward := by
  apply subset_closure
  refine ⟨quittingRootSequenceProfile reward
    (quittingElementaryCapRoots (.never : QuittingElementaryTailCap Player)) 0,
    ?_⟩
  exact quittingTerminalSemanticPair_elementaryCap_never reward

/-- Concrete global consequence: every debt lower bound on the full carrier of
this rational completion is at most `1/14`. -/
theorem reward_globalDebtFloor_le_one_fourteenth
    (δ : ℝ)
    (hfloor : ∀ pair ∈ quittingTerminalSemanticCarrier reward,
      δ ≤ quittingTerminalSemanticDebtSum pair) :
    δ ≤ 1 / 14 := by
  exact globalDebtFloor_le_one_fourteenth reward
    (quittingNeverBoundarySemanticPair reward)
    normalizedSoloMatrix_reward never_capClearance never_mem_carrier δ hfloor

end FullCoreDeadlockChargedReturn
end GameTheory

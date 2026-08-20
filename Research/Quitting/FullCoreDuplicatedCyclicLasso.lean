/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.StandardQSideExample
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryTailSemanticReduction
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.IdealSingletonCapDebtLasso
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.IdealSingletonBlockApproximation
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.IdealSingletonCarrierBridge

/-!
# A full-core filtered table with a contracting ideal singleton lasso

This calibration reuses the production-proved duplicated cyclic standard-Q
matrix.  Only the own-singleton levels are shifted; therefore its normalized
singleton comparison matrix, normal core, standard-Q property, and failure
of the homogeneous simplex problem are inherited exactly.
-/

noncomputable section

namespace GameTheory
namespace FullCoreDuplicatedCyclicLasso

open Finset
open QuittingLCPClassification
open QuittingLCPClassification.StandardQSideExample
open IdealSingletonBlockApproximation
open IdealSingletonCarrierBridge
open Filter

abbrev Player := StandardQSideExample.Player
abbrev CorePlayer := StandardQSideExample.CorePlayer

/-- Own-singleton levels.  The duplicate has positive Never debt, while
cyclic coordinate two supplies the unit starting clearance. -/
def ownSolo : Player → ℝ
  | none => 1
  | some i => ![0, 0, -1] i

/-- Full reward completion: singleton columns realize the shifted duplicated
cyclic matrix, and every coalition of size at least two pays zero. -/
def reward : {S : Finset Player // S.Nonempty} → Payoff Player :=
  fun S who =>
    if S.1.card = 1 then
      ownSolo who + ∑ owner ∈ S.1, duplicatedCyclicMatrix who owner
    else 0

theorem reward_singleton (owner who : Player) :
    reward (quittingProjectiveSingletonTerminal owner) who =
      ownSolo who + duplicatedCyclicMatrix who owner := by
  simp [reward, quittingProjectiveSingletonTerminal]

theorem quittingSingletonTerminal_eq_projective (owner : Player) :
    quittingSingletonTerminal owner =
      quittingProjectiveSingletonTerminal owner := by
  apply Subtype.ext
  rfl

theorem reward_quittingSingleton (owner who : Player) :
    reward (quittingSingletonTerminal owner) who =
      ownSolo who + duplicatedCyclicMatrix who owner := by
  rw [quittingSingletonTerminal_eq_projective, reward_singleton]

theorem normalizedSoloMatrix_reward :
    normalizedSoloMatrix reward = duplicatedCyclicMatrix := by
  funext who owner
  rw [normalizedSoloMatrix_eq_projectiveLCPMatrix]
  unfold quittingProjectiveLCPMatrix
  rw [reward_singleton, reward_singleton]
  simp [duplicatedCyclicMatrix_diagonal]

theorem reward_standardQMatrixSide : StandardQMatrixSide reward := by
  refine
    { normal_nonempty := ?_
      no_homogeneous := ?_
      normal_standardQ := ?_ }
  · rw [normalizedSoloMatrix_reward]
    exact ⟨none, mem_normalCore_duplicatedCyclicMatrix none⟩
  · change ¬HasHomogeneousSimplexSolution
      (normalPlayerMatrix (normalizedSoloMatrix reward))
    rw [normalizedSoloMatrix_reward]
    exact duplicatedCyclicMatrix_normal_noHomogeneous
  · change IsStandardQMatrix
      (normalPlayerMatrix (normalizedSoloMatrix reward))
    rw [normalizedSoloMatrix_reward]
    exact duplicatedCyclicMatrix_normal_standardQ

theorem reward_normalCore_eq_univ :
    normalCore (normalizedSoloMatrix reward) = Finset.univ := by
  rw [normalizedSoloMatrix_reward]
  exact normalCore_duplicatedCyclicMatrix_eq_univ

/-- Clearance vector of the Never semantic boundary. -/
def startClearance : Player → ℝ
  | none => 0
  | some i => ![0, 0, 1] i

theorem never_capClearance :
    capClearance reward (quittingNeverBoundarySemanticPair reward).2 =
      startClearance := by
  funext who
  cases who with
  | none => norm_num [capClearance, ownSingleton,
      quittingNeverBoundarySemanticPair, reward_singleton,
      reward_quittingSingleton, ownSolo,
      duplicatedCyclicMatrix_diagonal, startClearance]
  | some i =>
      fin_cases i <;>
        simp [capClearance, ownSingleton, quittingNeverBoundarySemanticPair,
          reward_singleton, reward_quittingSingleton, ownSolo,
          duplicatedCyclicMatrix_diagonal, startClearance]

theorem never_debtSum :
    quittingTerminalSemanticDebtSum
      (quittingNeverBoundarySemanticPair reward) = 1 := by
  simp [quittingTerminalSemanticDebtSum, quittingTerminalSemanticDebt,
    quittingNeverBoundarySemanticPair, reward_quittingSingleton, ownSolo,
    duplicatedCyclicMatrix_diagonal, Fin.sum_univ_succ]

abbrev owner₁ : Player := some 0
abbrev owner₂ : Player := some 2
abbrev owner₃ : Player := some 1

theorem first_clearance :
    idealSingletonClearance duplicatedCyclicMatrix owner₁ (1 / 2)
        startClearance =
      fun who => match who with
        | none => 0
        | some i => ![0, 1, 0] i := by
  funext who
  cases who with
  | none => norm_num [idealSingletonClearance, startClearance,
      duplicatedCyclicMatrix, duplicateCollapse, cyclicMatrix]
  | some i => fin_cases i <;>
      norm_num [idealSingletonClearance, startClearance,
        duplicatedCyclicMatrix, duplicateCollapse, cyclicMatrix]

def secondClearance : Player → ℝ
  | none => 1
  | some i => ![1, 0, 0] i

theorem second_clearance :
    idealSingletonClearance duplicatedCyclicMatrix owner₂ (1 / 2)
        (idealSingletonClearance duplicatedCyclicMatrix owner₁ (1 / 2)
          startClearance) = secondClearance := by
  rw [first_clearance]
  funext who
  cases who with
  | none =>
      simp [idealSingletonClearance, secondClearance, owner₂,
        duplicatedCyclicMatrix, duplicateCollapse, cyclicMatrix]
      norm_num
  | some i => fin_cases i <;>
      norm_num [idealSingletonClearance, secondClearance,
        duplicatedCyclicMatrix, duplicateCollapse, cyclicMatrix]

theorem third_clearance_return :
    idealSingletonClearance duplicatedCyclicMatrix owner₃ (1 / 2)
        (idealSingletonClearance duplicatedCyclicMatrix owner₂ (1 / 2)
          (idealSingletonClearance duplicatedCyclicMatrix owner₁ (1 / 2)
            startClearance)) = startClearance := by
  rw [second_clearance]
  funext who
  cases who with
  | none =>
      simp [idealSingletonClearance, secondClearance, owner₃,
        startClearance, duplicatedCyclicMatrix, duplicateCollapse,
        cyclicMatrix]
      norm_num
  | some i => fin_cases i <;>
      norm_num [idealSingletonClearance, secondClearance,
        startClearance, duplicatedCyclicMatrix, duplicateCollapse, cyclicMatrix]

theorem first_zeroCost (D : ℝ) :
    idealSingletonDebt duplicatedCyclicMatrix owner₁ (1 / 2)
      startClearance D = (1 / 2) * D := by
  apply idealSingletonDebt_eq_mul_of_zeroCost
  · rfl
  · intro who hwho
    cases who with
    | none => norm_num [startClearance, duplicatedCyclicMatrix,
        duplicateCollapse, cyclicMatrix]
    | some i => fin_cases i <;>
        norm_num [startClearance, duplicatedCyclicMatrix,
          duplicateCollapse, cyclicMatrix, owner₁] at *

theorem second_zeroCost (D : ℝ) :
    idealSingletonDebt duplicatedCyclicMatrix owner₂ (1 / 2)
      (idealSingletonClearance duplicatedCyclicMatrix owner₁ (1 / 2)
        startClearance) D = (1 / 2) * D := by
  rw [first_clearance]
  apply idealSingletonDebt_eq_mul_of_zeroCost
  · rfl
  · intro who hwho
    cases who with
    | none => norm_num [duplicatedCyclicMatrix, duplicateCollapse, cyclicMatrix]
    | some i => fin_cases i <;>
        norm_num [duplicatedCyclicMatrix, duplicateCollapse, cyclicMatrix,
          owner₂] at *

theorem third_zeroCost (D : ℝ) :
    idealSingletonDebt duplicatedCyclicMatrix owner₃ (1 / 2)
      (idealSingletonClearance duplicatedCyclicMatrix owner₂ (1 / 2)
        (idealSingletonClearance duplicatedCyclicMatrix owner₁ (1 / 2)
          startClearance)) D = (1 / 2) * D := by
  rw [second_clearance]
  apply idealSingletonDebt_eq_mul_of_zeroCost
  · rfl
  · intro who hwho
    cases who with
    | none => norm_num [secondClearance, duplicatedCyclicMatrix,
        duplicateCollapse, cyclicMatrix]
    | some i => fin_cases i <;>
        norm_num [secondClearance, duplicatedCyclicMatrix,
          duplicateCollapse, cyclicMatrix, owner₃] at *

theorem never_mem_carrier :
    quittingNeverBoundarySemanticPair reward ∈
      quittingTerminalSemanticCarrier reward := by
  apply subset_closure
  refine ⟨quittingRootSequenceProfile reward
    (quittingElementaryCapRoots (.never : QuittingElementaryTailCap Player)) 0,
    ?_⟩
  exact quittingTerminalSemanticPair_elementaryCap_never reward

/-- The actual carrier orbit supplied by the three ideal diffuse blocks. -/
def orbit (n : ℕ) : QuittingTerminalSemanticPair Player :=
  threeIdealSingletonLassoOrbit reward owner₁ owner₂ owner₃
    (1 / 2) (1 / 2) (1 / 2)
    (quittingNeverBoundarySemanticPair reward) n

theorem orbit_mem_and_exact_debt (n : ℕ) :
    orbit n ∈ quittingTerminalSemanticCarrier reward ∧
    quittingTerminalSemanticDebtSum (orbit n) = (1 / 8 : ℝ) ^ n := by
  have hreturn : threeIdealSingletonClearance (normalizedSoloMatrix reward)
      owner₁ owner₂ owner₃ (1 / 2) (1 / 2) (1 / 2)
        startClearance = startClearance := by
    rw [normalizedSoloMatrix_reward]
    exact third_clearance_return
  have hcost₁ : ∀ D, idealSingletonDebt (normalizedSoloMatrix reward)
      owner₁ (1 / 2) startClearance D = (1 / 2) * D := by
    intro D
    rw [normalizedSoloMatrix_reward]
    exact first_zeroCost D
  have hcost₂ : ∀ D, idealSingletonDebt (normalizedSoloMatrix reward)
      owner₂ (1 / 2)
        (idealSingletonClearance (normalizedSoloMatrix reward)
          owner₁ (1 / 2) startClearance) D = (1 / 2) * D := by
    intro D
    rw [normalizedSoloMatrix_reward]
    exact second_zeroCost D
  have hcost₃ : ∀ D, idealSingletonDebt (normalizedSoloMatrix reward)
      owner₃ (1 / 2)
        (idealSingletonClearance (normalizedSoloMatrix reward)
          owner₂ (1 / 2)
          (idealSingletonClearance (normalizedSoloMatrix reward)
            owner₁ (1 / 2) startClearance)) D = (1 / 2) * D := by
    intro D
    rw [normalizedSoloMatrix_reward]
    exact third_zeroCost D
  have horbit := threeIdealSingletonLassoOrbit_mem_and_debt reward
    (quittingNeverBoundarySemanticPair reward) owner₁ owner₂ owner₃
    (1 / 2) (1 / 2) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) startClearance
    (by intro who; cases who with
      | none => norm_num [startClearance]
      | some i => fin_cases i <;> norm_num [startClearance])
    never_capClearance hreturn hcost₁ hcost₂ hcost₃
    never_mem_carrier n
  refine ⟨?_, ?_⟩
  · simpa [orbit] using horbit.1
  · rw [show quittingTerminalSemanticDebtSum (orbit n) =
        ((1 / 2 : ℝ) * (1 / 2) * (1 / 2)) ^ n *
          quittingTerminalSemanticDebtSum
            (quittingNeverBoundarySemanticPair reward) by
      simpa [orbit] using horbit.2.2]
    rw [never_debtSum]
    norm_num

theorem orbit_debt_tendsto_zero :
    Tendsto (fun n => quittingTerminalSemanticDebtSum (orbit n))
      atTop (nhds 0) := by
  have hreturn : threeIdealSingletonClearance (normalizedSoloMatrix reward)
      owner₁ owner₂ owner₃ (1 / 2) (1 / 2) (1 / 2)
        startClearance = startClearance := by
    rw [normalizedSoloMatrix_reward]
    exact third_clearance_return
  have hcost₁ : ∀ D, idealSingletonDebt (normalizedSoloMatrix reward)
      owner₁ (1 / 2) startClearance D = (1 / 2) * D := by
    intro D
    rw [normalizedSoloMatrix_reward]
    exact first_zeroCost D
  have hcost₂ : ∀ D, idealSingletonDebt (normalizedSoloMatrix reward)
      owner₂ (1 / 2)
        (idealSingletonClearance (normalizedSoloMatrix reward)
          owner₁ (1 / 2) startClearance) D = (1 / 2) * D := by
    intro D
    rw [normalizedSoloMatrix_reward]
    exact second_zeroCost D
  have hcost₃ : ∀ D, idealSingletonDebt (normalizedSoloMatrix reward)
      owner₃ (1 / 2)
        (idealSingletonClearance (normalizedSoloMatrix reward)
          owner₂ (1 / 2)
          (idealSingletonClearance (normalizedSoloMatrix reward)
            owner₁ (1 / 2) startClearance)) D = (1 / 2) * D := by
    intro D
    rw [normalizedSoloMatrix_reward]
    exact third_zeroCost D
  simpa [orbit] using
    (threeIdealSingletonLassoOrbit_debt_tendsto_zero reward
      (quittingNeverBoundarySemanticPair reward) owner₁ owner₂ owner₃
      (1 / 2) (1 / 2) (1 / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      startClearance
      (by intro who; cases who with
        | none => norm_num [startClearance]
        | some i => fin_cases i <;> norm_num [startClearance])
      never_capClearance hreturn hcost₁ hcost₂ hcost₃
      never_mem_carrier)

/-- This full-core algebraically admissible table has no positive total-debt
floor on its attainable semantic carrier. -/
theorem no_positive_carrier_debt_floor :
    ¬∃ δ : ℝ, 0 < δ ∧
      ∀ pair ∈ quittingTerminalSemanticCarrier reward,
        δ ≤ quittingTerminalSemanticDebtSum pair := by
  rintro ⟨δ, hδ, hfloor⟩
  have heventually : ∀ᶠ n in atTop,
      quittingTerminalSemanticDebtSum (orbit n) < δ :=
    (tendsto_order.1 orbit_debt_tendsto_zero).2 δ hδ
  obtain ⟨n, hn⟩ := eventually_atTop.1 heventually
  have hle := hfloor (orbit n) (orbit_mem_and_exact_debt n).1
  linarith [hn n (le_refl n)]


end FullCoreDuplicatedCyclicLasso
end GameTheory

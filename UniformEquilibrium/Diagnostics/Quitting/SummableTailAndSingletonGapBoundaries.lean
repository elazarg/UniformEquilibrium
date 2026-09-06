/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.SinglePivotNonNormalRegression
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticDebtHomotopySelection
import UniformEquilibrium.Quitting.Bellman.Finite.SummableExactNashBellmanPunishmentFloor

/-!
# Normality and strict singleton-gap boundary examples

Two checked two-player examples record the hypotheses that cannot be removed
from the normal-floor and singleton-wall exits.  A nonnormal player can lie
strictly below its punishment floor on a constant exact all-Continue tail.
Separately, positive actual semantic debt at equality with the singleton wall
can coexist with an exact all-Continue root, zero absorption, and zero debt
drop under prefixing.
-/

noncomputable section

namespace GameTheory

open Math.Probability

namespace SummableTailNonNormalBoundary

open SinglePivotNonNormalRegression

/-- Constant displayed values for the nonnormal all-Continue tail. -/
def value : ℕ → Payoff Bool := fun _ who => if who then -(1 / 2 : ℝ) else 1

/-- Every displayed root is literally all Continue. -/
def roots : ℕ → Bool → PMF Bool := fun _ => quittingAllContinueRoot

theorem reward_bound (terminal) (player) : |reward terminal player| ≤ 1 := by
  simp [reward]
  split <;> split <;> norm_num

theorem value_bound (time) (player) : |value time player| ≤ 1 := by
  cases player <;> norm_num [value]

theorem policy (time) :
    value time = quittingRootSuccessorPayoff reward
      (value (time + 1)) (roots time) := by
  rw [show value time = value (time + 1) by rfl]
  exact (quittingRootSuccessorPayoff_allContinueRoot_eq
    reward (value (time + 1))).symm

theorem exact_root (time) :
    IsεQuittingRootNash reward (value (time + 1)) 0 (roots time) := by
  apply (isZeroQuittingRootNash_allContinue_iff_singleton_le
    reward (value (time + 1))).2
  intro who
  cases who
  · norm_num [value, pivot_singleton]
  · norm_num [value, other_singleton]

theorem summable_absorption : Summable (fun time =>
    quittingRootAbsorptionMass (roots time)) := by
  simp [roots, quittingRootAbsorptionMass_allContinueRoot]

/-- Normality is essential: all boundedness, exactness, and summable-charge
hypotheses hold, but the nonnormal player's displayed value is strictly below
its behavioral punishment value. -/
theorem nonnormal_allContinue_constant_tail_below_punishment :
    (∀ terminal player, |reward terminal player| ≤ 1) ∧
      (∀ time player, |value time player| ≤ 1) ∧
      (∀ time, value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time)) ∧
      (∀ time, IsεQuittingRootNash reward
        (value (time + 1)) 0 (roots time)) ∧
      Summable (fun time => quittingRootAbsorptionMass (roots time)) ∧
      ¬ IsQuittingNormalPlayer reward true ∧
      value 0 true < quittingPunishmentValue reward true := by
  refine ⟨reward_bound, value_bound, policy, exact_root,
    summable_absorption, ?_, ?_⟩
  · intro hnormal
    unfold IsQuittingNormalPlayer quittingSoloSelfPayoff at hnormal
    rw [other_punishment_eq_zero] at hnormal
    change 0 ≤ reward (quittingSingletonTerminal true) true at hnormal
    rw [other_singleton] at hnormal
    norm_num at hnormal
  · rw [other_punishment_eq_zero]
    norm_num [value]

end SummableTailNonNormalBoundary

namespace SingletonGapEqualityBoundary

/-- The existing local/global counterexample's actual terminal-semantic pair. -/
def pair : QuittingTerminalSemanticPair Bool :=
  quittingTerminalSemanticPair localGlobalCounterexampleReward
    localGlobalCounterexampleProfile

theorem pair_eq : pair =
    (localGlobalCounterexampleContinuation, fun _ => 0) := by
  exact quittingTerminalSemanticPair_localGlobalCounterexample_eq

theorem pair_mem_carrier :
    pair ∈ quittingTerminalSemanticCarrier localGlobalCounterexampleReward := by
  apply subset_closure
  exact ⟨localGlobalCounterexampleProfile, rfl⟩

theorem debt_false_eq_one : quittingTerminalSemanticDebt pair false = 1 := by
  rw [pair_eq]
  norm_num [quittingTerminalSemanticDebt, localGlobalCounterexampleContinuation]

theorem prescribed_false_eq_singleton :
    pair.1 false = localGlobalCounterexampleReward
      (quittingSingletonTerminal false) false := by
  rw [pair_eq, localGlobalCounterexampleReward_singleton_false]
  rfl

theorem allContinue_exact_against_prescribed :
    IsεQuittingRootNash localGlobalCounterexampleReward pair.1 0
      (quittingAllContinueRoot : Bool → PMF Bool) := by
  apply (isZeroQuittingRootNash_allContinue_iff_singleton_le
    localGlobalCounterexampleReward pair.1).2
  intro who
  rw [pair_eq]
  cases who <;>
    simp [localGlobalCounterexampleContinuation]

theorem allContinue_prefix_eq_pair :
    quittingTerminalSemanticPrefix localGlobalCounterexampleReward
      quittingAllContinueRoot pair = pair := by
  have hsemantic := semanticPair_allContinue_capNashPrefix_localGlobal
  rw [quittingTerminalSemanticPair_rootThenContinuation] at hsemantic
  exact hsemantic

/-- Strict singleton separation is essential: this actual carrier pair has
positive debt exactly on the singleton wall, while the exact all-Continue
root has zero absorption and its literal semantic prefix spends no debt. -/
theorem equality_wall_positiveDebt_zero_charge_and_drop :
    pair ∈ quittingTerminalSemanticCarrier localGlobalCounterexampleReward ∧
      0 < quittingTerminalSemanticDebt pair false ∧
      pair.1 false = localGlobalCounterexampleReward
        (quittingSingletonTerminal false) false ∧
      IsεQuittingRootNash localGlobalCounterexampleReward pair.1 0
        (quittingAllContinueRoot : Bool → PMF Bool) ∧
      quittingTerminalSemanticPrefix localGlobalCounterexampleReward
          quittingAllContinueRoot pair ∈
        quittingTerminalSemanticCarrier localGlobalCounterexampleReward ∧
      quittingRootAbsorptionMass
          (quittingAllContinueRoot : Bool → PMF Bool) = 0 ∧
      quittingTerminalSemanticDebtSum pair -
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPrefix localGlobalCounterexampleReward
              quittingAllContinueRoot pair) = 0 := by
  refine ⟨pair_mem_carrier, ?_, prescribed_false_eq_singleton,
    allContinue_exact_against_prescribed, ?_, ?_, ?_⟩
  · rw [debt_false_eq_one]
    norm_num
  · rw [allContinue_prefix_eq_pair]
    exact pair_mem_carrier
  · exact quittingRootAbsorptionMass_allContinueRoot
  · rw [allContinue_prefix_eq_pair, sub_self]

end SingletonGapEqualityBoundary

end GameTheory

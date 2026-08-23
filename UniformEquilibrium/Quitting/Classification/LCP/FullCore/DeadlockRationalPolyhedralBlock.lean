/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.FullCore.DeadlockChargedReturn
import UniformEquilibrium.Quitting.Cycles.BlockPeriodicProfile

/-!
# A rational joint block for a polyhedral deadlock slice

This file gives an exact three-phase product profile for a polyhedral class of
four-player quitting rewards.  Its singleton rows have the full-core deadlock
comparison matrix, its `{1, 3}` row equals the singleton baseline, and eight
linear collision inequalities are imposed.  All other reward coordinates are
unrestricted.  The baseline may have arbitrary sign.

The profile has supports `{0}`, `{2}`, and `{1, 3}` and hazards
`4/21`, `7/17`, `1/15`, and `5/26`, respectively.  The resulting fixed payoff
is `s + (0, 5/7, 8/21, 1/7)`.  The block certificate controls arbitrary
behavioral deviations through the general periodic-block consumer.
-/

noncomputable section

namespace GameTheory
namespace FullCoreDeadlock

open Math.Probability Math.PMFProduct Math.ProbabilityMassFunction
open QuittingLCPClassification

/-- Raw reward data for the rational three-phase block.  The fields contain
only reward-table equalities and inequalities, not the desired certificate. -/
structure IsDeadlockRationalJointBlockCompletion
    (reward' : {S : Finset Player // S.Nonempty} → Payoff Player)
    (baseline : Payoff Player) : Prop where
  singleton : ∀ owner who,
    reward' (quittingSingletonTerminal owner) who =
      baseline who + deadlockMatrix who owner
  pair_one_three : reward' ⟨{1, 3}, by simp⟩ = baseline
  pair_zero_one_one : reward' ⟨{0, 1}, by simp⟩ 1 - baseline 1 ≤ 15 / 4
  pair_zero_two_two : reward' ⟨{0, 2}, by simp⟩ 2 - baseline 2 ≤ 2
  pair_zero_three_three : reward' ⟨{0, 3}, by simp⟩ 3 - baseline 3 ≤ 3 / 4
  pair_zero_two_zero : reward' ⟨{0, 2}, by simp⟩ 0 - baseline 0 ≤ 0
  pair_one_two_one : reward' ⟨{1, 2}, by simp⟩ 1 - baseline 1 ≤ 1
  pair_two_three_three : reward' ⟨{2, 3}, by simp⟩ 3 - baseline 3 ≤ 1
  joint_cap_zero :
    21 * (reward' ⟨{0, 1}, by simp⟩ 0 - baseline 0) +
        70 * (reward' ⟨{0, 3}, by simp⟩ 0 - baseline 0) +
        5 * (reward' ⟨{0, 1, 3}, by simp⟩ 0 - baseline 0) ≤ 273
  joint_cap_two :
    21 * (reward' ⟨{1, 2}, by simp⟩ 2 - baseline 2) +
        70 * (reward' ⟨{2, 3}, by simp⟩ 2 - baseline 2) +
        5 * (reward' ⟨{1, 2, 3}, by simp⟩ 2 - baseline 2) ≤ 0

private theorem literalSingletonTerminal_eq (owner : Player) :
    (⟨{owner}, Finset.singleton_nonempty owner⟩ :
      {S : Finset Player // S.Nonempty}) = quittingSingletonTerminal owner := by
  apply Subtype.ext
  rfl

private theorem projectiveSingletonTerminal_eq (owner : Player) :
    quittingProjectiveSingletonTerminal owner = quittingSingletonTerminal owner := by
  apply Subtype.ext
  rfl

private theorem IsDeadlockRationalJointBlockCompletion.literalSingleton
    {reward' : {S : Finset Player // S.Nonempty} → Payoff Player}
    {s : Payoff Player} (h : IsDeadlockRationalJointBlockCompletion reward' s)
    (owner who : Player) :
    reward' ⟨{owner}, Finset.singleton_nonempty owner⟩ who =
      s who + deadlockMatrix who owner := by
  rw [literalSingletonTerminal_eq]
  exact h.singleton owner who

/-- The raw singleton equalities are exactly a completion of the normalized
full-core deadlock matrix. -/
theorem IsDeadlockRationalJointBlockCompletion.isFullCoreDeadlockCompletion
    {reward' : {S : Finset Player // S.Nonempty} → Payoff Player}
    {s : Payoff Player} (h : IsDeadlockRationalJointBlockCompletion reward' s) :
    IsFullCoreDeadlockCompletion reward' := by
  rw [IsFullCoreDeadlockCompletion,
    normalizedSoloMatrix_eq_projectiveLCPMatrix]
  funext who owner
  unfold quittingProjectiveLCPMatrix
  rw [projectiveSingletonTerminal_eq, projectiveSingletonTerminal_eq]
  rw [h.singleton owner who, h.singleton who who, deadlockMatrix_diagonal]
  ring

/-- The rational hazards, in phases supported by `{0}`, `{2}`, and `{1, 3}`. -/
def deadlockRationalBlockHazard : Fin 3 → Player → ℝ :=
  ![![4 / 21, 0, 0, 0],
    ![0, 0, 7 / 17, 0],
    ![0, 1 / 15, 0, 5 / 26]]

theorem deadlockRationalBlockHazard_nonneg :
    ∀ phase who, 0 ≤ deadlockRationalBlockHazard phase who := by
  intro phase who
  fin_cases phase <;> fin_cases who <;> norm_num [deadlockRationalBlockHazard]

theorem deadlockRationalBlockHazard_le_one :
    ∀ phase who, deadlockRationalBlockHazard phase who ≤ 1 := by
  intro phase who
  fin_cases phase <;> fin_cases who <;> norm_num [deadlockRationalBlockHazard]

/-- The desired value at the start of the block. -/
def deadlockRationalBlockValue (s : Payoff Player) : Payoff Player :=
  fun who ↦ s who + ![0, 5 / 7, 8 / 21, 1 / 7] who

/-- The value after the `{0}` phase. -/
def deadlockRationalBlockMiddleValue (s : Payoff Player) : Payoff Player :=
  fun who ↦ s who + ![0, 7 / 17, 0, 7 / 17] who

/-- The value after the `{2}` phase and before the joint phase. -/
def deadlockRationalBlockJointValue (s : Payoff Player) : Payoff Player :=
  fun who ↦ s who + ![7 / 10, 0, 0, 0] who

/-- The three cyclic phase values. -/
def deadlockRationalBlockCycleValue (s : Payoff Player) : Fin 3 → Payoff Player :=
  ![deadlockRationalBlockValue s, deadlockRationalBlockMiddleValue s,
    deadlockRationalBlockJointValue s]

/-- The closed four-row path expected by `IsQuittingBlockCertificate`. -/
def deadlockRationalBlockValuePath (s : Payoff Player) : Fin 4 → Payoff Player :=
  ![deadlockRationalBlockValue s, deadlockRationalBlockMiddleValue s,
    deadlockRationalBlockJointValue s, deadlockRationalBlockValue s]

private theorem deadlockRationalBlockRoot_zero_active :
    IsQuittingActiveRoot {0}
      (quittingBlockCycle deadlockRationalBlockHazard
        deadlockRationalBlockHazard_nonneg deadlockRationalBlockHazard_le_one 0) := by
  intro who hwho
  fin_cases who <;>
    simp [quittingBlockCycle, rootOfHazard, deadlockRationalBlockHazard] at hwho ⊢
  all_goals exact quittingHazardCoin_zero _ _

private theorem deadlockRationalBlockRoot_two_active :
    IsQuittingActiveRoot {2}
      (quittingBlockCycle deadlockRationalBlockHazard
        deadlockRationalBlockHazard_nonneg deadlockRationalBlockHazard_le_one 1) := by
  intro who hwho
  fin_cases who <;>
    simp [quittingBlockCycle, rootOfHazard, deadlockRationalBlockHazard] at hwho ⊢
  all_goals exact quittingHazardCoin_zero _ _

private theorem deadlockRationalBlockRoot_joint_active :
    IsQuittingActiveRoot {1, 3}
      (quittingBlockCycle deadlockRationalBlockHazard
        deadlockRationalBlockHazard_nonneg deadlockRationalBlockHazard_le_one 2) := by
  intro who hwho
  fin_cases who <;>
    simp [quittingBlockCycle, rootOfHazard, deadlockRationalBlockHazard] at hwho ⊢
  all_goals exact quittingHazardCoin_zero _ _

theorem deadlockRationalBlockRoot_zero_successor
    {reward' : {S : Finset Player // S.Nonempty} → Payoff Player}
    {s : Payoff Player} (h : IsDeadlockRationalJointBlockCompletion reward' s) :
    quittingRootSuccessorPayoff reward' (deadlockRationalBlockMiddleValue s)
        (quittingBlockCycle deadlockRationalBlockHazard
          deadlockRationalBlockHazard_nonneg deadlockRationalBlockHazard_le_one 0) =
      deadlockRationalBlockValue s := by
  funext who
  change quittingRootExpectedPayoff reward' (deadlockRationalBlockMiddleValue s)
    (quittingBlockCycle deadlockRationalBlockHazard
      deadlockRationalBlockHazard_nonneg deadlockRationalBlockHazard_le_one 0) who = _
  rw [quittingRootExpectedPayoff_singleton_active reward'
    (deadlockRationalBlockMiddleValue s) _ 0 who
    deadlockRationalBlockRoot_zero_active]
  rw [hazardOfRoot_quittingBlockCycle, literalSingletonTerminal_eq, h.singleton]
  fin_cases who <;>
    norm_num [deadlockRationalBlockHazard, deadlockRationalBlockMiddleValue,
      deadlockRationalBlockValue, deadlockMatrix] <;> ring

theorem deadlockRationalBlockRoot_two_successor
    {reward' : {S : Finset Player // S.Nonempty} → Payoff Player}
    {s : Payoff Player} (h : IsDeadlockRationalJointBlockCompletion reward' s) :
    quittingRootSuccessorPayoff reward' (deadlockRationalBlockJointValue s)
        (quittingBlockCycle deadlockRationalBlockHazard
          deadlockRationalBlockHazard_nonneg deadlockRationalBlockHazard_le_one 1) =
      deadlockRationalBlockMiddleValue s := by
  funext who
  change quittingRootExpectedPayoff reward' (deadlockRationalBlockJointValue s)
    (quittingBlockCycle deadlockRationalBlockHazard
      deadlockRationalBlockHazard_nonneg deadlockRationalBlockHazard_le_one 1) who = _
  rw [quittingRootExpectedPayoff_singleton_active reward'
    (deadlockRationalBlockJointValue s) _ 2 who
    deadlockRationalBlockRoot_two_active]
  rw [hazardOfRoot_quittingBlockCycle, literalSingletonTerminal_eq, h.singleton]
  fin_cases who <;>
    simp [deadlockRationalBlockHazard, deadlockRationalBlockJointValue,
      deadlockRationalBlockMiddleValue, deadlockMatrix,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three] <;> ring

theorem deadlockRationalBlockRoot_joint_successor
    {reward' : {S : Finset Player // S.Nonempty} → Payoff Player}
    {s : Payoff Player} (h : IsDeadlockRationalJointBlockCompletion reward' s) :
    quittingRootSuccessorPayoff reward' (deadlockRationalBlockValue s)
        (quittingBlockCycle deadlockRationalBlockHazard
          deadlockRationalBlockHazard_nonneg deadlockRationalBlockHazard_le_one 2) =
      deadlockRationalBlockJointValue s := by
  funext who
  change quittingRootExpectedPayoff reward' (deadlockRationalBlockValue s)
    (quittingBlockCycle deadlockRationalBlockHazard
      deadlockRationalBlockHazard_nonneg deadlockRationalBlockHazard_le_one 2) who = _
  rw [quittingRootExpectedPayoff_pair_active reward'
    (deadlockRationalBlockValue s) _ 1 3 who (by decide)
    deadlockRationalBlockRoot_joint_active]
  simp only [hazardOfRoot_quittingBlockCycle]
  rw [literalSingletonTerminal_eq, literalSingletonTerminal_eq,
    h.singleton, h.singleton, h.pair_one_three]
  fin_cases who <;>
    simp [deadlockRationalBlockHazard, deadlockRationalBlockValue,
      deadlockRationalBlockJointValue, deadlockMatrix] <;> ring

/-- The three displayed phase values solve the exact closed recursion. -/
theorem deadlockRationalBlock_isOnPathValue
    {reward' : {S : Finset Player // S.Nonempty} → Payoff Player}
    {s : Payoff Player} (h : IsDeadlockRationalJointBlockCompletion reward' s) :
    IsQuittingBlockOnPathValue reward' deadlockRationalBlockHazard
      (deadlockRationalBlockCycleValue s) := by
  rw [isQuittingBlockOnPathValue_iff_rootSuccessorPayoff
    deadlockRationalBlockHazard_nonneg deadlockRationalBlockHazard_le_one]
  intro phase
  fin_cases phase
  · exact deadlockRationalBlockRoot_zero_successor h |>.symm
  · exact deadlockRationalBlockRoot_two_successor h |>.symm
  · exact deadlockRationalBlockRoot_joint_successor h |>.symm

theorem deadlockRationalBlock_oneTurnSurvival_lt_one :
    (∏ phase : Fin 3, continueMass (deadlockRationalBlockHazard phase)) < 1 := by
  norm_num [continueMass, deadlockRationalBlockHazard, Fin.prod_univ_succ]

/-- The value path is reward-bounded because its exact closed recursion has
positive one-period absorption. -/
theorem deadlockRationalBlockValuePath_box
    {reward' : {S : Finset Player // S.Nonempty} → Payoff Player}
    {s : Payoff Player} (h : IsDeadlockRationalJointBlockCompletion reward' s)
    (stage : Fin 4) (who : Player) :
    |deadlockRationalBlockValuePath s stage who| ≤
      quittingRewardBound reward' := by
  have hbox :=
    abs_le_quittingRewardBound_of_isQuittingBlockOnPathValue_of_absorbing
      deadlockRationalBlockHazard_nonneg deadlockRationalBlockHazard_le_one
      (deadlockRationalBlock_isOnPathValue h)
      deadlockRationalBlock_oneTurnSurvival_lt_one
  fin_cases stage
  · simpa [deadlockRationalBlockValuePath, deadlockRationalBlockCycleValue] using
      hbox (0 : Fin 3) who
  · simpa [deadlockRationalBlockValuePath, deadlockRationalBlockCycleValue] using
      hbox (1 : Fin 3) who
  · simpa [deadlockRationalBlockValuePath, deadlockRationalBlockCycleValue] using
      hbox (2 : Fin 3) who
  · simpa [deadlockRationalBlockValuePath, deadlockRationalBlockCycleValue] using
      hbox (0 : Fin 3) who

/-! ## Exact endpoint comparisons -/

@[simp] private theorem expect_deadlockRationalBlockCoin
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : Bool → ℝ) :
    expect (quittingHazardCoin p hp0 hp1) f =
      (1 - p) * f false + p * f true := by
  rw [expect_eq_sum, Fintype.sum_bool]
  simp
  ring

@[simp] private theorem quitters_only_zero :
    {who : Player | ![true, false, false, false] who = true} = {0} := by
  ext who
  fin_cases who <;> simp

@[simp] private theorem quitters_only_one :
    {who : Player | ![false, true, false, false] who = true} = {1} := by
  ext who
  fin_cases who <;> simp

@[simp] private theorem quitters_only_two :
    {who : Player | ![false, false, true, false] who = true} = {2} := by
  ext who
  fin_cases who <;> simp

@[simp] private theorem quitters_only_three :
    {who : Player | ![false, false, false, true] who = true} = {3} := by
  ext who
  fin_cases who <;> simp

@[simp] private theorem quitters_zero_one :
    {who : Player | ![true, true, false, false] who = true} = {0, 1} := by
  ext who
  fin_cases who <;> simp

@[simp] private theorem quitters_zero_two :
    {who : Player | ![true, false, true, false] who = true} = {0, 2} := by
  ext who
  fin_cases who <;> simp

@[simp] private theorem quitters_zero_three :
    {who : Player | ![true, false, false, true] who = true} = {0, 3} := by
  ext who
  fin_cases who <;> simp

@[simp] private theorem quitters_one_two :
    {who : Player | ![false, true, true, false] who = true} = {1, 2} := by
  ext who
  fin_cases who <;> simp

@[simp] private theorem quitters_one_three :
    {who : Player | ![false, true, false, true] who = true} = {1, 3} := by
  ext who
  fin_cases who <;> simp

@[simp] private theorem quitters_two_three :
    {who : Player | ![false, false, true, true] who = true} = {2, 3} := by
  ext who
  fin_cases who <;> simp

@[simp] private theorem quitters_zero_one_three :
    {who : Player | ![true, true, false, true] who = true} = {0, 1, 3} := by
  ext who
  fin_cases who <;> simp

@[simp] private theorem quitters_one_two_three :
    {who : Player | ![false, true, true, true] who = true} = {1, 2, 3} := by
  ext who
  fin_cases who <;> simp

private theorem reward_quitters_only_zero
    (reward' : {S : Finset Player // S.Nonempty} → Payoff Player)
    (hne : ({who : Player | ![true, false, false, false] who = true} :
      Finset Player).Nonempty) (who : Player) :
    reward' ⟨({player | ![true, false, false, false] player = true} : Finset Player), hne⟩ who =
      reward' (quittingSingletonTerminal 0) who := by
  congr 1

private theorem reward_quitters_only_one
    (reward' : {S : Finset Player // S.Nonempty} → Payoff Player)
    (hne : ({who : Player | ![false, true, false, false] who = true} :
      Finset Player).Nonempty) (who : Player) :
    reward' ⟨({player | ![false, true, false, false] player = true} : Finset Player), hne⟩ who =
      reward' (quittingSingletonTerminal 1) who := by
  congr 1

private theorem reward_quitters_only_two
    (reward' : {S : Finset Player // S.Nonempty} → Payoff Player)
    (hne : ({who : Player | ![false, false, true, false] who = true} :
      Finset Player).Nonempty) (who : Player) :
    reward' ⟨({player | ![false, false, true, false] player = true} : Finset Player), hne⟩ who =
      reward' (quittingSingletonTerminal 2) who := by
  congr 1

private theorem reward_quitters_only_three
    (reward' : {S : Finset Player // S.Nonempty} → Payoff Player)
    (hne : ({who : Player | ![false, false, false, true] who = true} :
      Finset Player).Nonempty) (who : Player) :
    reward' ⟨({player | ![false, false, false, true] player = true} : Finset Player), hne⟩ who =
      reward' (quittingSingletonTerminal 3) who := by
  congr 1

private theorem reward_quitters_zero_one
    (reward' : {S : Finset Player // S.Nonempty} → Payoff Player)
    (hne : ({who : Player | ![true, true, false, false] who = true} :
      Finset Player).Nonempty) (who : Player) :
    reward' ⟨({player | ![true, true, false, false] player = true} : Finset Player), hne⟩ who =
      reward' ⟨{0, 1}, by simp⟩ who := by
  congr 1

private theorem reward_quitters_zero_two
    (reward' : {S : Finset Player // S.Nonempty} → Payoff Player)
    (hne : ({who : Player | ![true, false, true, false] who = true} :
      Finset Player).Nonempty) (who : Player) :
    reward' ⟨({player | ![true, false, true, false] player = true} : Finset Player), hne⟩ who =
      reward' ⟨{0, 2}, by simp⟩ who := by
  congr 1

private theorem reward_quitters_zero_three
    (reward' : {S : Finset Player // S.Nonempty} → Payoff Player)
    (hne : ({who : Player | ![true, false, false, true] who = true} :
      Finset Player).Nonempty) (who : Player) :
    reward' ⟨({player | ![true, false, false, true] player = true} : Finset Player), hne⟩ who =
      reward' ⟨{0, 3}, by simp⟩ who := by
  congr 1

private theorem reward_quitters_one_two
    (reward' : {S : Finset Player // S.Nonempty} → Payoff Player)
    (hne : ({who : Player | ![false, true, true, false] who = true} :
      Finset Player).Nonempty) (who : Player) :
    reward' ⟨({player | ![false, true, true, false] player = true} : Finset Player), hne⟩ who =
      reward' ⟨{1, 2}, by simp⟩ who := by
  congr 1

private theorem reward_quitters_one_three
    (reward' : {S : Finset Player // S.Nonempty} → Payoff Player)
    (hne : ({who : Player | ![false, true, false, true] who = true} :
      Finset Player).Nonempty) (who : Player) :
    reward' ⟨({player | ![false, true, false, true] player = true} : Finset Player), hne⟩ who =
      reward' ⟨{1, 3}, by simp⟩ who := by
  congr 1

private theorem reward_quitters_two_three
    (reward' : {S : Finset Player // S.Nonempty} → Payoff Player)
    (hne : ({who : Player | ![false, false, true, true] who = true} :
      Finset Player).Nonempty) (who : Player) :
    reward' ⟨({player | ![false, false, true, true] player = true} : Finset Player), hne⟩ who =
      reward' ⟨{2, 3}, by simp⟩ who := by
  congr 1

private theorem reward_quitters_zero_one_three
    (reward' : {S : Finset Player // S.Nonempty} → Payoff Player)
    (hne : ({who : Player | ![true, true, false, true] who = true} :
      Finset Player).Nonempty) (who : Player) :
    reward' ⟨({player | ![true, true, false, true] player = true} : Finset Player), hne⟩ who =
      reward' ⟨{0, 1, 3}, by simp⟩ who := by
  congr 1

private theorem reward_quitters_one_two_three
    (reward' : {S : Finset Player // S.Nonempty} → Payoff Player)
    (hne : ({who : Player | ![false, true, true, true] who = true} :
      Finset Player).Nonempty) (who : Player) :
    reward' ⟨({player | ![false, true, true, true] player = true} : Finset Player), hne⟩ who =
      reward' ⟨{1, 2, 3}, by simp⟩ who := by
  congr 1

theorem deadlockRationalBlockRoot_zero_endpointDifference
    {reward' : {S : Finset Player // S.Nonempty} → Payoff Player}
    {s : Payoff Player} (h : IsDeadlockRationalJointBlockCompletion reward' s)
    (who : Player) :
    quittingRootEndpointDifference reward' (deadlockRationalBlockMiddleValue s)
        (quittingBlockCycle deadlockRationalBlockHazard
          deadlockRationalBlockHazard_nonneg deadlockRationalBlockHazard_le_one 0) who =
      ![0,
        (4 / 21) * (reward' ⟨{0, 1}, by simp⟩ 1 - s 1 - 15 / 4),
        (4 / 21) * (reward' ⟨{0, 2}, by simp⟩ 2 - s 2 - 2),
        (4 / 21) * (reward' ⟨{0, 3}, by simp⟩ 3 - s 3 - 3 / 4)] who := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4,
    Math.PMFProduct.expect_pmfPi_fin4]
  fin_cases who <;>
    simp +decide [quittingBlockCycle, rootOfHazard, deadlockRationalBlockHazard,
      quittingRootPayoff, quittingQuitters, h.literalSingleton, deadlockMatrix,
      deadlockRationalBlockMiddleValue, quittingSingletonTerminal,
      reward_quitters_only_zero,
      reward_quitters_only_one, reward_quitters_only_two,
      reward_quitters_only_three, reward_quitters_zero_one,
      reward_quitters_zero_two, reward_quitters_zero_three] <;> ring

theorem deadlockRationalBlockRoot_two_endpointDifference
    {reward' : {S : Finset Player // S.Nonempty} → Payoff Player}
    {s : Payoff Player} (h : IsDeadlockRationalJointBlockCompletion reward' s)
    (who : Player) :
    quittingRootEndpointDifference reward' (deadlockRationalBlockJointValue s)
        (quittingBlockCycle deadlockRationalBlockHazard
          deadlockRationalBlockHazard_nonneg deadlockRationalBlockHazard_le_one 1) who =
      ![(7 / 17) * (reward' ⟨{0, 2}, by simp⟩ 0 - s 0),
        (7 / 17) * (reward' ⟨{1, 2}, by simp⟩ 1 - s 1 - 1),
        0,
        (7 / 17) * (reward' ⟨{2, 3}, by simp⟩ 3 - s 3 - 1)] who := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4,
    Math.PMFProduct.expect_pmfPi_fin4]
  fin_cases who <;>
    simp +decide [quittingBlockCycle, rootOfHazard, deadlockRationalBlockHazard,
      quittingRootPayoff, quittingQuitters, h.literalSingleton, deadlockMatrix,
      deadlockRationalBlockJointValue, quittingSingletonTerminal,
      reward_quitters_only_zero,
      reward_quitters_only_one, reward_quitters_only_two,
      reward_quitters_only_three, reward_quitters_zero_two,
      reward_quitters_one_two, reward_quitters_two_three] <;> ring

theorem deadlockRationalBlockRoot_joint_endpointDifference
    {reward' : {S : Finset Player // S.Nonempty} → Payoff Player}
    {s : Payoff Player} (h : IsDeadlockRationalJointBlockCompletion reward' s)
    (who : Player) :
    quittingRootEndpointDifference reward' (deadlockRationalBlockValue s)
        (quittingBlockCycle deadlockRationalBlockHazard
          deadlockRationalBlockHazard_nonneg deadlockRationalBlockHazard_le_one 2) who =
      ![(1 / 390) *
          (21 * (reward' ⟨{0, 1}, by simp⟩ 0 - s 0) +
            70 * (reward' ⟨{0, 3}, by simp⟩ 0 - s 0) +
            5 * (reward' ⟨{0, 1, 3}, by simp⟩ 0 - s 0) - 273),
        0,
        (1 / 390) *
          (21 * (reward' ⟨{1, 2}, by simp⟩ 2 - s 2) +
            70 * (reward' ⟨{2, 3}, by simp⟩ 2 - s 2) +
            5 * (reward' ⟨{1, 2, 3}, by simp⟩ 2 - s 2)),
        0] who := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4,
    Math.PMFProduct.expect_pmfPi_fin4]
  fin_cases who <;>
    simp +decide [quittingBlockCycle, rootOfHazard, deadlockRationalBlockHazard,
      quittingRootPayoff, quittingQuitters, h.literalSingleton, h.pair_one_three,
      deadlockMatrix, deadlockRationalBlockValue, quittingSingletonTerminal,
      reward_quitters_only_zero,
      reward_quitters_only_one, reward_quitters_only_two,
      reward_quitters_only_three, reward_quitters_zero_one,
      reward_quitters_zero_three, reward_quitters_one_two,
      reward_quitters_one_three, reward_quitters_two_three,
      reward_quitters_zero_one_three, reward_quitters_one_two_three] <;> ring

theorem deadlockRationalBlockRoot_zero_isZeroEndpointNash
    {reward' : {S : Finset Player // S.Nonempty} → Payoff Player}
    {s : Payoff Player} (h : IsDeadlockRationalJointBlockCompletion reward' s) :
    IsεQuittingRootEndpointNash reward' (deadlockRationalBlockMiddleValue s) 0
      (quittingBlockCycle deadlockRationalBlockHazard
        deadlockRationalBlockHazard_nonneg deadlockRationalBlockHazard_le_one 0) := by
  intro who
  rw [deadlockRationalBlockRoot_zero_endpointDifference h]
  fin_cases who <;> simp [deadlockRationalBlockHazard] <;>
    nlinarith [h.pair_zero_one_one, h.pair_zero_two_two,
      h.pair_zero_three_three]

theorem deadlockRationalBlockRoot_two_isZeroEndpointNash
    {reward' : {S : Finset Player // S.Nonempty} → Payoff Player}
    {s : Payoff Player} (h : IsDeadlockRationalJointBlockCompletion reward' s) :
    IsεQuittingRootEndpointNash reward' (deadlockRationalBlockJointValue s) 0
      (quittingBlockCycle deadlockRationalBlockHazard
        deadlockRationalBlockHazard_nonneg deadlockRationalBlockHazard_le_one 1) := by
  intro who
  rw [deadlockRationalBlockRoot_two_endpointDifference h]
  fin_cases who <;> simp [deadlockRationalBlockHazard] <;>
    nlinarith [h.pair_zero_two_zero, h.pair_one_two_one,
      h.pair_two_three_three]

theorem deadlockRationalBlockRoot_joint_isZeroEndpointNash
    {reward' : {S : Finset Player // S.Nonempty} → Payoff Player}
    {s : Payoff Player} (h : IsDeadlockRationalJointBlockCompletion reward' s) :
    IsεQuittingRootEndpointNash reward' (deadlockRationalBlockValue s) 0
      (quittingBlockCycle deadlockRationalBlockHazard
        deadlockRationalBlockHazard_nonneg deadlockRationalBlockHazard_le_one 2) := by
  intro who
  rw [deadlockRationalBlockRoot_joint_endpointDifference h]
  fin_cases who <;> simp [deadlockRationalBlockHazard] <;>
    nlinarith [h.joint_cap_zero, h.joint_cap_two]

/-- Every player sees positive opponent absorption over a three-phase turn.
This is independent of the reward table and of the player's own hazards. -/
theorem deadlockRationalBlock_deletedSurvival_lt_one (who : Player) :
    (∏ phase : Fin 3,
      continueMass (quittingBlockDeletedHazard
        deadlockRationalBlockHazard who phase)) < 1 := by
  fin_cases who <;>
    simp +decide [continueMass, quittingBlockDeletedHazard,
      deadlockRationalBlockHazard, Fin.prod_univ_succ, Function.update] <;>
    norm_num

theorem deadlockRationalBlock_admissible
    (reward' : {S : Finset Player // S.Nonempty} → Payoff Player) :
    ∀ who : Player,
      (∏ phase : Fin 3,
          continueMass (quittingBlockDeletedHazard
            deadlockRationalBlockHazard who phase)) < 1 ∨
        0 ≤ reward' (quittingSingletonTerminal who) who := by
  intro who
  exact Or.inl (deadlockRationalBlock_deletedSurvival_lt_one who)

/-! ## Certificate and semantic conclusions -/

/-- The rational three-phase profile is an exact block certificate throughout
the raw polyhedral reward class. -/
theorem isQuittingBlockCertificate_of_isDeadlockRationalJointBlockCompletion
    {reward' : {S : Finset Player // S.Nonempty} → Payoff Player}
    {s : Payoff Player} (h : IsDeadlockRationalJointBlockCompletion reward' s) :
    IsQuittingBlockCertificate (m := 2) reward' deadlockRationalBlockHazard
      (deadlockRationalBlockValuePath s) := by
  refine isQuittingBlockCertificate_of_root deadlockRationalBlockHazard_nonneg
    deadlockRationalBlockHazard_le_one (deadlockRationalBlockValuePath_box h)
    rfl ?_ ?_ ?_ (deadlockRationalBlock_admissible reward')
  · intro phase
    fin_cases phase
    · exact (deadlockRationalBlockRoot_zero_successor h).symm
    · exact (deadlockRationalBlockRoot_two_successor h).symm
    · exact (deadlockRationalBlockRoot_joint_successor h).symm
  · intro phase
    fin_cases phase
    · exact deadlockRationalBlockRoot_zero_isZeroEndpointNash h
    · exact deadlockRationalBlockRoot_two_isZeroEndpointNash h
    · exact deadlockRationalBlockRoot_joint_isZeroEndpointNash h
  · refine ⟨0, ?_⟩
    norm_num [continueMass, deadlockRationalBlockHazard, Fin.prod_univ_succ]

/-- The exact fixed target produced by the rational polyhedral block.  The
deviation class is all behavioral strategies. -/
theorem isUniformEquilibriumPayoff_of_isDeadlockRationalJointBlockCompletion
    {reward' : {S : Finset Player // S.Nonempty} → Payoff Player}
    {s : Payoff Player} (h : IsDeadlockRationalJointBlockCompletion reward' s) :
    (quittingGame reward').IsUniformEquilibriumPayoff none
      (deadlockRationalBlockValue s) := by
  simpa [deadlockRationalBlockValuePath] using
    isUniformEquilibriumPayoff_of_isQuittingBlockCertificate
      (isQuittingBlockCertificate_of_isDeadlockRationalJointBlockCompletion h)

/-- Existential consequence exposing only the existence of a fixed
uniform-equilibrium payoff. -/
theorem exists_uniformEquilibriumPayoff_of_isDeadlockRationalJointBlockCompletion
    {reward' : {S : Finset Player // S.Nonempty} → Payoff Player}
    {s : Payoff Player} (h : IsDeadlockRationalJointBlockCompletion reward' s) :
    ∃ x : Payoff Player,
      (quittingGame reward').IsUniformEquilibriumPayoff none x :=
  ⟨deadlockRationalBlockValue s,
    isUniformEquilibriumPayoff_of_isDeadlockRationalJointBlockCompletion h⟩

end FullCoreDeadlock
end GameTheory

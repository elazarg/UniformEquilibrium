/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.PayoffProcess.Basic
import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality
import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryRestart

/-!
# Stability of a quitting path under time-varying payoff tables

The stopping law is independent of the numerical rewards.  Consequently a
uniform coordinate perturbation of every future table changes the path
payoff by at most the perturbation size: the survival-weighted absorption
probabilities have total mass at most one.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Expected payoff along live product roots when the terminal table may vary
with the stage. -/
def quittingVariableTailValue
    (reward : ℕ → ({S : Finset ι // S.Nonempty} → Payoff ι))
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ) : ℝ :=
  ∑' offset : ℕ,
    quittingJointSurvivalWeight roots start offset *
      quittingRootAbsorbingContribution (reward (start + offset))
        (roots (start + offset)) who

omit [DecidableEq ι] in
/-- The constant-table path series along a behavior profile's live spine is
its stochastic-game terminal payoff. -/
theorem quittingComplementarityTailValue_profileLiveRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingComplementarityTailValue reward
        (quittingProfileLiveRoot reward profile) who 0 =
      quittingTerminalPayoff reward profile who := by
  rw [show quittingComplementarityTailValue reward
      (quittingProfileLiveRoot reward profile) who 0 =
    quittingRootSequenceTerminalValue reward
      (quittingProfileLiveRoot reward profile) who 0 by
    symm
    exact quittingRootSequenceTerminalValue_eq_tsum_absorbingContribution
      reward (quittingProfileLiveRoot reward profile) who 0]
  exact (quittingTerminalPayoff_eq_rootSequence_profileLiveRoot
    reward profile who).symm

omit [DecidableEq ι] in
/-- Absorbing contribution is linear in the terminal reward table. -/
theorem quittingRootAbsorbingContribution_sub
    (first second : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingRootAbsorbingContribution first root who -
        quittingRootAbsorbingContribution second root who =
      quittingRootAbsorbingContribution
        (fun terminal player => first terminal player - second terminal player)
        root who := by
  classical
  unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
  rw [← expect_sub]
  apply congrArg (expect (pmfPi root))
  funext action
  unfold quittingRootPayoff
  split_ifs <;> simp

omit [DecidableEq ι] in
/-- A uniform coordinate perturbation changes one root contribution by at
most the perturbation size times that root's absorption probability. -/
theorem abs_quittingRootAbsorbingContribution_sub_le
    (first second : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) {ε : ℝ}
    (hclose : ∀ terminal player,
      |first terminal player - second terminal player| ≤ ε) :
    |quittingRootAbsorbingContribution first root who -
        quittingRootAbsorbingContribution second root who| ≤
      ε * quittingRootAbsorptionMass root := by
  rw [quittingRootAbsorbingContribution_sub]
  exact abs_quittingRootAbsorbingContribution_le _ root who ε hclose

omit [DecidableEq ι] in
/-- Every finite prefix of the absolute payoff difference is bounded by the
uniform table error. -/
theorem sum_abs_quittingVariableTailDifference_le
    (reward : ℕ → ({S : Finset ι // S.Nonempty} → Payoff ι))
    (base : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hclose : ∀ offset terminal player,
      |reward (start + offset) terminal player - base terminal player| ≤ ε) :
    (∑ offset ∈ Finset.range fuel,
        |quittingJointSurvivalWeight roots start offset *
          (quittingRootAbsorbingContribution (reward (start + offset))
              (roots (start + offset)) who -
            quittingRootAbsorbingContribution base
              (roots (start + offset)) who)|) ≤ ε := by
  calc
    _ ≤ ∑ offset ∈ Finset.range fuel,
          quittingJointSurvivalWeight roots start offset *
            (ε * quittingRootAbsorptionMass
              (roots (start + offset))) := by
      apply Finset.sum_le_sum
      intro offset _
      rw [abs_mul, abs_of_nonneg
        (quittingJointSurvivalWeight_nonneg roots start offset)]
      exact mul_le_mul_of_nonneg_left
        (abs_quittingRootAbsorbingContribution_sub_le
          _ _ _ who (hclose offset))
        (quittingJointSurvivalWeight_nonneg roots start offset)
    _ = ε * (1 - quittingJointSurvivalWeight roots start fuel) := by
      rw [show (∑ offset ∈ Finset.range fuel,
          quittingJointSurvivalWeight roots start offset *
            (ε * quittingRootAbsorptionMass
              (roots (start + offset)))) =
          ε * ∑ offset ∈ Finset.range fuel,
            quittingJointSurvivalWeight roots start offset *
              (1 - quittingStationaryContinueMass
                (roots (start + offset))) by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro offset _
        rw [quittingRootAbsorptionMass]
        ring]
      rw [sum_quittingJointSurvivalWeight_mul_one_sub_continueMass]
    _ ≤ ε := by
      have hsurvival := quittingJointSurvivalWeight_nonneg roots start fuel
      nlinarith

omit [DecidableEq ι] in
/-- The survival-weighted difference between a varying table sequence and a
fixed table is absolutely summable under a uniform coordinate bound. -/
theorem summable_quittingVariableTailDifference
    (reward : ℕ → ({S : Finset ι // S.Nonempty} → Payoff ι))
    (base : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hclose : ∀ offset terminal player,
      |reward (start + offset) terminal player - base terminal player| ≤ ε) :
    Summable fun offset =>
      quittingJointSurvivalWeight roots start offset *
        (quittingRootAbsorbingContribution (reward (start + offset))
            (roots (start + offset)) who -
          quittingRootAbsorbingContribution base
            (roots (start + offset)) who) := by
  apply Summable.of_abs
  apply summable_of_sum_range_le (c := ε)
  · intro offset
    exact abs_nonneg _
  · intro fuel
    exact sum_abs_quittingVariableTailDifference_le
      reward base roots who start fuel hε hclose

omit [DecidableEq ι] in
/-- A uniformly bounded varying reward path has an absolutely summable payoff
series. -/
theorem summable_quittingVariableTailValue
    (reward : ℕ → ({S : Finset ι // S.Nonempty} → Payoff ι))
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ offset terminal player,
      |reward (start + offset) terminal player| ≤ bound) :
    Summable fun offset ↦
      quittingJointSurvivalWeight roots start offset *
        quittingRootAbsorbingContribution (reward (start + offset))
          (roots (start + offset)) who := by
  classical
  let zeroReward : {S : Finset ι // S.Nonempty} → Payoff ι := fun _ _ ↦ 0
  have hsummable := summable_quittingVariableTailDifference
    reward zeroReward roots who start hbound (fun offset terminal player ↦ by
      simpa only [zeroReward, sub_zero] using hreward offset terminal player)
  have hzero (root : ι → PMF Bool) :
      quittingRootAbsorbingContribution zeroReward root who = 0 := by
    unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
    rw [expect_eq_sum]
    apply Finset.sum_eq_zero
    intro action _
    by_cases hquit : (quittingQuitters action).Nonempty
    · simp [quittingRootPayoff, zeroReward, hquit]
    · simp [quittingRootPayoff, hquit]
  convert hsummable using 1
  funext offset
  rw [hzero]
  ring

omit [DecidableEq ι] in
/-- The varying-table tail value satisfies its exact one-stage Bellman
recursion whenever the future reward coordinates have a common bound. -/
theorem quittingVariableTailValue_eq
    (reward : ℕ → ({S : Finset ι // S.Nonempty} → Payoff ι))
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ offset terminal player,
      |reward (start + offset) terminal player| ≤ bound) :
    quittingVariableTailValue reward roots who start =
      quittingRootAbsorbingContribution (reward start) (roots start) who +
        quittingStationaryContinueMass (roots start) *
          quittingVariableTailValue reward roots who (start + 1) := by
  unfold quittingVariableTailValue
  have hsummable := summable_quittingVariableTailValue
    reward roots who start hbound hreward
  rw [hsummable.tsum_eq_zero_add]
  have hzero : quittingJointSurvivalWeight roots start 0 *
      quittingRootAbsorbingContribution (reward (start + 0))
        (roots (start + 0)) who =
      quittingRootAbsorbingContribution (reward start) (roots start) who := by
    simp [quittingJointSurvivalWeight, quittingFiniteContinueWeight]
  rw [hzero]
  congr 1
  have hterm : ∀ offset : ℕ,
      quittingJointSurvivalWeight roots start (offset + 1) *
          quittingRootAbsorbingContribution
            (reward (start + (offset + 1)))
            (roots (start + (offset + 1))) who =
        quittingStationaryContinueMass (roots start) *
          (quittingJointSurvivalWeight roots (start + 1) offset *
            quittingRootAbsorbingContribution
              (reward (start + 1 + offset))
              (roots (start + 1 + offset)) who) := by
    intro offset
    have hsplit : quittingJointSurvivalWeight roots start (1 + offset) =
        quittingJointSurvivalWeight roots start 1 *
          quittingJointSurvivalWeight roots (start + 1) offset :=
      quittingJointSurvivalWeight_add roots start 1 offset
    have hone : quittingJointSurvivalWeight roots start 1 =
        quittingStationaryContinueMass (roots start) := by
      simp [quittingJointSurvivalWeight, quittingFiniteContinueWeight]
    rw [show offset + 1 = 1 + offset by omega, hsplit, hone,
      show start + (1 + offset) = start + 1 + offset by omega]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left]

omit [DecidableEq ι] in
/-- Re-indexing both the reward tables and live roots at `start` turns a
global tail value into the corresponding stage-zero value. -/
theorem quittingVariableTailValue_eq_shift
    (reward : ℕ → ({S : Finset ι // S.Nonempty} → Payoff ι))
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ) :
    quittingVariableTailValue reward roots who start =
      quittingVariableTailValue (fun offset ↦ reward (start + offset))
        (fun offset ↦ roots (start + offset)) who 0 := by
  unfold quittingVariableTailValue
  apply congrArg tsum
  funext offset
  rw [← quittingJointSurvivalWeight_eq_shift roots start offset]
  simp only [Nat.zero_add]

omit [DecidableEq ι] in
/-- A stagewise-uniform `ε` perturbation changes the entire future stopping
payoff by at most `ε`. -/
theorem abs_quittingVariableTailValue_sub_le
    (reward : ℕ → ({S : Finset ι // S.Nonempty} → Payoff ι))
    (base : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hclose : ∀ offset terminal player,
      |reward (start + offset) terminal player - base terminal player| ≤ ε) :
    |quittingVariableTailValue reward roots who start -
        quittingComplementarityTailValue base roots who start| ≤ ε := by
  let difference : ℕ → ℝ := fun offset =>
    quittingJointSurvivalWeight roots start offset *
      (quittingRootAbsorbingContribution (reward (start + offset))
          (roots (start + offset)) who -
        quittingRootAbsorbingContribution base
          (roots (start + offset)) who)
  have hsummable : Summable difference :=
    summable_quittingVariableTailDifference reward base roots who start hε hclose
  have hnorm : |∑' offset, difference offset| ≤ ∑' offset, |difference offset| := by
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsummable.norm
  have hbound : (∑' offset, |difference offset|) ≤ ε :=
    Real.tsum_le_of_sum_range_le (fun offset => abs_nonneg (difference offset))
      (fun fuel => by
        simpa only [difference] using
          sum_abs_quittingVariableTailDifference_le
            reward base roots who start fuel hε hclose)
  have hconstant :=
    summable_quittingJointSurvivalWeight_mul_quittingRootAbsorbingContribution
      base roots who start
  have hvarying : Summable fun offset =>
      quittingJointSurvivalWeight roots start offset *
        quittingRootAbsorbingContribution (reward (start + offset))
          (roots (start + offset)) who := by
    have hadd := hsummable.add hconstant
    convert hadd using 1
    funext offset
    dsimp only [difference]
    ring
  have hrewrite : quittingVariableTailValue reward roots who start -
        quittingComplementarityTailValue base roots who start =
      ∑' offset, difference offset := by
    unfold quittingVariableTailValue quittingComplementarityTailValue
    rw [← hvarying.tsum_sub hconstant]
    apply congrArg tsum
    funext offset
    dsimp only [difference]
    ring
  rw [hrewrite]
  exact hnorm.trans hbound

omit [DecidableEq ι] in
/-- A uniformly bounded varying table sequence has path payoff bounded by the
same envelope, independently of the stopping law. -/
theorem abs_quittingVariableTailValue_le
    (reward : ℕ → ({S : Finset ι // S.Nonempty} → Payoff ι))
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ offset terminal player,
      |reward (start + offset) terminal player| ≤ bound) :
    |quittingVariableTailValue reward roots who start| ≤ bound := by
  let zeroReward : {S : Finset ι // S.Nonempty} → Payoff ι :=
    fun _ _ => 0
  have hstability := abs_quittingVariableTailValue_sub_le
    reward zeroReward roots who start hbound (by
      intro offset terminal player
      simpa only [zeroReward, sub_zero] using hreward offset terminal player)
  have hzero : quittingComplementarityTailValue zeroReward roots who start = 0 := by
    simp [quittingComplementarityTailValue, zeroReward,
      quittingRootAbsorbingContribution, quittingRootExpectedPayoff,
      quittingRootPayoff]
  simpa only [hzero, sub_zero] using hstability

end GameTheory

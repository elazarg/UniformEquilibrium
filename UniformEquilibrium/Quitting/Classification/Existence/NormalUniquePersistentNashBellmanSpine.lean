/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanClockReduction
import UniformEquilibrium.Quitting.Classification.AbnormalPlayers
import UniformEquilibrium.Quitting.Cycles.ConditionedDeletedClockSoloCompletion
import UniformEquilibrium.Quitting.Paths.PersistentDeletedClockTwoLabel

/-!
# Normal unique-persistent Nash--Bellman spines

A nonsummable marginal Quit clock forces complete absorption along every suffix.
If the same player's opponent clock is summable, the bounded Bellman values
concentrate quantitatively on that player's singleton reward vector.  Late
positive owner rows then feed the existing deleted-clock solo compiler.  Under
the exact Nash condition and punishment normality, the singleton vector is a
uniform-equilibrium payoff.

This is a conditional compiler for a supplied exact Nash--Bellman spine.  It
does not construct a spine with a unique persistent player, prove normality, or
show that arbitrary compact spine selection enters this branch.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped BigOperators Topology

variable {iota : Type} [Fintype iota] [DecidableEq iota]

private theorem exists_ge_pos_of_not_summable_nonneg
    {f : ℕ → ℝ} (hnonneg : ∀ time, 0 ≤ f time)
    (hnot : ¬ Summable f) (threshold : ℕ) :
    ∃ time, threshold ≤ time ∧ 0 < f time := by
  by_contra hnone
  push Not at hnone
  apply hnot
  have hzero : ∀ offset, f (offset + threshold) = 0 := fun offset ↦
    le_antisymm
      (hnone (offset + threshold) (Nat.le_add_left threshold offset))
      (hnonneg (offset + threshold))
  have hshift : Summable (fun offset ↦ f (offset + threshold)) := by
    have hconst : (fun offset ↦ f (offset + threshold)) =
        fun _ ↦ (0 : ℝ) := funext hzero
    rw [hconst]
    exact summable_zero
  exact (summable_nat_add_iff threshold).1 hshift

omit [DecidableEq iota] in
private theorem not_summable_rootAbsorptionMass_of_persistent
    (roots : ℕ → iota → PMF Bool) (owner : iota)
    (howner : ¬ Summable (quittingMarginalQuitHazard roots owner)) :
    ¬ Summable (fun time ↦ quittingRootAbsorptionMass (roots time)) := by
  intro habsorption
  apply howner
  exact habsorption.of_nonneg_of_le
    (quittingMarginalQuitHazard_nonneg roots owner)
    (fun time ↦
      quittingRoot_quitProbability_le_absorptionMass (roots time) owner)

omit [DecidableEq iota] in
private theorem tendsto_zero_jointSurvival_of_persistent
    (roots : ℕ → iota → PMF Bool) (owner : iota)
    (howner : ¬ Summable (quittingMarginalQuitHazard roots owner)) :
    ∀ start,
      Tendsto (quittingJointSurvivalWeight roots start) atTop (nhds 0) := by
  have habsorption :=
    not_summable_rootAbsorptionMass_of_persistent roots owner howner
  intro start
  apply tendsto_zero_quittingJointSurvivalWeight_of_not_summable_absorption
  intro hsuffix
  apply habsorption
  have hshift : Summable (fun offset ↦
      quittingRootAbsorptionMass (roots (offset + start))) := by
    simpa [Nat.add_comm] using hsuffix
  exact (summable_nat_add_iff start).1 hshift

/-- A bounded Bellman recursion with one persistent player and summable
opponent clock is quantitatively concentrated on that player's singleton
reward vector.  Stagewise Nash is not required for this estimate. -/
theorem abs_value_sub_soloReward_le_of_bounded_bellman
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (value : ℕ → Payoff iota) (roots : ℕ → iota → PMF Bool)
    (hbound : ∀ time who,
      |value time who| ≤ quittingRewardBound reward)
    (hpolicy : ∀ time, value time = quittingRootSuccessorPayoff reward
      (value (time + 1)) (roots time))
    (owner : iota)
    (howner : ¬ Summable (quittingMarginalQuitHazard roots owner))
    (hclock : Summable (quittingOpponentClockCharge roots owner))
    (time : ℕ) (who : iota) :
    |value time who - quittingSoloReward reward owner who| ≤
      2 * quittingRewardBound reward *
        quittingOpponentClockTailCharge roots owner time := by
  have hsurvival := tendsto_zero_jointSurvival_of_persistent roots owner howner
  have hvalue :=
    eq_quittingRootSequenceTerminalValue_of_exact_bounded_path_of_jointSurvival_tendsto_zero
      reward roots value hsurvival
      (abs_reward_le_quittingRewardBound reward) hbound hpolicy
  have hclockShift : Summable (fun offset ↦
      quittingOpponentClockCharge roots owner (time + offset)) := by
    have hshift : Summable (fun offset ↦
        quittingOpponentClockCharge roots owner (offset + time)) :=
      (summable_nat_add_iff time).2 hclock
    simpa [Nat.add_comm] using hshift
  have hconcentration :=
    abs_quittingRootSequenceTerminalValue_sub_soloReward_le_tailCharge
      reward roots owner who time
      (abs_reward_le_quittingRewardBound reward) (hsurvival time) hclockShift
  rw [← congrFun (hvalue time) who] at hconcentration
  exact hconcentration

/-- Canonical exact-spine form of the quantitative concentration estimate. -/
theorem IsCanonicalExactQuittingNashBellmanSpine.abs_value_sub_soloReward_le
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (value : ℕ → Payoff iota) (roots : ℕ → iota → PMF Bool)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots)
    (owner : iota)
    (howner : ¬ Summable (quittingMarginalQuitHazard roots owner))
    (hclock : Summable (quittingOpponentClockCharge roots owner))
    (time : ℕ) (who : iota) :
    |value time who - quittingSoloReward reward owner who| ≤
      2 * quittingRewardBound reward *
        quittingOpponentClockTailCharge roots owner time :=
  abs_value_sub_soloReward_le_of_bounded_bellman reward value roots
    hspine.1 hspine.2.1 owner howner hclock time who

/-- Under the persistent-owner and summable-opponent-clock hypotheses, all
coordinates of a canonical exact spine converge to the owner's singleton
reward vector. -/
theorem IsCanonicalExactQuittingNashBellmanSpine.tendsto_value_soloReward
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (value : ℕ → Payoff iota) (roots : ℕ → iota → PMF Bool)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots)
    (owner : iota)
    (howner : ¬ Summable (quittingMarginalQuitHazard roots owner))
    (hclock : Summable (quittingOpponentClockCharge roots owner)) :
    Tendsto value atTop (nhds (quittingSoloReward reward owner)) := by
  rw [tendsto_pi_nhds]
  intro who
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero
  · intro time
    exact dist_nonneg
  · intro time
    simpa [Real.dist_eq] using
      hspine.abs_value_sub_soloReward_le reward value roots owner howner
        hclock time who
  · have hclockZero : Summable (fun offset ↦
        quittingOpponentClockCharge roots owner (0 + offset)) := by
      simpa using hclock
    have htail := tendsto_quittingOpponentClockTailCharge_zero
      roots owner 0 hclockZero
    have htail' : Tendsto
        (quittingOpponentClockTailCharge roots owner) atTop (nhds 0) := by
      simpa only [Nat.zero_add] using htail
    have hscaled := htail'.const_mul (2 * quittingRewardBound reward)
    simpa using hscaled

/-- A persistent player with summable opponent clock supplies a singleton
uniform-equilibrium payoff when the exact spine is punishment-normal for that
player. -/
theorem
    IsCanonicalExactQuittingNashBellmanSpine.isUniformEquilibriumPayoff_soloReward_of_persistent
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (value : ℕ → Payoff iota) (roots : ℕ → iota → PMF Bool)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots)
    (owner : iota)
    (howner : ¬ Summable (quittingMarginalQuitHazard roots owner))
    (hclock : Summable (quittingOpponentClockCharge roots owner))
    (hnormal : IsQuittingNormalPlayer reward owner) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSoloReward reward owner) := by
  have hlate : ∀ threshold, ∃ time, threshold ≤ time ∧
      0 < quittingMarginalQuitHazard roots owner time :=
    exists_ge_pos_of_not_summable_nonneg
      (quittingMarginalQuitHazard_nonneg roots owner) howner
  choose selected hselected_ge hselected_pos using hlate
  have hselectedTendsto : Tendsto selected atTop atTop :=
    Filter.tendsto_atTop_mono hselected_ge tendsto_id
  let hazardError : ℕ → ℝ := fun index ↦
    quittingOpponentClockCharge roots owner (selected index)
  let targetError : ℕ → ℝ := fun index ↦
    2 * quittingRewardBound reward *
      quittingOpponentClockTailCharge roots owner (selected index)
  let quitError : ℕ → ℝ := fun _ ↦ 0
  apply isUniformEquilibriumPayoff_soloReward_of_deletedQuitLimits
    reward owner (fun index ↦ roots (selected index))
      (fun index ↦ value (selected index)) hazardError targetError quitError
  · intro index
    simpa [quittingMarginalQuitHazard] using hselected_pos index
  · intro index
    exact quittingOpponentClockCharge_nonneg roots owner (selected index)
  · intro index
    dsimp only [targetError]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (quittingRewardBound_nonneg reward))
      (tsum_nonneg fun offset ↦
        quittingOpponentClockCharge_nonneg roots owner
          (selected index + offset))
  · intro index
    exact le_rfl
  · exact hclock.tendsto_atTop_zero.comp hselectedTendsto
  · have hclockZero : Summable (fun offset ↦
        quittingOpponentClockCharge roots owner (0 + offset)) := by
      simpa using hclock
    have htail := tendsto_quittingOpponentClockTailCharge_zero
      roots owner 0 hclockZero
    have htail' : Tendsto
        (quittingOpponentClockTailCharge roots owner) atTop (nhds 0) := by
      simpa only [Nat.zero_add] using htail
    have hscaled := htail'.const_mul (2 * quittingRewardBound reward)
    dsimp only [targetError]
    change Tendsto
      ((fun later ↦ 2 * quittingRewardBound reward *
        quittingOpponentClockTailCharge roots owner later) ∘ selected)
      atTop (nhds 0)
    simpa using hscaled.comp hselectedTendsto
  · exact tendsto_const_nhds
  · intro index
    dsimp only [hazardError]
    rw [quittingOpponentClockCharge_eq_one_sub]
    rfl
  · intro index who
    exact hspine.abs_value_sub_soloReward_le reward value roots owner
      howner hclock (selected index) who
  · intro index who hwho
    dsimp only [quitError]
    rw [add_zero]
    unfold quittingStationaryFixedOpponentsQuitValue
    rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward
      (fun _ ↦ roots (selected index)) who (value (selected index + 1)) 0]
    calc
      quittingRootQuitPayoff reward (value (selected index + 1))
          (roots (selected index)) who ≤
          quittingRootSuccessorPayoff reward (value (selected index + 1))
            (roots (selected index)) who :=
        quittingRootQuitPayoff_le_successor_of_isZeroNash
          reward (value (selected index + 1)) (roots (selected index)) who
            (hspine.2.2 (selected index))
      _ = value (selected index) who :=
        (congrFun (hspine.2.1 (selected index)) who).symm
      _ ≤ value (selected index) who := le_rfl
  · simpa [IsQuittingNormalPlayer, quittingSoloSelfPayoff,
      quittingSoloReward] using hnormal

namespace IsCanonicalExactQuittingNashBellmanSpine

/-- If one player is persistent and every other marginal clock is summable,
normality of that unique persistent player gives the singleton vector as a
uniform-equilibrium payoff. -/
theorem isUniformEquilibriumPayoff_soloReward_of_uniquePersistent
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (value : ℕ → Payoff iota) (roots : ℕ → iota → PMF Bool)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots)
    (owner : iota)
    (howner : ¬ Summable (quittingMarginalQuitHazard roots owner))
    (hothers : ∀ other, other ≠ owner →
      Summable (quittingMarginalQuitHazard roots other))
    (hnormal : IsQuittingNormalPlayer reward owner) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSoloReward reward owner) := by
  apply hspine.isUniformEquilibriumPayoff_soloReward_of_persistent
    reward value roots owner howner
  · exact (summable_quittingOpponentClockCharge_iff roots owner).2 hothers
  · exact hnormal

end IsCanonicalExactQuittingNashBellmanSpine

end GameTheory

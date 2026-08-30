/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Classification.AbnormalPlayers
import UniformEquilibrium.Quitting.Cycles.ConditionedDeletedClockSoloCompletion
import UniformEquilibrium.Quitting.Debt.Dynamic.SummableResidualPersistentClosure

/-!
# All-normal closure of unbounded exact-block hazard capacity

A persistent label on a summable-residual Nash--Bellman spine is consumed in
one of two ways.  A second persistent label gives a uniform payoff directly;
otherwise the first label has summable opponent clock, and punishment
normality gives its singleton reward as a uniform payoff.  Hence unbounded
exact-block hazard capacity in a compact carrier gives a uniform-equilibrium
payoff when every player is punishment-normal.

The theorem is conditional on the supplied carrier capacity and all-player
normality.  It does not produce capacity from a source trace or prove that a
given reward table has no abnormal players.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction
open scoped BigOperators Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingSummableResidualNashBellmanSpine

private theorem exists_ge_pos_of_not_summable_nonneg
    {f : ℕ → ℝ} (hnonneg : ∀ time, 0 ≤ f time)
    (hnot : ¬ Summable f) (threshold : ℕ) :
    ∃ time, threshold ≤ time ∧ 0 < f time := by
  by_contra hnone
  push Not at hnone
  apply hnot
  have hzero : ∀ offset, f (offset + threshold) = 0 := fun offset =>
    le_antisymm
      (hnone (offset + threshold) (Nat.le_add_left threshold offset))
      (hnonneg (offset + threshold))
  have hshift : Summable (fun offset => f (offset + threshold)) := by
    have hconst : (fun offset => f (offset + threshold)) =
        fun _ => (0 : ℝ) := funext hzero
    rw [hconst]
    exact summable_zero
  exact (summable_nat_add_iff threshold).1 hshift

omit [DecidableEq ι] in
private theorem tendsto_zero_jointSurvival_of_persistent
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (howner : ¬ Summable (quittingMarginalQuitHazard roots owner)) :
    ∀ start,
      Tendsto (quittingJointSurvivalWeight roots start) atTop (nhds 0) := by
  have habsorption :
      ¬ Summable (fun time => quittingRootAbsorptionMass (roots time)) := by
    intro hsummable
    apply howner
    exact hsummable.of_nonneg_of_le
      (quittingMarginalQuitHazard_nonneg roots owner)
      (fun time =>
        quittingRoot_quitProbability_le_absorptionMass (roots time) owner)
  intro start
  apply tendsto_zero_quittingJointSurvivalWeight_of_not_summable_absorption
  intro hsuffix
  apply habsorption
  have hshift : Summable (fun offset =>
      quittingRootAbsorptionMass (roots (offset + start))) := by
    simpa [Nat.add_comm] using hsuffix
  exact (summable_nat_add_iff start).1 hshift

/-- A persistent owner with summable opponent clock concentrates the stored
value on its singleton reward, up to the remaining Bellman-error and opponent
clock tails. -/
theorem abs_value_sub_soloReward_le
    (spine : QuittingSummableResidualNashBellmanSpine reward)
    (owner : ι)
    (howner : ¬ Summable
      (quittingMarginalQuitHazard spine.roots owner))
    (hclock : Summable (quittingOpponentClockCharge spine.roots owner))
    (time : ℕ) (who : ι) :
    |spine.value time who - quittingSoloReward reward owner who| ≤
      (∑' offset, spine.bellmanError (time + offset)) +
        2 * quittingRewardBound reward *
          quittingOpponentClockTailCharge spine.roots owner time := by
  have hjoint := tendsto_zero_jointSurvival_of_persistent
    spine.roots owner howner time
  have hjointShifted : Tendsto
      (Math.survivalProduct (fun offset =>
        quittingStationaryContinueMass
          ((spine.shiftedChain time).roots offset)) 0)
      atTop (nhds 0) := by
    change Tendsto
      (Math.survivalProduct (fun offset =>
        quittingStationaryContinueMass (spine.roots (time + offset))) 0)
      atTop (nhds 0)
    convert hjoint using 1
    funext fuel
    rw [quittingJointSurvivalWeight_eq_survivalProduct]
    simp [Math.survivalProduct]
  have hvalue := spine.abs_value_sub_shiftedActualPair_prescribed_le_tsum
    time who hjointShifted
  have hclockShift : Summable (fun offset =>
      quittingOpponentClockCharge spine.roots owner (time + offset)) := by
    have hshift : Summable (fun offset =>
        quittingOpponentClockCharge spine.roots owner (offset + time)) :=
      (summable_nat_add_iff time).2 hclock
    simpa [Nat.add_comm] using hshift
  have hterminal :=
    abs_quittingRootSequenceTerminalValue_sub_soloReward_le_tailCharge
      reward spine.roots owner who time
        (abs_reward_le_quittingRewardBound reward) hjoint hclockShift
  have hactual :
      ((spine.shiftedChain time).actualPair 0).1 who =
        quittingRootSequenceTerminalValue reward spine.roots who time := by
    unfold QuittingBoundedSeamChain.actualPair
      quittingTerminalSemanticPair quittingRootSequenceTerminalValue
    dsimp only [Prod.fst]
    change quittingTerminalPayoff reward
      (quittingRootSequenceProfile reward
        (fun offset => spine.roots (time + offset)) 0) who = _
    rw [← quittingRootSequenceProfile_eq_shift reward spine.roots time]
  rw [hactual] at hvalue
  exact (abs_sub_le _ _ _).trans (add_le_add hvalue hterminal)

/-- A persistent owner with summable opponent clock and punishment normality
gives its singleton reward as a uniform-equilibrium payoff, even for a
summable-residual rather than exact Nash--Bellman spine. -/
theorem isUniformEquilibriumPayoff_soloReward_of_persistent
    (spine : QuittingSummableResidualNashBellmanSpine reward)
    (owner : ι)
    (howner : ¬ Summable
      (quittingMarginalQuitHazard spine.roots owner))
    (hclock : Summable (quittingOpponentClockCharge spine.roots owner))
    (hnormal : IsQuittingNormalPlayer reward owner) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSoloReward reward owner) := by
  have hlate : ∀ threshold, ∃ time, threshold ≤ time ∧
      0 < quittingMarginalQuitHazard spine.roots owner time :=
    exists_ge_pos_of_not_summable_nonneg
      (quittingMarginalQuitHazard_nonneg spine.roots owner) howner
  choose selected hselected_ge hselected_pos using hlate
  have hselectedTendsto : Tendsto selected atTop atTop :=
    Filter.tendsto_atTop_mono hselected_ge tendsto_id
  let hazardError : ℕ → ℝ := fun index =>
    quittingOpponentClockCharge spine.roots owner (selected index)
  let targetError : ℕ → ℝ := fun index =>
    (∑' offset, spine.bellmanError (selected index + offset)) +
      2 * quittingRewardBound reward *
        quittingOpponentClockTailCharge spine.roots owner (selected index)
  let quitError : ℕ → ℝ := fun index =>
    spine.bellmanError (selected index) + spine.nashError (selected index)
  apply isUniformEquilibriumPayoff_soloReward_of_deletedQuitLimits
    reward owner (fun index => spine.roots (selected index))
      (fun index => spine.value (selected index))
      hazardError targetError quitError
  · intro index
    simpa [quittingMarginalQuitHazard] using hselected_pos index
  · intro index
    exact quittingOpponentClockCharge_nonneg spine.roots owner
      (selected index)
  · intro index
    dsimp only [targetError]
    exact add_nonneg
      (tsum_nonneg fun offset =>
        spine.bellmanError_nonneg (selected index + offset))
      (mul_nonneg
        (mul_nonneg (by norm_num) (quittingRewardBound_nonneg reward))
        (tsum_nonneg fun offset =>
          quittingOpponentClockCharge_nonneg spine.roots owner
            (selected index + offset)))
  · intro index
    exact add_nonneg (spine.bellmanError_nonneg (selected index))
      (spine.nashError_nonneg (selected index))
  · exact hclock.tendsto_atTop_zero.comp hselectedTendsto
  · have _hbellman : Summable spine.bellmanError :=
      spine.bellmanError_summable
    have hbellmanTail : Tendsto
        (fun time => ∑' offset, spine.bellmanError (time + offset))
        atTop (nhds 0) := by
      simpa [Nat.add_comm] using tendsto_sum_nat_add spine.bellmanError
    have hclockZero : Summable (fun offset =>
        quittingOpponentClockCharge spine.roots owner (0 + offset)) := by
      simpa using hclock
    have hopponentTail := tendsto_quittingOpponentClockTailCharge_zero
      spine.roots owner 0 hclockZero
    have hopponentTail' : Tendsto
        (quittingOpponentClockTailCharge spine.roots owner)
        atTop (nhds 0) := by
      simpa only [Nat.zero_add] using hopponentTail
    have htarget : Tendsto (fun time =>
        (∑' offset, spine.bellmanError (time + offset)) +
          2 * quittingRewardBound reward *
            quittingOpponentClockTailCharge spine.roots owner time)
        atTop (nhds 0) := by
      simpa using hbellmanTail.add
        (hopponentTail'.const_mul (2 * quittingRewardBound reward))
    exact htarget.comp hselectedTendsto
  · have hbellman := spine.bellmanError_summable.tendsto_atTop_zero
    have hnash := spine.nashError_summable.tendsto_atTop_zero
    change Tendsto
      ((fun time => spine.bellmanError time + spine.nashError time) ∘ selected)
      atTop (nhds 0)
    simpa using (hbellman.add hnash).comp hselectedTendsto
  · intro index
    dsimp only [hazardError]
    rw [quittingOpponentClockCharge_eq_one_sub]
    rfl
  · intro index who
    exact spine.abs_value_sub_soloReward_le owner howner hclock
      (selected index) who
  · intro index who _hwho
    simpa [quitError, add_assoc] using
      spine.fixedOpponentsQuitValue_le_value_add_residual
        (selected index) who
  · simpa [IsQuittingNormalPlayer, quittingSoloSelfPayoff,
      quittingSoloReward] using hnormal

/-- A unique persistent player on a summable-residual spine yields its
singleton uniform-equilibrium payoff under punishment normality. -/
theorem isUniformEquilibriumPayoff_soloReward_of_uniquePersistent
    (spine : QuittingSummableResidualNashBellmanSpine reward)
    (owner : ι)
    (howner : ¬ Summable
      (quittingMarginalQuitHazard spine.roots owner))
    (hothers : ∀ other, other ≠ owner →
      Summable (quittingMarginalQuitHazard spine.roots other))
    (hnormal : IsQuittingNormalPlayer reward owner) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSoloReward reward owner) := by
  apply spine.isUniformEquilibriumPayoff_soloReward_of_persistent
    owner howner
  · exact (summable_quittingOpponentClockCharge_iff
      spine.roots owner).2 hothers
  · exact hnormal

end QuittingSummableResidualNashBellmanSpine

/-- Unbounded exact-block capacity in a compact carrier gives a
uniform-equilibrium payoff whenever every player is punishment-normal. -/
theorem
    exists_uniformEquilibriumPayoff_of_unboundedExactBlockHazardCapacity_of_allNormal
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : Set (QuittingNashBellmanPoint ι))
    (hcarrier : IsCompact carrier)
    (hcapacity :
      HasUnboundedFiniteExactNashBellmanHazardCapacity reward carrier)
    (hnormal : ∀ owner, IsQuittingNormalPlayer reward owner) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨spine, _hledger, owner, howner⟩ :=
    exists_summableResidualNashBellmanSpine_of_unboundedCapacity
      reward carrier hcarrier hcapacity 1 zero_lt_one
  by_cases hother : ∃ other, other ≠ owner ∧
      ¬ Summable (quittingMarginalQuitHazard spine.roots other)
  · obtain ⟨other, hne, hotherPersistent⟩ := hother
    exact spine.exists_uniformEquilibriumPayoff_of_twoPersistent
      ⟨owner, other, hne.symm, howner, hotherPersistent⟩
  · push Not at hother
    exact ⟨quittingSoloReward reward owner,
      spine.isUniformEquilibriumPayoff_soloReward_of_uniquePersistent
        owner howner hother (hnormal owner)⟩

end GameTheory

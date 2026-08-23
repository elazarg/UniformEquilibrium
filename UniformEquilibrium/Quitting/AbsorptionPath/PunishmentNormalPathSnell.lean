/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.PunishmentNormalPathEmbedding
import UniformEquilibrium.Quitting.AbsorptionPath.SingletonPathSnellTail

/-!
# Deleted clocks for punishment-normal path embeddings

This module specializes the generic singleton-path Snell calculus to the
zero-extended ambient punishment-normal path.  Omitted players have exactly
zero logarithmic rate and hence ordinary exponential deleted survival.  In
particular, every owner with positive limiting deleted survival belongs to the
punishment-normal face.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open Filter Finset Set unitInterval
open MeasureTheory QuittingAbsorptionPath
open scoped Interval Topology unitInterval

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem ContinuousZeroPerfectSingletonPath.ambient_logMass_abnormal
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward))
    {who : ι} (hwho : who ∉ punishmentNormalPlayers reward) (tau : ℝ) :
    witness.ambientSingletonWitness.logMass who tau = 0 := by
  unfold ContinuousZeroPerfectSingletonPath.logMass
    ContinuousZeroPerfectSingletonPath.ambientSingletonWitness
  exact witness.ambientMass_extend_apply_abnormal _ hwho

theorem ContinuousZeroPerfectSingletonPath.ambient_logRate_abnormal
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward))
    {who : ι} (hwho : who ∉ punishmentNormalPlayers reward) (tau : ℝ) :
    witness.ambientSingletonWitness.logRate who tau = 0 := by
  unfold ContinuousZeroPerfectSingletonPath.logRate
  rw [show witness.ambientSingletonWitness.logMass who = 0 by
    funext second
    exact witness.ambient_logMass_abnormal hwho second]
  simp

theorem ContinuousZeroPerfectSingletonPath.ambient_deletedSurvival_abnormal
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward))
    {who : ι} (hwho : who ∉ punishmentNormalPlayers reward) (T : ℝ) :
    witness.ambientSingletonWitness.deletedSurvival who T = Real.exp (-T) := by
  simp only [ContinuousZeroPerfectSingletonPath.deletedSurvival_apply,
    ContinuousZeroPerfectSingletonPath.deletedHazard,
    ContinuousZeroPerfectSingletonPath.deletedHazardRate,
    witness.ambient_logRate_abnormal hwho]
  simp

/-- Positive limiting deleted survival is possible only on the retained
punishment-normal face. -/
theorem ContinuousZeroPerfectSingletonPath.mem_punishmentNormalPlayers_of_positive_deletedLimit
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward))
    {who : ι} {limit : ℝ}
    (htendsto : Tendsto
      (witness.ambientSingletonWitness.deletedSurvival who)
      atTop (nhds limit))
    (hlimit : 0 < limit) :
    who ∈ punishmentNormalPlayers reward := by
  by_contra habnormal
  have hzero : Tendsto
      (witness.ambientSingletonWitness.deletedSurvival who)
      atTop (nhds 0) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero using 1
    funext T
    exact witness.ambient_deletedSurvival_abnormal habnormal T
  have : limit = 0 := tendsto_nhds_unique htendsto hzero
  linarith

/-- The sampled logarithmic payoff at time zero is exactly the continuation
target of the ambient embedded path. -/
theorem ContinuousZeroPerfectSingletonPath.ambient_logPayoff_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward)) (who : ι) :
    witness.ambientSingletonWitness.logPayoff reward 0 who =
      absorptionPathPayoff reward witness.ambientPath 0 who := by
  rw [witness.ambientSingletonWitness.logPayoff_eq_absorptionPathPayoff
    reward (by norm_num)]
  simp only [witness.ambientSingletonWitness_path, logarithmicPathClock,
    neg_zero, Real.exp_zero, sub_self]

/-- A positive ambient deleted-survival limit forces the exceptional owner's
singleton row to dominate every receiver's own singleton payoff. -/
theorem ContinuousZeroPerfectSingletonPath.ambient_noHarm_of_positive_deletedLimit
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward))
    {owner : ι} {limit : ℝ}
    (htendsto : Tendsto
      (witness.ambientSingletonWitness.deletedSurvival owner)
      atTop (nhds limit))
    (hlimit : 0 < limit) :
    ∀ who, quittingSoloReward reward who who ≤
      quittingSoloReward reward owner who := by
  intro who
  have hpayoff :=
    witness.ambientSingletonWitness.tendsto_logPayoff_of_positive_survival
      reward owner htendsto hlimit who
  apply ge_of_tendsto hpayoff
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact witness.ambientSingletonWitness.solo_le_logPayoff reward who hT

/-- A positive ambient deleted-survival limit supplies both natural inputs of
the exceptional-owner strategic constructor. -/
theorem ContinuousZeroPerfectSingletonPath.ambient_positive_deletedLimit_ownerData
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward))
    {owner : ι} {limit : ℝ}
    (htendsto : Tendsto
      (witness.ambientSingletonWitness.deletedSurvival owner)
      atTop (nhds limit))
    (hlimit : 0 < limit) :
    (∀ other, other ≠ owner →
      quittingSoloReward reward other other ≤
        quittingSoloReward reward owner other) ∧
      quittingPunishmentValue reward owner ≤
        quittingSoloReward reward owner owner := by
  constructor
  · intro other _
    exact witness.ambient_noHarm_of_positive_deletedLimit
      htendsto hlimit other
  · have hmem := witness.mem_punishmentNormalPlayers_of_positive_deletedLimit
      htendsto hlimit
    exact (mem_punishmentNormalPlayers reward owner).1 hmem

end QuittingLCPClassification
end GameTheory

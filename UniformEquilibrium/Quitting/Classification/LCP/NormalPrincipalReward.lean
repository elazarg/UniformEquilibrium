/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.PrincipalQContinuousPath
import UniformEquilibrium.Quitting.Classification.AbnormalSingletonConsequences
import UniformEquilibrium.Quitting.Classification.LCP.NormalPrincipalQBar
import UniformEquilibrium.Quitting.Classification.LCP.PrincipalReward

/-!
# Reward restriction to punishment-normal players

This file restricts a quitting reward table to the finite subtype of players
whose own singleton payoff covers their behavioral punishment value.  It
checks that singleton normalization commutes with this restriction and hence
connects projective Q-bar on the normal principal matrix to the existing
continuous-path producer.

The resulting path lives on the restricted player type.  Extending it to an
ambient sequentially perfect path requires the omitted-player inequality and
is intentionally not asserted here.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open QuittingAbsorptionPath

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Include a coalition of punishment-normal players into the ambient player
set. -/
def quittingPunishmentNormalCoalition
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (coalition :
      {S : Finset (punishmentNormalPlayers reward) // S.Nonempty}) :
    {S : Finset ι // S.Nonempty} :=
  quittingPrincipalCoalition (punishmentNormalPlayers reward) coalition

/-- Restriction of the reward table to punishment-normal coalitions and
payoff coordinates. -/
def quittingPunishmentNormalReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    {S : Finset (punishmentNormalPlayers reward) // S.Nonempty} →
      Payoff (punishmentNormalPlayers reward) :=
  quittingPrincipalReward reward (punishmentNormalPlayers reward)

@[simp] theorem quittingPunishmentNormalCoalition_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : punishmentNormalPlayers reward) :
      quittingPunishmentNormalCoalition reward
        (quittingProjectiveSingletonTerminal who) =
      quittingProjectiveSingletonTerminal who.1 := by
  simpa only [quittingPunishmentNormalCoalition] using
    quittingPrincipalCoalition_singleton
      (punishmentNormalPlayers reward) who

@[simp] theorem quittingPunishmentNormalReward_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner who : punishmentNormalPlayers reward) :
      quittingPunishmentNormalReward reward
        (quittingProjectiveSingletonTerminal owner) who =
      reward (quittingProjectiveSingletonTerminal owner.1) who.1 := by
  simpa only [quittingPunishmentNormalReward] using
    quittingPrincipalReward_singleton reward
      (punishmentNormalPlayers reward) owner who

/-- The restricted reward's normalized singleton matrix is literally the
production-normal principal matrix. -/
theorem normalizedSoloMatrix_quittingPunishmentNormalReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    normalizedSoloMatrix (quittingPunishmentNormalReward reward) =
      normalizedPunishmentNormalPlayerMatrix reward := by
  simpa only [quittingPunishmentNormalReward,
    normalizedPunishmentNormalPlayerMatrix] using
      normalizedSoloMatrix_quittingPrincipalReward reward
        (punishmentNormalPlayers reward)

/-- Every probability mixture of punishment-normal singleton owners protects
an omitted abnormal coordinate: its payoff is above the behavioral punishment
floor and hence strictly above the omitted player's own singleton payoff.
This is the finite protected-face adapter; extending the inequality through
the continuum path's residual laws remains a separate analytic step. -/
theorem abnormal_punishmentFloor_chain_punishmentNormal_singletonMixture
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {abnormal : ι} (habnormal : IsQuittingAbnormalPlayer reward abnormal)
    (weight : punishmentNormalPlayers reward → ℝ)
    (hweight : ∀ owner, 0 ≤ weight owner)
    (htotal : ∑ owner, weight owner = 1) :
    quittingSoloSelfPayoff reward abnormal <
        quittingPunishmentValue reward abnormal ∧
      quittingPunishmentValue reward abnormal ≤
        ∑ owner, weight owner *
          quittingSoloReward reward owner.1 abnormal := by
  refine ⟨habnormal, ?_⟩
  calc
    quittingPunishmentValue reward abnormal =
        ∑ owner, weight owner * quittingPunishmentValue reward abnormal := by
      rw [← Finset.sum_mul, htotal, one_mul]
    _ ≤ ∑ owner, weight owner *
        quittingSoloReward reward owner.1 abnormal := by
      apply Finset.sum_le_sum
      intro owner howner
      apply mul_le_mul_of_nonneg_left _ (hweight owner)
      apply quittingPunishmentValue_le_soloReward_of_abnormal reward habnormal
      intro heq
      have hnormal :=
        (mem_punishmentNormalPlayers reward owner.1).1 owner.2
      rw [← heq] at hnormal
      exact (not_lt_of_ge hnormal) habnormal

/-- Off the zero-solo branch, projective Q-bar on the punishment-normal
principal matrix produces an exposed singleton player-mass path for the
restricted reward table. -/
theorem exists_punishmentNormal_singletonPath_of_projectiveQBar
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnotZero : ¬IsQuittingZeroSolo reward)
    (hQ : IsProjectiveQBarMatrix
      (normalizedPunishmentNormalPlayerMatrix reward)) :
    Nonempty (ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward)) := by
  letI : Nonempty (punishmentNormalPlayers reward) :=
    (punishmentNormalPlayers_nonempty_of_not_zeroSolo reward hnotZero).to_subtype
  apply exists_continuousZeroPerfectSingletonPath_of_projectiveQBar
    (quittingPunishmentNormalReward reward)
  rwa [normalizedSoloMatrix_quittingPunishmentNormalReward]

/-- Path-valued wrapper around the exposed singleton-mass producer. -/
theorem exists_punishmentNormal_continuous_zeroPerfect_of_projectiveQBar
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnotZero : ¬IsQuittingZeroSolo reward)
    (hQ : IsProjectiveQBarMatrix
      (normalizedPunishmentNormalPlayerMatrix reward)) :
    ∃ path : AbsorptionPath (ι := punishmentNormalPlayers reward),
      IsContinuousAbsorptionPath path ∧
        IsSequentiallyPerfectAbsorptionPath
          (quittingPunishmentNormalReward reward) path 0 := by
  obtain ⟨witness⟩ :=
    exists_punishmentNormal_singletonPath_of_projectiveQBar
      reward hnotZero hQ
  exact ⟨witness.path, witness.continuous, witness.zeroPerfect⟩

end QuittingLCPClassification
end GameTheory

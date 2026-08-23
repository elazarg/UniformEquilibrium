/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.NormalPrincipalReward

/-!
# Embedding punishment-normal singleton paths

This file embeds a continuous singleton-mass path on the subtype of players
whose own singleton payoff covers their behavioral punishment value into the
ambient quitting game.  Omitted coordinates are identically zero.  The
checked abnormal-player singleton-floor inequality then supplies their lower
sequential-perfection inequality.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open Filter Finset Set unitInterval
open QuittingAbsorptionPath
open scoped Topology unitInterval

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Extend a mass vector on punishment-normal players by zero. -/
def punishmentNormalMassExtension
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mass : punishmentNormalPlayers reward → ℝ) : ι → ℝ :=
  fun who => if hwho : who ∈ punishmentNormalPlayers reward then
    mass ⟨who, hwho⟩ else 0

@[simp] theorem punishmentNormalMassExtension_apply_mem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mass : punishmentNormalPlayers reward → ℝ)
    (who : punishmentNormalPlayers reward) :
    punishmentNormalMassExtension reward mass who.1 = mass who := by
  simp only [punishmentNormalMassExtension, dif_pos who.2]

@[simp] theorem punishmentNormalMassExtension_apply_not_mem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mass : punishmentNormalPlayers reward → ℝ) {who : ι}
    (hwho : who ∉ punishmentNormalPlayers reward) :
    punishmentNormalMassExtension reward mass who = 0 := by
  simp only [punishmentNormalMassExtension, dif_neg hwho]

/-- Extend a punishment-normal player-mass path to the ambient player type. -/
def ContinuousZeroPerfectSingletonPath.ambientMass
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward)) :
    Path (0 : ι → ℝ)
      (punishmentNormalMassExtension reward witness.terminal) :=
  Path.mk
    (ContinuousMap.mk
      (fun time => punishmentNormalMassExtension reward (witness.mass time))
      (by
        apply continuous_pi
        intro who
        simp only [punishmentNormalMassExtension]
        split_ifs <;> fun_prop))
    (by
      funext who
      by_cases hwho : who ∈ punishmentNormalPlayers reward
      · simp only [punishmentNormalMassExtension, dif_pos hwho,
          witness.mass.source, Pi.zero_apply]
      · simp only [punishmentNormalMassExtension, dif_neg hwho,
          Pi.zero_apply])
    (by
      funext who
      by_cases hwho : who ∈ punishmentNormalPlayers reward
      · simp only [punishmentNormalMassExtension, dif_pos hwho,
          witness.mass.target]
      · simp only [punishmentNormalMassExtension, dif_neg hwho])

theorem ContinuousZeroPerfectSingletonPath.ambientMass_apply_normal
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward))
    (time : unitInterval) (who : punishmentNormalPlayers reward) :
    witness.ambientMass time who.1 = witness.mass time who := by
  simp only [ContinuousZeroPerfectSingletonPath.ambientMass,
    Path.coe_mk_mk, punishmentNormalMassExtension_apply_mem]

theorem ContinuousZeroPerfectSingletonPath.ambientMass_apply_abnormal
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward))
    (time : unitInterval) {who : ι}
    (hwho : who ∉ punishmentNormalPlayers reward) :
    witness.ambientMass time who = 0 := by
  simp only [ContinuousZeroPerfectSingletonPath.ambientMass,
    Path.coe_mk_mk, punishmentNormalMassExtension_apply_not_mem
      reward _ hwho]

theorem ContinuousZeroPerfectSingletonPath.ambientMass_monotone
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward)) :
    ∀ who, Monotone fun time => witness.ambientMass time who := by
  intro who first second hle
  by_cases hwho : who ∈ punishmentNormalPlayers reward
  · simpa only [witness.ambientMass_apply_normal first ⟨who, hwho⟩,
      witness.ambientMass_apply_normal second ⟨who, hwho⟩] using
        witness.monotone ⟨who, hwho⟩ hle
  · simp only [witness.ambientMass_apply_abnormal first hwho,
      witness.ambientMass_apply_abnormal second hwho]
    exact le_rfl

theorem ContinuousZeroPerfectSingletonPath.ambientMass_total
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward))
    (time : unitInterval) :
    ∑ who, witness.ambientMass time who = (time : ℝ) := by
  rw [← witness.total time]
  change (∑ who : ι, punishmentNormalMassExtension reward
    (witness.mass time) who) = _
  calc
    _ = ∑ who ∈ punishmentNormalPlayers reward,
        punishmentNormalMassExtension reward (witness.mass time) who := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro who _ hwho
      exact punishmentNormalMassExtension_apply_not_mem reward _ hwho
    _ = ∑ who ∈ (punishmentNormalPlayers reward).attach,
        punishmentNormalMassExtension reward (witness.mass time) who.1 := by
      exact (Finset.sum_attach (punishmentNormalPlayers reward)
        (punishmentNormalMassExtension reward (witness.mass time))).symm
    _ = ∑ who ∈ (punishmentNormalPlayers reward).attach,
        witness.mass time who := by
      apply Finset.sum_congr rfl
      intro who _
      exact punishmentNormalMassExtension_apply_mem reward _ who
    _ = ∑ who, witness.mass time who := by
      congr 1

/-- The ambient zero-extension as a continuous singleton absorption path. -/
def ContinuousZeroPerfectSingletonPath.ambientPath
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward)) :
    AbsorptionPath (ι := ι) :=
  singletonAbsorptionPathOfPlayerPath witness.ambientMass
    witness.ambientMass_monotone witness.ambientMass_total

theorem ContinuousZeroPerfectSingletonPath.ambientPath_continuous
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward)) :
    IsContinuousAbsorptionPath witness.ambientPath :=
  singletonAbsorptionPathOfPlayerPath_continuous witness.ambientMass
    witness.ambientMass_monotone witness.ambientMass_total

/-- A weighted ambient sum of a zero-extended vector is the corresponding
sum over punishment-normal owners. -/
theorem sum_punishmentNormalMassExtension_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mass : punishmentNormalPlayers reward → ℝ) (payoff : ι → ℝ) :
    ∑ owner, punishmentNormalMassExtension reward mass owner * payoff owner =
      ∑ owner, mass owner * payoff owner.1 := by
  calc
    _ = ∑ owner ∈ punishmentNormalPlayers reward,
        punishmentNormalMassExtension reward mass owner * payoff owner := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro owner _ howner
      rw [punishmentNormalMassExtension_apply_not_mem reward mass howner,
        zero_mul]
    _ = ∑ owner ∈ (punishmentNormalPlayers reward).attach,
        punishmentNormalMassExtension reward mass owner.1 * payoff owner.1 := by
      exact (Finset.sum_attach (punishmentNormalPlayers reward)
        (fun owner => punishmentNormalMassExtension reward mass owner *
          payoff owner)).symm
    _ = ∑ owner ∈ (punishmentNormalPlayers reward).attach,
        mass owner * payoff owner.1 := by
      apply Finset.sum_congr rfl
      intro owner _
      rw [punishmentNormalMassExtension_apply_mem]
    _ = ∑ owner, mass owner * payoff owner.1 := by
      congr 1

/-- Remaining normal-owner mass, normalized to a probability vector. -/
def ContinuousZeroPerfectSingletonPath.normalResidualWeight
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward))
    (time : unitInterval) : punishmentNormalPlayers reward → ℝ :=
  fun owner => (witness.mass 1 owner - witness.mass time owner) /
    (1 - (time : ℝ))

theorem ContinuousZeroPerfectSingletonPath.normalResidualWeight_nonneg
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward))
    (time : unitInterval) (owner : punishmentNormalPlayers reward) :
    0 ≤ witness.normalResidualWeight time owner := by
  unfold ContinuousZeroPerfectSingletonPath.normalResidualWeight
  exact div_nonneg
    (sub_nonneg.mpr (witness.monotone owner time.property.2))
    (sub_nonneg.mpr time.property.2)

theorem ContinuousZeroPerfectSingletonPath.sum_normalResidualWeight
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward))
    (time : unitInterval) (htimeOne : time ≠ 1) :
    ∑ owner, witness.normalResidualWeight time owner = 1 := by
  unfold ContinuousZeroPerfectSingletonPath.normalResidualWeight
  rw [← Finset.sum_div, Finset.sum_sub_distrib, witness.total, witness.total]
  have hne : 1 - (time : ℝ) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro heq
    apply htimeOne
    exact Subtype.ext heq.symm
  exact div_self hne

/-- The ambient continuation payoff is exactly the residual mixture of
punishment-normal singleton rows. -/
theorem ContinuousZeroPerfectSingletonPath.ambientPathPayoff_eq_normalResidualMixture
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward))
    (time : unitInterval) (htimeOne : time ≠ 1) (who : ι) :
    absorptionPathPayoff reward witness.ambientPath (time : ℝ) who =
      ∑ owner, witness.normalResidualWeight time owner *
        quittingSoloReward reward owner.1 who := by
  unfold ContinuousZeroPerfectSingletonPath.ambientPath
  rw [absorptionPathPayoff_singletonAbsorptionPathOfPlayerPath
    witness.ambientMass witness.ambientMass_monotone
    witness.ambientMass_total reward time htimeOne who]
  change (∑ owner,
      (witness.ambientMass 1 owner - witness.ambientMass time owner) *
        quittingSoloReward reward owner who) / (1 - (time : ℝ)) = _
  calc
    _ = (∑ owner,
        (witness.mass 1 owner - witness.mass time owner) *
          quittingSoloReward reward owner.1 who) / (1 - (time : ℝ)) := by
      congr 1
      rw [← sum_punishmentNormalMassExtension_mul reward
        (fun owner => witness.mass 1 owner - witness.mass time owner)
        (fun owner => quittingSoloReward reward owner who)]
      apply Finset.sum_congr rfl
      intro owner _
      by_cases howner : owner ∈ punishmentNormalPlayers reward
      · simp only [witness.ambientMass_apply_normal 1 ⟨owner, howner⟩,
          witness.ambientMass_apply_normal time ⟨owner, howner⟩,
          punishmentNormalMassExtension, dif_pos howner]
      · simp only [witness.ambientMass_apply_abnormal 1 howner,
          witness.ambientMass_apply_abnormal time howner,
          sub_self, zero_mul, punishmentNormalMassExtension,
          dif_neg howner]
    _ = ∑ owner,
        ((witness.mass 1 owner - witness.mass time owner) /
          (1 - (time : ℝ))) * quittingSoloReward reward owner.1 who := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro owner _
      ring
    _ = _ := by rfl

/-- Every omitted abnormal coordinate satisfies the lower ambient
sequential-perfection inequality. -/
theorem ContinuousZeroPerfectSingletonPath.ambientPathPayoff_abnormal_gt_solo
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward))
    (time : unitInterval) (htimeOne : time ≠ 1) {who : ι}
    (habnormal : IsQuittingAbnormalPlayer reward who) :
    quittingSoloSelfPayoff reward who <
      absorptionPathPayoff reward witness.ambientPath (time : ℝ) who := by
  rw [witness.ambientPathPayoff_eq_normalResidualMixture time htimeOne who]
  exact
    (abnormal_punishmentFloor_chain_punishmentNormal_singletonMixture
      reward habnormal (witness.normalResidualWeight time)
      (witness.normalResidualWeight_nonneg time)
      (witness.sum_normalResidualWeight time htimeOne)).1.trans_le
      (abnormal_punishmentFloor_chain_punishmentNormal_singletonMixture
        reward habnormal (witness.normalResidualWeight time)
        (witness.normalResidualWeight_nonneg time)
        (witness.sum_normalResidualWeight time htimeOne)).2

/-- On a retained coordinate, real-time extension of the ambient mass agrees
with real-time extension of the restricted mass. -/
theorem ContinuousZeroPerfectSingletonPath.ambientMass_extend_apply_normal
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward))
    (time : ℝ) (who : punishmentNormalPlayers reward) :
    witness.ambientMass.extend time who.1 = witness.mass.extend time who := by
  by_cases hzero : time ≤ 0
  · rw [Path.extend_of_le_zero _ hzero, Path.extend_of_le_zero _ hzero]
    rfl
  by_cases hone : 1 ≤ time
  · rw [Path.extend_of_one_le _ hone, Path.extend_of_one_le _ hone]
    exact punishmentNormalMassExtension_apply_mem reward _ who
  have htime : time ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_of_not_ge hzero, le_of_not_ge hone⟩
  rw [Path.extend_apply _ htime, Path.extend_apply _ htime]
  exact witness.ambientMass_apply_normal ⟨time, htime⟩ who

/-- On an omitted coordinate, real-time extension of the ambient mass is
identically zero. -/
theorem ContinuousZeroPerfectSingletonPath.ambientMass_extend_apply_abnormal
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward))
    (time : ℝ) {who : ι}
    (hwho : who ∉ punishmentNormalPlayers reward) :
    witness.ambientMass.extend time who = 0 := by
  by_cases hzero : time ≤ 0
  · rw [Path.extend_of_le_zero _ hzero]
    rfl
  by_cases hone : 1 ≤ time
  · rw [Path.extend_of_one_le _ hone]
    exact punishmentNormalMassExtension_apply_not_mem reward _ hwho
  have htime : time ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_of_not_ge hzero, le_of_not_ge hone⟩
  rw [Path.extend_apply _ htime]
  exact witness.ambientMass_apply_abnormal ⟨time, htime⟩ hwho

/-- Retained singleton coordinates have the same lower right derivative in
the restricted and ambient paths. -/
theorem ContinuousZeroPerfectSingletonPath.ambientPathRightDerivative_normal
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward))
    (time : ℝ) (who : punishmentNormalPlayers reward) :
    pathRightDerivative witness.ambientPath.1 time
        (quittingProjectiveSingletonTerminal who.1) =
      pathRightDerivative witness.path.1 time
        (quittingProjectiveSingletonTerminal who) := by
  unfold ContinuousZeroPerfectSingletonPath.ambientPath
    ContinuousZeroPerfectSingletonPath.path pathRightDerivative
    singletonAbsorptionPathOfPlayerPath singletonCadlagPathOfPlayerPath
  simp_rw [singletonCoalitionMass_singleton,
    witness.ambientMass_extend_apply_normal]

/-- Omitted singleton coordinates have zero lower right derivative. -/
theorem ContinuousZeroPerfectSingletonPath.ambientPathRightDerivative_abnormal
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward))
    (time : ℝ) (htime : time < 1) {who : ι}
    (hwho : who ∉ punishmentNormalPlayers reward) :
    pathRightDerivative witness.ambientPath.1 time
        (quittingProjectiveSingletonTerminal who) = 0 := by
  unfold ContinuousZeroPerfectSingletonPath.ambientPath pathRightDerivative
    singletonAbsorptionPathOfPlayerPath singletonCadlagPathOfPlayerPath
  simp_rw [singletonCoalitionMass_singleton,
    witness.ambientMass_extend_apply_abnormal _ hwho]
  simp only [sub_self, zero_div]
  letI : NeBot (nhdsWithin time (Set.Ioo time 1)) :=
    left_nhdsWithin_Ioo_neBot htime
  exact Filter.liminf_const 0

/-- A retained player's ambient continuation payoff is exactly her payoff on
the restricted path. -/
theorem ContinuousZeroPerfectSingletonPath.ambientPathPayoff_normal
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward))
    (time : unitInterval) (htimeOne : time ≠ 1)
    (who : punishmentNormalPlayers reward) :
    absorptionPathPayoff reward witness.ambientPath (time : ℝ) who.1 =
      absorptionPathPayoff (quittingPunishmentNormalReward reward)
        witness.path (time : ℝ) who := by
  rw [witness.ambientPathPayoff_eq_normalResidualMixture time htimeOne who.1]
  unfold ContinuousZeroPerfectSingletonPath.path
  rw [absorptionPathPayoff_singletonAbsorptionPathOfPlayerPath
    witness.mass witness.monotone witness.total
    (quittingPunishmentNormalReward reward) time htimeOne who]
  unfold ContinuousZeroPerfectSingletonPath.normalResidualWeight
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro owner _
  rw [quittingPunishmentNormalReward_singleton]
  simp only [quittingSoloReward, quittingProjectiveSingletonTerminal]
  ring

/-- Zero-extension along the protected punishment-normal face preserves both
continuous sequential-perfection inequalities in the ambient game. -/
theorem ContinuousZeroPerfectSingletonPath.ambientPath_zeroPerfect
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward)) :
    IsSequentiallyPerfectAbsorptionPath reward witness.ambientPath 0 := by
  intro who
  constructor
  · intro time htime
    change time ∈ pathJumps (singletonCadlagPathOfPlayerPath
      witness.ambientMass witness.ambientMass_monotone
      witness.ambientMass_total) at htime
    rw [pathJumps_singletonCadlagPathOfPlayerPath
      witness.ambientMass witness.ambientMass_monotone
      witness.ambientMass_total] at htime
    exact htime.elim
  · intro time htime htimeOne
    have htimeIcc : time ∈ Set.Icc (0 : ℝ) 1 := by
      rw [← witness.ambientPath_continuous]
      exact htime
    let clock : unitInterval := ⟨time, htimeIcc⟩
    have hclockOne : clock ≠ 1 := by
      intro heq
      apply htimeOne
      exact congrArg Subtype.val heq
    by_cases hnormal : who ∈ punishmentNormalPlayers reward
    · let normal : punishmentNormalPlayers reward := ⟨who, hnormal⟩
      have hrestrictedTime : time ∈ pathTimes witness.path.1 := by
        rw [witness.continuous]
        exact htimeIcc
      have hperfect := (witness.zeroPerfect normal).2 time
        hrestrictedTime htimeOne
      constructor
      · simp only [sub_zero]
        rw [witness.ambientPathPayoff_normal clock hclockOne normal]
        simpa [normal, clock, ContinuousZeroPerfectSingletonPath.path,
          quittingPunishmentNormalReward,
          quittingPunishmentNormalCoalition,
          quittingProjectiveSingletonTerminal] using hperfect.1
      · intro hderivative
        have hrestrictedDerivative :
            0 < pathRightDerivative witness.path.1 time
              (quittingProjectiveSingletonTerminal normal) := by
          rwa [← witness.ambientPathRightDerivative_normal time normal]
        simp only [add_zero]
        rw [witness.ambientPathPayoff_normal clock hclockOne normal]
        simpa [normal, clock, ContinuousZeroPerfectSingletonPath.path,
          quittingPunishmentNormalReward,
          quittingPunishmentNormalCoalition,
          quittingProjectiveSingletonTerminal] using
            hperfect.2 hrestrictedDerivative
    · have habnormal : IsQuittingAbnormalPlayer reward who := by
        rw [mem_punishmentNormalPlayers] at hnormal
        exact lt_of_not_ge hnormal
      constructor
      · simp only [sub_zero]
        change quittingSoloSelfPayoff reward who ≤
          absorptionPathPayoff reward witness.ambientPath time who
        exact (witness.ambientPathPayoff_abnormal_gt_solo
          clock hclockOne habnormal).le
      · intro hderivative
        have htimeLt : time < 1 := lt_of_le_of_ne htimeIcc.2 htimeOne
        have hderivative' : 0 < pathRightDerivative witness.ambientPath.1 time
            (quittingProjectiveSingletonTerminal who) := by
          simpa only [quittingProjectiveSingletonTerminal] using hderivative
        rw [witness.ambientPathRightDerivative_abnormal time htimeLt hnormal]
          at hderivative'
        exact (lt_irrefl 0 hderivative').elim

/-- The full checked ambient lift of a punishment-normal singleton path. -/
theorem ContinuousZeroPerfectSingletonPath.ambientLift
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward)) :
    IsContinuousAbsorptionPath witness.ambientPath ∧
      IsSequentiallyPerfectAbsorptionPath reward witness.ambientPath 0 :=
  ⟨witness.ambientPath_continuous, witness.ambientPath_zeroPerfect⟩

/-- Off the zero-solo branch, projective Q-bar on the principal matrix of
punishment-normal players produces an ambient continuous singleton absorption
path that is exactly sequentially perfect.  The witness retains the restricted
path, so downstream decoders can use its singleton-mass coordinates while the
conclusion is stated in the original player type. -/
theorem exists_punishmentNormal_ambientPath_of_projectiveQBar
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnotZero : ¬IsQuittingZeroSolo reward)
    (hQ : IsProjectiveQBarMatrix
      (normalizedPunishmentNormalPlayerMatrix reward)) :
    ∃ witness : ContinuousZeroPerfectSingletonPath
        (quittingPunishmentNormalReward reward),
      IsContinuousAbsorptionPath witness.ambientPath ∧
        IsSequentiallyPerfectAbsorptionPath reward witness.ambientPath 0 := by
  obtain ⟨witness⟩ :=
    exists_punishmentNormal_singletonPath_of_projectiveQBar reward hnotZero hQ
  exact ⟨witness, witness.ambientLift⟩

/-- Path-only form of `exists_punishmentNormal_ambientPath_of_projectiveQBar`.
This is the assembled ambient path producer consumed by interfaces that do not
need the underlying punishment-normal mass path. -/
theorem exists_ambient_continuous_zeroPerfect_of_punishmentNormal_projectiveQBar
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnotZero : ¬IsQuittingZeroSolo reward)
    (hQ : IsProjectiveQBarMatrix
      (normalizedPunishmentNormalPlayerMatrix reward)) :
    ∃ path : AbsorptionPath (ι := ι),
      IsContinuousAbsorptionPath path ∧
        IsSequentiallyPerfectAbsorptionPath reward path 0 := by
  obtain ⟨witness, hcontinuous, hperfect⟩ :=
    exists_punishmentNormal_ambientPath_of_projectiveQBar reward hnotZero hQ
  exact ⟨witness.ambientPath, hcontinuous, hperfect⟩

end QuittingLCPClassification
end GameTheory

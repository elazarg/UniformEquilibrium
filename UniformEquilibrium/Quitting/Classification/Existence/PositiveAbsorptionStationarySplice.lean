/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.StationarilyGeneratedBranch
import UniformEquilibrium.Quitting.Classification.LCP.StationaryEquilibrium
import UniformEquilibrium.Quitting.Paths.SupportWitnessIndividualRational
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps

/-!
# Positive-absorption stationary equilibria generate punished prefixes

A stationary approximate equilibrium whose product root absorbs with positive
probability can be repeated for a long finite prefix and then followed by a
near-minmax punishment of one player with positive Quit probability.  The
resulting root sequence remains an approximate equilibrium against every
time-dependent hazard response, hence against every behavioral deviation.

The selected player is controlled by resuming the stationary marginal after
the prefix and comparing the resulting stationary deviation with the
punished tail.  Every other player is controlled by prefix stability: the
selected player's positive Quit probability makes their opponent-survival
clock contract geometrically.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A repeated root has the expected power-law joint survival. -/
theorem quittingJointSurvivalWeight_const
    (root : ι → PMF Bool) (fuel : ℕ) :
    quittingJointSurvivalWeight (fun _ => root) 0 fuel =
      quittingStationaryContinueMass root ^ fuel := by
  rw [quittingJointSurvivalWeight_eq_prod]
  simp

omit [DecidableEq ι] in
/-- One marked marginal bounds the joint survival of a repeated root. -/
theorem quittingJointSurvivalWeight_const_le_pow_continue
    (root : ι → PMF Bool) (marked : ι) (fuel : ℕ) :
    quittingJointSurvivalWeight (fun _ => root) 0 fuel ≤
      (root marked false).toReal ^ fuel := by
  rw [quittingJointSurvivalWeight_const]
  exact pow_le_pow_left₀ (quittingStationaryContinueMass_nonneg root)
    (quittingStationaryContinueMass_le_ownContinueProbability root marked) fuel

/-- If `marked` is one of `who`'s opponents, its Continue probability bounds
the whole repeated-prefix opponent-survival clock. -/
theorem quittingOpponentSurvivalWeight_const_le_pow_continue
    (root : ι → PMF Bool) (who marked : ι) (hne : marked ≠ who) (fuel : ℕ) :
    quittingOpponentSurvivalWeight (fun _ => root) who 0 fuel ≤
      (root marked false).toReal ^ fuel := by
  unfold quittingOpponentSurvivalWeight quittingFixedOpponentsContinueMass
  have hprod :
      (∏ _offset ∈ Finset.range fuel,
          quittingStationaryContinueMass
            (Function.update root who (PMF.pure false))) ≤
        ∏ _offset ∈ Finset.range fuel, (root marked false).toReal := by
    apply Finset.prod_le_prod
    · intro offset _
      exact quittingStationaryContinueMass_nonneg
        (Function.update root who (PMF.pure false))
    · intro offset _
      have hmass := quittingStationaryContinueMass_le_ownContinueProbability
        (Function.update root who (PMF.pure false)) marked
      rw [Function.update_of_ne hne] at hmass
      exact hmass
  simpa using hprod

omit [Fintype ι] [DecidableEq ι] in
/-- The stationary-prefix syntax is the ordinary phase switch at the first
stage strictly after its inclusive horizon. -/
theorem quittingStationaryPrefixThenRoots_eq_phaseSwitch
    (root : ι → PMF Bool) (horizon : ℕ)
    (punishment : ℕ → ι → PMF Bool) :
    quittingStationaryPrefixThenRoots root horizon punishment =
      quittingPhaseSwitchRoots (fun _ => root) punishment (horizon + 1) := by
  funext time
  by_cases htime : time ≤ horizon
  · rw [quittingStationaryPrefixThenRoots_of_le _ _ _ htime,
      quittingPhaseSwitchRoots_of_lt]
    omega
  · have hswitch : horizon + 1 ≤ time := by omega
    rw [quittingStationaryPrefixThenRoots, if_neg htime,
      quittingPhaseSwitchRoots_of_le _ _ hswitch]

omit [DecidableEq ι] in
/-- A positive-absorption root has a marginal with positive Quit
probability. -/
theorem exists_quitProbability_pos_of_absorptionMass_pos
    (root : ι → PMF Bool) (habsorbs : 0 < quittingRootAbsorptionMass root) :
    ∃ who, 0 < (root who true).toReal := by
  by_contra hnone
  have hzero : ∀ who, (root who true).toReal = 0 := by
    intro who
    apply le_antisymm
    · exact le_of_not_gt fun hpositive => hnone ⟨who, hpositive⟩
    · exact ENNReal.toReal_nonneg
  have hroot : root = (quittingAllContinueRoot : ι → PMF Bool) := by
    funext who
    exact Math.ProbabilityMassFunction.eq_pure_false_of_apply_true_toReal_eq_zero
      _ (hzero who)
  subst root
  unfold quittingRootAbsorptionMass at habsorbs
  rw [quittingStationaryContinueMass_eq_prod_continueProbability] at habsorbs
  simp [quittingAllContinueRoot] at habsorbs

/-- Quantifier-exact positive-absorption stationary approximability: every
positive error ceiling contains a positive-error stationary equilibrium with
positive one-stage absorption. -/
def HasArbitrarilyAccuratePositiveAbsorptionStationaryEquilibria
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ upper : ℝ, 0 < upper →
    ∃ (error : ℝ) (root : ι → PMF Bool),
      0 < error ∧ error < upper ∧
        IsεQuittingStationaryNash reward error root ∧
        0 < quittingRootAbsorptionMass root

/-- A positive-absorption stationary approximate equilibrium can be spliced
to a near-minmax punishment after a long repeated prefix.  The displayed
error leaves the punishment allowance `δ` separate, exactly as required by
`QuittingStationarilyGeneratedApproximateEquilibriaAt`.

All deviations in the conclusion are arbitrary hazard sequences; through
`isεQuittingRootSequenceNash_iff_isεAsymptoticNash`, this is the full class of
behavioral deviations, not a stationary restriction. -/
theorem exists_stationaryPrefix_punishment_nash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {η ε δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hsmall : 2 * η < ε)
    (root : ι → PMF Bool)
    (hnash : IsεQuittingStationaryNash reward η root)
    (habsorbs : 0 < quittingRootAbsorptionMass root) :
    ∃ (horizon : ℕ) (who : ι) (punishment : ℕ → ι → PMF Bool),
      1 < horizon ∧
      IsQuittingRootSequencePunishmentWithin reward who δ punishment ∧
      IsεQuittingRootSequenceNash reward (ε + δ)
        (quittingStationaryPrefixThenRoots root horizon punishment) := by
  obtain ⟨who, hwho⟩ :=
    exists_quitProbability_pos_of_absorptionMass_pos root habsorbs
  let base : ℝ := (root who false).toReal
  let M : ℝ := quittingRewardBound reward
  have hM : 0 ≤ M := quittingRewardBound_nonneg reward
  have hbase0 : 0 ≤ base := ENNReal.toReal_nonneg
  have hbase1 : base < 1 := by
    have hsum := quittingRoot_continueProbability_add_quitProbability root who
    dsimp [base]
    linarith
  have hgap : 0 < ε - 2 * η := by linarith
  have hdenom : 0 < 4 * M + 1 := by linarith
  have htarget : 0 < (ε - 2 * η) / (4 * M + 1) :=
    div_pos hgap hdenom
  obtain ⟨fuel, hfuel⟩ := exists_pow_lt_of_lt_one htarget hbase1
  let horizon : ℕ := fuel + 2
  let switch : ℕ := horizon + 1
  have hswitch : switch = fuel + 3 := by simp [switch, horizon]
  have hpow : base ^ switch < (ε - 2 * η) / (4 * M + 1) := by
    have hle : base ^ switch ≤ base ^ fuel := by
      apply pow_le_pow_of_le_one hbase0 hbase1.le
      rw [hswitch]
      omega
    exact hle.trans_lt hfuel
  have hdecay : 4 * M * base ^ switch < ε - 2 * η := by
    have hscaled : (4 * M + 1) * base ^ switch <
        (4 * M + 1) * ((ε - 2 * η) / (4 * M + 1)) :=
      mul_lt_mul_of_pos_left hpow hdenom
    have hleft : 4 * M * base ^ switch ≤
        (4 * M + 1) * base ^ switch := by
      exact mul_le_mul_of_nonneg_right (by linarith)
        (pow_nonneg hbase0 switch)
    have hcancel :
        (4 * M + 1) * ((ε - 2 * η) / (4 * M + 1)) = ε - 2 * η := by
      field_simp
    rw [hcancel] at hscaled
    exact hleft.trans_lt hscaled
  obtain ⟨punishmentRoot, hpunishmentRoot⟩ :=
    exists_stationaryRoot_cap_lt_punishmentValue_add reward who hδ
  let punishment : ℕ → ι → PMF Bool := fun _ => punishmentRoot
  have hpunish :
      IsQuittingRootSequencePunishmentWithin reward who δ punishment := by
    intro hazard
    exact (quittingRootSequenceHazardTerminalValue_const_le_cap
      reward punishmentRoot who hazard).trans hpunishmentRoot.le
  let plan : ℕ → ι → PMF Bool := fun _ => root
  have hnashPlan : IsεQuittingRootSequenceNash reward η plan := by
    apply (isεQuittingRootSequenceNash_iff_isεAsymptoticNash
      reward η plan).mpr
    have hprofile : quittingRootSequenceProfile reward plan 0 =
        quittingStationaryProfile reward root := by
      rfl
    rw [hprofile]
    exact hnash
  have hreward : ∀ terminal player, |reward terminal player| ≤ M := by
    exact abs_reward_le_quittingRewardBound reward
  have hstationaryIR : quittingPunishmentValue reward who ≤
      quittingRootSequenceTerminalValue reward plan who 0 + η := by
    have hbest : quittingBestReplyValue reward
        (quittingStationaryProfile reward root) who ≤
        quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) who + η := by
      apply quittingBestReplyValue_le
      intro deviation
      exact hnash who deviation
    have hir := (quittingPunishmentValue_le reward who
      (quittingStationaryProfile reward root)).trans hbest
    rw [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
      quittingProfileLiveRoot_stationary] at hir
    exact hir
  refine ⟨horizon, who, punishment, by simp [horizon], hpunish, ?_⟩
  rw [quittingStationaryPrefixThenRoots_eq_phaseSwitch]
  intro player hazard
  let spliced := quittingPhaseSwitchRoots plan punishment switch
  have hspliced :
      quittingPhaseSwitchRoots (fun _ => root) punishment (horizon + 1) =
        spliced := by rfl
  rw [hspliced]
  have hprefix : ∀ time, time < switch → spliced time = plan time := by
    intro time htime
    exact quittingPhaseSwitchRoots_of_lt plan punishment htime
  have hjoint : quittingJointSurvivalWeight plan 0 switch ≤ base ^ switch := by
    exact quittingJointSurvivalWeight_const_le_pow_continue root who switch
  by_cases hplayer : player = who
  · subst player
    let resume : ℕ → PMF Bool := fun time =>
      if time < switch then hazard time else root who
    have hresumePrefix : ∀ time, time < switch → resume time = hazard time := by
      intro time htime
      simp [resume, htime]
    have hupdatedPrefix : ∀ time, time < switch →
        quittingRootSequenceUpdate plan who resume time =
          quittingRootSequenceUpdate plan who hazard time := by
      intro time htime
      rw [quittingRootSequenceUpdate, quittingRootSequenceUpdate,
        hresumePrefix time htime]
    have htruncatedUpdate :
        quittingTruncatedRoots (quittingRootSequenceUpdate plan who resume) switch =
          quittingTruncatedRoots (quittingRootSequenceUpdate plan who hazard) switch := by
      funext time
      by_cases htime : time < switch
      · rw [quittingTruncatedRoots_of_lt _ htime,
          quittingTruncatedRoots_of_lt _ htime, hupdatedPrefix time htime]
      · rw [quittingTruncatedRoots_of_le _ (Nat.not_lt.mp htime),
          quittingTruncatedRoots_of_le _ (Nat.not_lt.mp htime)]
    have hupdatedSurvival :
        quittingJointSurvivalWeight
            (quittingRootSequenceUpdate plan who resume) 0 switch =
          quittingJointSurvivalWeight
            (quittingRootSequenceUpdate plan who hazard) 0 switch := by
      apply quittingJointSurvivalWeight_congr _ _ 0 switch
      intro offset hoffset
      simpa using hupdatedPrefix offset hoffset
    have hresumeTail :
        quittingRootSequenceTerminalValue reward
            (quittingRootSequenceUpdate plan who resume) who switch =
          quittingRootSequenceTerminalValue reward plan who 0 := by
      rw [quittingRootSequenceTerminalValue_eq_shift]
      apply quittingRootSequenceTerminalValue_congr reward _ _ who 0
      intro offset
      simp [resume, plan, quittingRootSequenceUpdate]
    have hresumeDecomp :
        quittingRootSequenceHazardTerminalValue reward plan who resume 0 =
          quittingRootSequenceHazardTerminalValue reward
              (quittingTruncatedRoots plan switch) who
              (quittingTruncatedHazard hazard switch) 0 +
            quittingJointSurvivalWeight
                (quittingRootSequenceUpdate plan who hazard) 0 switch *
              quittingRootSequenceTerminalValue reward plan who 0 := by
      unfold quittingRootSequenceHazardTerminalValue
      rw [quittingRootSequenceTerminalValue_eq_truncated_add_jointSurvival_mul,
        htruncatedUpdate,
        ← quittingRootSequenceUpdate_quittingTruncatedRoots plan who hazard switch,
        hupdatedSurvival, hresumeTail]
    have hsplicedDecomp :=
      quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots
        reward plan punishment switch who hazard
    have htail : quittingRootSequenceHazardTerminalValue reward punishment who
          (fun offset => hazard (switch + offset)) 0 ≤
        quittingRootSequenceTerminalValue reward plan who 0 + η + δ := by
      have := hpunish (fun offset => hazard (switch + offset))
      linarith
    let survival := quittingJointSurvivalWeight
      (quittingRootSequenceUpdate plan who hazard) 0 switch
    have hsurvival0 : 0 ≤ survival :=
      quittingJointSurvivalWeight_nonneg _ 0 switch
    have hsurvival1 : survival ≤ 1 :=
      quittingJointSurvivalWeight_le_one _ 0 switch
    have hsplicedDeviation :
        quittingRootSequenceHazardTerminalValue reward spliced who hazard 0 ≤
          quittingRootSequenceHazardTerminalValue reward plan who resume 0 +
            η + δ := by
      have htailScaled := mul_le_mul_of_nonneg_left htail hsurvival0
      rw [hsplicedDecomp, hresumeDecomp]
      dsimp only [survival] at hsurvival0 hsurvival1 ⊢
      have herrorScaled :
          quittingJointSurvivalWeight
                (quittingRootSequenceUpdate plan who hazard) 0 switch *
              (η + δ) ≤ η + δ := by
        have herror0 : 0 ≤ η + δ := by linarith
        simpa using mul_le_mul_of_nonneg_right hsurvival1 herror0
      linarith
    have hresumeNash := hnashPlan who resume
    have hprescribed := abs_quittingRootSequenceTerminalValue_sub_le_of_prefix_eq
      reward spliced plan who switch hreward hprefix
    have hprescribed' :
        quittingRootSequenceTerminalValue reward plan who 0 -
            quittingRootSequenceTerminalValue reward spliced who 0 ≤
          2 * M * base ^ switch := by
      have hnegative := neg_le_of_abs_le hprescribed
      have hscaled : 2 * M * quittingJointSurvivalWeight plan 0 switch ≤
          2 * M * base ^ switch :=
        mul_le_mul_of_nonneg_left hjoint (mul_nonneg (by norm_num) hM)
      linarith
    have hhalfDecay : 2 * M * base ^ switch ≤
        4 * M * base ^ switch := by
      exact mul_le_mul_of_nonneg_right (by linarith)
        (pow_nonneg hbase0 switch)
    linarith
  · have hopponent : quittingOpponentSurvivalWeight plan player 0 switch ≤
        base ^ switch := by
      exact quittingOpponentSurvivalWeight_const_le_pow_continue
        root player who (Ne.symm hplayer) switch
    have hdeviation := abs_quittingRootSequenceHazardTerminalValue_sub_le_of_prefix_eq
      reward spliced plan player hazard switch hreward hprefix
    have hprescribed := abs_quittingRootSequenceTerminalValue_sub_le_of_prefix_eq
      reward spliced plan player switch hreward hprefix
    have hdeviation' :
        quittingRootSequenceHazardTerminalValue reward spliced player hazard 0 -
            quittingRootSequenceHazardTerminalValue reward plan player hazard 0 ≤
          2 * M * base ^ switch := by
      exact (le_of_abs_le hdeviation).trans
        (mul_le_mul_of_nonneg_left hopponent (mul_nonneg (by norm_num) hM))
    have hprescribed' :
        quittingRootSequenceTerminalValue reward plan player 0 -
            quittingRootSequenceTerminalValue reward spliced player 0 ≤
          2 * M * base ^ switch := by
      have hnegative := neg_le_of_abs_le hprescribed
      have hscaled : 2 * M * quittingJointSurvivalWeight plan 0 switch ≤
          2 * M * base ^ switch :=
        mul_le_mul_of_nonneg_left hjoint (mul_nonneg (by norm_num) hM)
      linarith
    have hplanNash := hnashPlan player hazard
    have hhalfDecay : 2 * M * base ^ switch ≤
        4 * M * base ^ switch := by
      exact mul_le_mul_of_nonneg_right (by linarith)
        (pow_nonneg hbase0 switch)
    linarith

/-- **Positive-absorption stationary approximability generates Simon's
stationary-prefix branch.** -/
theorem quittingStationarilyGeneratedApproximateEquilibria_of_positiveAbsorptionStationary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hstationary :
      HasArbitrarilyAccuratePositiveAbsorptionStationaryEquilibria reward) :
    QuittingStationarilyGeneratedApproximateEquilibria reward := by
  intro δ hδ ε hε
  obtain ⟨η, root, hη, hηsmall, hnash, habsorbs⟩ :=
    hstationary (ε / 3) (by linarith)
  obtain ⟨horizon, who, punishment, hhorizon, hpunish, hsplice⟩ :=
    exists_stationaryPrefix_punishment_nash (ε := ε) reward hη hδ
      (by nlinarith) root hnash habsorbs
  exact ⟨root, horizon, who, punishment, hhorizon, hpunish, hsplice⟩

/-- Literal every-error adapter: stationary behavioral equilibria with
positive absorption at every positive accuracy satisfy the cofinal input of
the splice theorem. -/
theorem quittingStationarilyGeneratedApproximateEquilibria_of_forall_positiveAbsorptionStationary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hstationary : ∀ error : ℝ, 0 < error →
      ∃ root : ι → PMF Bool,
        IsεQuittingStationaryNash reward error root ∧
          0 < quittingRootAbsorptionMass root) :
    QuittingStationarilyGeneratedApproximateEquilibria reward := by
  apply quittingStationarilyGeneratedApproximateEquilibria_of_positiveAbsorptionStationary
    reward
  intro upper hupper
  obtain ⟨root, hnash, habsorbs⟩ :=
    hstationary (upper / 2) (by linarith)
  exact ⟨upper / 2, root, by linarith, by linarith, hnash, habsorbs⟩

end GameTheory

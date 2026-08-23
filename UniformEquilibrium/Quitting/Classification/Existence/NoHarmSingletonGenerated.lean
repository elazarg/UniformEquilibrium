/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.PositiveAbsorptionStationarySplice
import UniformEquilibrium.Quitting.Punishment.SoloFloorCompletion

/-!
# Stationarily generated play from a no-harm singleton owner

Suppose one player's singleton row weakly dominates every outsider's own
singleton payoff, coordinate by coordinate, and that the owner is normal in
the punishment-value sense.  A vanishing positive solo hazard then has only a
vanishing outsider incentive defect.  Repeating that row for a long finite
prefix and following it by an actual near-minmax punishment controls the
owner's deleted clock even when the owner's singleton payoff is negative.

The result below produces the repository's stationarily generated witness,
not merely a uniform payoff.  All unilateral deviations in its conclusion are
arbitrary time-dependent hazards, hence arbitrary behavioral deviations.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A solo row whose outsiders have a supplied vanishing unilateral-cap error
produces a genuine stationary-prefix witness after punishment completion. -/
theorem quittingStationarilyGeneratedApproximateEquilibria_of_approximate_solo_caps
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : ℕ → PMF Bool) (error : ℕ → ℝ)
    (hpositive : ∀ n, 0 < (hazard n true).toReal)
    (herror0 : ∀ n, 0 ≤ error n)
    (herrorVanish : Tendsto error atTop (nhds 0))
    (hcap : ∀ n other, other ≠ owner →
      quittingStationaryUnilateralCap reward
          (quittingSoloStationaryRoot owner (hazard n)) other ≤
        quittingSoloReward reward owner other + error n)
    (hpunishment : quittingPunishmentValue reward owner ≤
      quittingSoloReward reward owner owner) :
    QuittingStationarilyGeneratedApproximateEquilibria reward := by
  intro δ hδ ε hε
  have heventually : ∀ᶠ n : ℕ in atTop, error n < ε / 2 :=
    (tendsto_order.1 herrorVanish).2 (ε / 2) (by linarith)
  obtain ⟨n, hn⟩ := heventually.exists
  let root := quittingSoloStationaryRoot owner (hazard n)
  let plan : ℕ → ι → PMF Bool := fun _ => root
  let base := (hazard n false).toReal
  let M := quittingRewardBound reward
  have hM : 0 ≤ M := quittingRewardBound_nonneg reward
  have hbase0 : 0 ≤ base := ENNReal.toReal_nonneg
  have hbase1 : base < 1 := by
    have hsum := quittingSoloHazardMass_add (hazard n)
    dsimp only [base]
    linarith [hpositive n]
  have hgap : 0 < ε - error n := by linarith
  have hdenom : 0 < 4 * M + 1 := by linarith
  have htarget : 0 < (ε - error n) / (4 * M + 1) :=
    div_pos hgap hdenom
  obtain ⟨fuel, hfuel⟩ := exists_pow_lt_of_lt_one htarget hbase1
  let horizon := fuel + 2
  let switch := horizon + 1
  have hswitchEq : switch = fuel + 3 := by simp [switch, horizon]
  have hpow : base ^ switch < (ε - error n) / (4 * M + 1) := by
    have hle : base ^ switch ≤ base ^ fuel := by
      apply pow_le_pow_of_le_one hbase0 hbase1.le
      rw [hswitchEq]
      omega
    exact hle.trans_lt hfuel
  have hdecay : 4 * M * base ^ switch < ε - error n := by
    have hscaled : (4 * M + 1) * base ^ switch <
        (4 * M + 1) * ((ε - error n) / (4 * M + 1)) :=
      mul_lt_mul_of_pos_left hpow hdenom
    have hleft : 4 * M * base ^ switch ≤
        (4 * M + 1) * base ^ switch := by
      exact mul_le_mul_of_nonneg_right (by linarith)
        (pow_nonneg hbase0 switch)
    have hcancel :
        (4 * M + 1) * ((ε - error n) / (4 * M + 1)) = ε - error n := by
      field_simp
    rw [hcancel] at hscaled
    exact hleft.trans_lt hscaled
  obtain ⟨punishmentRoot, hpunishmentRoot⟩ :=
    exists_stationaryRoot_cap_lt_punishmentValue_add reward owner hδ
  let punishment : ℕ → ι → PMF Bool := fun _ => punishmentRoot
  have hpunish :
      IsQuittingRootSequencePunishmentWithin reward owner δ punishment := by
    intro response
    exact (quittingRootSequenceHazardTerminalValue_const_le_cap
      reward punishmentRoot owner response).trans hpunishmentRoot.le
  have hplanValue : ∀ who,
      quittingRootSequenceTerminalValue reward plan who 0 =
        quittingSoloReward reward owner who := by
    intro who
    change quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) who = _
    dsimp only [root]
    exact quittingTerminalPayoff_soloStationary reward owner who
      (hazard n) (hpositive n)
  have hprefix : ∀ time, time < switch →
      (quittingPhaseSwitchRoots plan punishment switch) time = plan time := by
    intro time htime
    exact quittingPhaseSwitchRoots_of_lt plan punishment htime
  have hjoint : quittingJointSurvivalWeight plan 0 switch ≤ base ^ switch := by
    dsimp only [plan, root]
    simpa [base, quittingSoloStationaryRoot] using
      (quittingJointSurvivalWeight_const_le_pow_continue
        (quittingSoloStationaryRoot owner (hazard n)) owner switch)
  have hopponent : ∀ who, who ≠ owner →
      quittingOpponentSurvivalWeight plan who 0 switch ≤ base ^ switch := by
    intro who hwho
    dsimp only [plan, root]
    simpa [base, quittingSoloStationaryRoot] using
      (quittingOpponentSurvivalWeight_const_le_pow_continue
        (quittingSoloStationaryRoot owner (hazard n)) who owner
          (Ne.symm hwho) switch)
  refine ⟨root, horizon, owner, punishment, by simp [horizon], hpunish, ?_⟩
  rw [quittingStationaryPrefixThenRoots_eq_phaseSwitch]
  intro who response
  change quittingRootSequenceHazardTerminalValue reward
      (quittingPhaseSwitchRoots plan punishment switch) who response 0 ≤
    quittingRootSequenceTerminalValue reward
        (quittingPhaseSwitchRoots plan punishment switch) who 0 + (ε + δ)
  by_cases hwho : who = owner
  · subst who
    have hisolated : ∀ time,
        IsQuittingIsolatedRoot (plan time) owner := by
      intro time other hother
      simp [plan, root, quittingSoloStationaryRoot, hother]
    have hprefixCap : ∀ g : ℕ → PMF Bool,
        quittingRootSequenceHazardTerminalValue reward
            (quittingTruncatedRoots plan switch) owner
            (quittingTruncatedHazard g switch) 0 ≤
          (1 - quittingJointSurvivalWeight
            (quittingRootSequenceUpdate plan owner g) 0 switch) *
              quittingSoloReward reward owner owner + 0 := by
      intro g
      rw [add_zero]
      exact le_of_eq
        (quittingRootSequenceHazardTerminalValue_truncated_eq_one_sub_survival_mul_of_isolated
          reward plan owner g switch (fun time _ => hisolated time))
    have htail : ∀ g : ℕ → PMF Bool,
        quittingRootSequenceHazardTerminalValue reward punishment owner g 0 ≤
          quittingSoloReward reward owner owner + δ := by
      intro g
      exact (hpunish g).trans (by
        simpa [add_comm] using add_le_add_right hpunishment δ)
    have hdeviation :=
      quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots_le_coupled
        reward plan punishment switch owner hδ.le hprefixCap htail response
    have hclose :=
      abs_quittingRootSequenceTerminalValue_quittingPhaseSwitchRoots_sub_plan_le
        reward plan punishment switch owner hM
          (abs_reward_le_quittingRewardBound reward)
    have hreach : 2 * M * quittingJointSurvivalWeight plan 0 switch ≤
        2 * M * base ^ switch :=
      mul_le_mul_of_nonneg_left hjoint (mul_nonneg (by norm_num) hM)
    rw [hplanValue owner] at hclose
    have hlower := (abs_le.mp hclose).1
    have hhalfDecay : 2 * M * base ^ switch ≤ 4 * M * base ^ switch :=
      mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hbase0 switch)
    have hprescribedLower :
        quittingSoloReward reward owner owner - 2 * M * base ^ switch ≤
          quittingRootSequenceTerminalValue reward
            (quittingPhaseSwitchRoots plan punishment switch) owner 0 := by
      linarith
    have hsmall : 2 * M * base ^ switch < ε := by
      have : 4 * M * base ^ switch < ε := by
        linarith [herror0 n]
      exact hhalfDecay.trans_lt this
    linarith
  · have hplanDeviation :
        quittingRootSequenceHazardTerminalValue reward plan who response 0 ≤
          quittingRootSequenceTerminalValue reward plan who 0 + error n := by
      have hcapBound := quittingRootSequenceHazardTerminalValue_const_le_cap
        reward root who response
      rw [hplanValue who]
      exact hcapBound.trans (hcap n who hwho)
    have hdeviation :=
      quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots_le_of_plan_add
        reward plan punishment switch who response hM
          (abs_reward_le_quittingRewardBound reward) hplanDeviation
    have hreach : 4 * M *
        quittingOpponentSurvivalWeight plan who 0 switch ≤
          4 * M * base ^ switch :=
      mul_le_mul_of_nonneg_left (hopponent who hwho)
        (mul_nonneg (by norm_num) hM)
    linarith

/-- A normal singleton owner whose row does not harm any outsider generates
arbitrarily accurate stationary-prefix equilibria with actual punishment. -/
theorem quittingStationarilyGeneratedApproximateEquilibria_of_normal_noHarmSingleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι)
    (hnoHarm : ∀ other, other ≠ owner →
      quittingSoloReward reward other other ≤
        quittingSoloReward reward owner other)
    (hnormal : quittingPunishmentValue reward owner ≤
      quittingSoloReward reward owner owner) :
    QuittingStationarilyGeneratedApproximateEquilibria reward := by
  let rate : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hratePos : ∀ n, 0 < rate n := by
    intro n
    dsimp only [rate]
    positivity
  have hrateOne : ∀ n, rate n ≤ 1 := by
    intro n
    dsimp only [rate]
    apply (div_le_one (by positivity)).2
    exact_mod_cast (show (1 : ℕ) ≤ n + 1 by omega)
  have hrateVanish : Tendsto rate atTop (nhds 0) := by
    simpa only [rate] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (nhds 0))
  let hazard : ℕ → PMF Bool := fun n =>
    quittingHazardCoin (rate n) (hratePos n).le (hrateOne n)
  let error : ℕ → ℝ := fun n => 2 * quittingRewardBound reward * rate n
  have herror0 : ∀ n, 0 ≤ error n := by
    intro n
    exact mul_nonneg
      (mul_nonneg (by norm_num) (quittingRewardBound_nonneg reward))
      (hratePos n).le
  have herrorVanish : Tendsto error atTop (nhds 0) := by
    simpa [error, mul_assoc] using
      hrateVanish.const_mul (2 * quittingRewardBound reward)
  apply quittingStationarilyGeneratedApproximateEquilibria_of_approximate_solo_caps
    reward owner hazard error
  · intro n
    simp [hazard, hratePos n]
  · exact herror0
  · exact herrorVanish
  · intro n other hother
    let M := quittingRewardBound reward
    let target := quittingSoloReward reward owner other
    let solo := quittingSoloReward reward other other
    let collision := quittingSingletonCollisionReward reward owner other
    have hM : 0 ≤ M := quittingRewardBound_nonneg reward
    have hcollision : collision ≤ M := by
      exact (le_abs_self collision).trans (by
        simpa [M, collision, quittingSingletonCollisionReward] using
          (abs_reward_le_quittingRewardBound reward
            ⟨{owner, other}, by simp⟩ other))
    have htargetAbs : |target| ≤ M := by
      change |reward (quittingSingletonTerminal owner) other| ≤
        quittingRewardBound reward
      exact abs_reward_le_quittingRewardBound reward
        (quittingSingletonTerminal owner) other
    have hspread : collision - target ≤ 2 * M := by
      have htargetLower := (abs_le.mp htargetAbs).1
      linarith
    have hcontinue : 0 ≤ 1 - rate n := sub_nonneg.mpr (hrateOne n)
    rw [quittingStationaryUnilateralCap_solo_other
      reward hother (hazard n) (by simp [hazard, hratePos n])]
    apply max_le
    · rw [quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix
        reward hother (hazard n)]
      have htrue : (hazard n true).toReal = rate n := by simp [hazard]
      have hfalse : (hazard n false).toReal = 1 - rate n := by simp [hazard]
      rw [htrue, hfalse]
      calc
        (1 - rate n) * solo + rate n * collision ≤
            (1 - rate n) * target + rate n * collision := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (hnoHarm other hother) hcontinue)
            (le_refl _)
        _ = target + rate n * (collision - target) := by ring
        _ ≤ target + rate n * (2 * M) := by gcongr
        _ = quittingSoloReward reward owner other + error n := by
          dsimp only [target, M, error]
          ring
    · exact le_add_of_nonneg_right (herror0 n)
  · exact hnormal

end GameTheory

/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.FixedPrefixArbitraryTailBarrier
import UniformEquilibrium.Quitting.Cycles.SoloRootSequenceValues
import UniformEquilibrium.Quitting.Root.TerminalSemanticEqualityStratum

/-!
# Global finite-clock comparison for the fixed-prefix barrier table

For the same normalized Fin4 reward table used by the fixed-prefix arbitrary-tail
barrier, this module constructs a fresh profile at every positive clock length.
Players `0` and `1` independently stop uniformly over the available dates, while
players `2` and `3` never stop.  Its unrestricted behavioral exploitability is
exactly `2 / length`, and therefore converges to zero.

This global reselection does not repair a previously fixed prefix.  It supplies
the comparison family on the other side of that prefix obstruction.
-/

noncomputable section

namespace GameTheory
namespace FixedPrefixSameTableGlobalComparison

open Filter Math.Probability Math.ProbabilityMassFunction Math.PMFProduct
open FixedPrefixArbitraryTailBarrier

abbrev Player := FixedPrefixArbitraryTailBarrier.Player

/-- The hazard realizing the uniform law on dates `0, ..., length - 1`. -/
def uniformHazard (length time : ℕ) : ℝ :=
  if time < length then 1 / ((length - time : ℕ) : ℝ) else 0

theorem uniformHazard_nonneg (length time : ℕ) :
    0 ≤ uniformHazard length time := by
  unfold uniformHazard
  split_ifs
  · positivity
  · exact le_rfl

theorem uniformHazard_le_one (length time : ℕ) :
    uniformHazard length time ≤ 1 := by
  unfold uniformHazard
  split_ifs with htime
  · have hpos : 0 < length - time := by omega
    rw [div_le_one (by positivity : (0 : ℝ) < (length - time : ℕ))]
    exact_mod_cast hpos
  · norm_num

/-- Both active players stop uniformly on the first `length` dates. -/
def roots (length : ℕ) : ℕ → Player → PMF Bool := fun time who ↦
  if who = 0 ∨ who = 1 then
    bernoulliBool (uniformHazard length time)
      (uniformHazard_nonneg length time) (uniformHazard_le_one length time)
  else PMF.pure false

@[simp] theorem roots_zero_true_toReal (length time : ℕ) :
    (roots length time 0 true).toReal = uniformHazard length time := by
  simp [roots]

@[simp] theorem roots_zero_false_toReal (length time : ℕ) :
    (roots length time 0 false).toReal = 1 - uniformHazard length time := by
  simp [roots]

@[simp] theorem roots_one_true_toReal (length time : ℕ) :
    (roots length time 1 true).toReal = uniformHazard length time := by
  simp [roots]

@[simp] theorem roots_one_false_toReal (length time : ℕ) :
    (roots length time 1 false).toReal = 1 - uniformHazard length time := by
  simp [roots]

theorem roots_dummy (length time : ℕ) (who : Player) (htwo : 2 ≤ who) :
    roots length time who = PMF.pure false := by
  fin_cases who <;> simp_all [roots]

theorem roots_eq_allContinue_of_le
    (length time : ℕ) (htime : length ≤ time) :
    roots length time = (quittingAllContinueRoot : Player → PMF Bool) := by
  funext who
  fin_cases who <;> simp only [roots, Fin.isValue, quittingAllContinueRoot]
  all_goals
    apply eq_pure_false_of_apply_true_toReal_eq_zero
    simp [uniformHazard, Nat.not_lt.mpr htime]

/-- The finite policy-evaluation value with `length - time` dates left. -/
def value (length time : ℕ) : Payoff Player := fun who ↦
  if time < length then
    if who = 0 then 1 - 2 / ((length - time : ℕ) : ℝ)
    else if who = 1 then -(1 - 2 / ((length - time : ℕ) : ℝ))
    else 0
  else 0

theorem value_eq_zero_of_le (length time : ℕ) (htime : length ≤ time) :
    value length time = 0 := by
  funext who
  simp [value, Nat.not_lt.mpr htime]

private theorem value_policy
    (length time : ℕ) (htime : time < length) :
    value length time = quittingRootSuccessorPayoff reward
      (value length (time + 1)) (roots length time) := by
  by_cases hnext : time + 1 < length
  · have hsub : length - (time + 1) = length - time - 1 := by omega
    have hcast : ((length - time : ℕ) : ℝ) = length - time := by
      exact_mod_cast Nat.cast_sub htime.le
    have htimeCast : (time : ℝ) < length := by exact_mod_cast htime
    have hnextCast : ((time + 1 : ℕ) : ℝ) < length := by
      exact_mod_cast hnext
    have hrPos : (0 : ℝ) < length - time := by linarith
    have hrNextPos : (0 : ℝ) < -1 + length - time := by
      norm_num at hnextCast ⊢
      linarith
    have hrNextPos' : (0 : ℝ) < length - time - 1 := by linarith
    funext who
    fin_cases who
    all_goals
      unfold quittingRootSuccessorPayoff quittingRootExpectedPayoff
      rw [expect_pmfPi_fin4]
      simp [value, roots, uniformHazard, htime, hnext, reward,
        quittingRootPayoff, quittingQuitters,
        Math.Probability.expect_eq_sum, hsub, hcast]
    case «0» =>
      field_simp [ne_of_gt hrPos, ne_of_gt hrNextPos']
      ring
    case «1» =>
      field_simp [ne_of_gt hrPos, ne_of_gt hrNextPos']
      ring
  · have hlast : length = time + 1 := by omega
    subst length
    funext who
    fin_cases who <;>
      unfold quittingRootSuccessorPayoff quittingRootExpectedPayoff <;>
      rw [expect_pmfPi_fin4] <;>
      simp [value, roots, uniformHazard, reward, quittingRootPayoff,
        quittingQuitters, Math.Probability.expect_eq_sum] <;>
      norm_num

/-- The selected finite chain is the literal terminal payoff of the root sequence. -/
theorem value_eq_terminalValue (length time : ℕ) (htime : time ≤ length) :
    value length time = fun who ↦
      quittingRootSequenceTerminalValue reward (roots length) who time := by
  exact eq_quittingRootSequenceTerminalValue_of_finite_zeroBoundary
    reward (roots length) (value length) length
    (roots_eq_allContinue_of_le length)
    (value_eq_zero_of_le length length le_rfl)
    (value_policy length) time htime

/-- The freshly reselected finite-clock profile. -/
def profile (length : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingRootSequenceProfile reward (roots length) 0

@[simp] theorem profile_liveRoot (length time : ℕ) :
    quittingProfileLiveRoot reward (profile length) time = roots length time := by
  simp [profile]

/-- Exact payoff vector of the global comparison profile. -/
theorem profile_payoff (length : ℕ) (hlength : 0 < length) :
    quittingTerminalPayoff reward (profile length) = value length 0 := by
  funext who
  rw [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot]
  have hroots : quittingProfileLiveRoot reward (profile length) = roots length := by
    funext time
    exact profile_liveRoot length time
  rw [hroots]
  exact (congrFun (value_eq_terminalValue length 0 hlength.le) who).symm

/-! ## Player `1`'s exact behavioral cap -/

/-- The opponent-only version of the clock, used to evaluate player `1`'s
deviations after deleting player `1`'s prescribed marginal. -/
def soloRoots (length : ℕ) : ℕ → Player → PMF Bool := fun time ↦
  Function.update (roots length time) 1 (PMF.pure false)

@[simp] theorem soloRoots_zero_true_toReal (length time : ℕ) :
    (soloRoots length time 0 true).toReal = uniformHazard length time := by
  simp [soloRoots]

@[simp] theorem soloRoots_zero_false_toReal (length time : ℕ) :
    (soloRoots length time 0 false).toReal = 1 - uniformHazard length time := by
  simp [soloRoots]

theorem soloRoots_solo (length time : ℕ) :
    ∀ who, who ≠ (0 : Player) → soloRoots length time who = PMF.pure false := by
  intro who hwho
  fin_cases who <;> simp_all [soloRoots, roots]

theorem soloRoots_opponentSurvival_one
    (length phase : ℕ) (hlength : 0 < length) (hphase : phase ≤ length) :
    quittingOpponentSurvivalWeight (soloRoots length) 1 0 phase =
      ((length - phase : ℕ) : ℝ) / length := by
  induction phase with
  | zero =>
      simp [quittingOpponentSurvivalWeight,
        show (length : ℝ) ≠ 0 by exact_mod_cast ne_of_gt hlength]
  | succ phase ih =>
      have hphaseLt : phase < length := by omega
      have hsubPos : 0 < length - phase := by omega
      have hcastSub : ((length - phase : ℕ) : ℝ) =
          (length : ℝ) - phase := by
        exact_mod_cast Nat.cast_sub hphaseLt.le
      have hsubSucc : length - (phase + 1) = length - phase - 1 := by omega
      have hsubCastPos : (0 : ℝ) < (length - phase : ℕ) := by
        exact_mod_cast hsubPos
      have hdenNe : (length : ℝ) - phase ≠ 0 := by
        rw [← hcastSub]
        exact ne_of_gt hsubCastPos
      rw [show phase + 1 = phase.succ by rfl,
        quittingOpponentSurvivalWeight_succ]
      simp only [Nat.zero_add]
      rw [ih hphaseLt.le]
      rw [quittingFixedOpponentsContinueMass_eq_of_soloRoot
        (soloRoots length) (soloRoots_solo length phase)
        (by norm_num : (1 : Player) ≠ 0)]
      rw [soloRoots_zero_false_toReal]
      simp only [uniformHazard, if_pos hphaseLt]
      rw [hsubSucc, Nat.cast_sub (by omega : 1 ≤ length - phase),
        Nat.cast_one, hcastSub]
      field_simp [show (length : ℝ) ≠ 0 by exact_mod_cast ne_of_gt hlength,
        hdenNe]

theorem soloRoots_opponentSurvival_one_eq_zero_of_le
    (length phase : ℕ) (hlength : 0 < length) (hphase : length ≤ phase) :
    quittingOpponentSurvivalWeight (soloRoots length) 1 0 phase = 0 := by
  have hsum : length + (phase - length) = phase := by omega
  rw [← hsum, quittingOpponentSurvivalWeight_add,
    soloRoots_opponentSurvival_one length length hlength le_rfl]
  simp

private theorem soloRoots_jointSurvivalLimit_eq_zero
    (length : ℕ) (hlength : 0 < length) :
    quittingJointSurvivalLimit (soloRoots length) 0 = 0 := by
  have hopponent : quittingOpponentSurvivalWeight
      (soloRoots length) 1 0 length = 0 :=
    soloRoots_opponentSurvival_one_eq_zero_of_le
      length length hlength le_rfl
  have hjoint : quittingJointSurvivalWeight
      (soloRoots length) 0 length ≤ 0 := by
    simpa [hopponent] using
      (quittingJointSurvivalWeight_le_quittingOpponentSurvivalWeight
        (soloRoots length) 1 0 length)
  apply le_antisymm
  · have hlimit : quittingJointSurvivalLimit (soloRoots length) 0 ≤
        quittingJointSurvivalWeight (soloRoots length) 0 length := by
      unfold quittingJointSurvivalLimit
      apply ciInf_le
      refine ⟨0, ?_⟩
      rintro _ ⟨fuel, rfl⟩
      exact quittingJointSurvivalWeight_nonneg (soloRoots length) 0 fuel
    exact hlimit.trans hjoint
  · exact quittingJointSurvivalLimit_nonneg (soloRoots length) 0

private theorem pureTimeValue_one_roots_eq_soloRoots
    (length : ℕ) (choice : Option ℕ) :
    quittingRootSequencePureTimeTerminalValue reward
        (roots length) 1 choice 0 =
      quittingRootSequencePureTimeTerminalValue reward
        (soloRoots length) 1 choice 0 := by
  have hupdate : quittingRootSequenceUpdate (roots length) 1
      (quittingPureTimeHazard choice) =
        quittingRootSequenceUpdate (soloRoots length) 1
          (quittingPureTimeHazard choice) := by
    funext time who
    unfold quittingRootSequenceUpdate soloRoots
    by_cases hwho : who = (1 : Player)
    · subst who
      simp
    · simp [Function.update_of_ne hwho]
  unfold quittingRootSequencePureTimeTerminalValue
    quittingRootSequenceHazardTerminalValue
  rw [hupdate]

theorem pureTimeValue_one_eq
    (length phase : ℕ) (hlength : 0 < length) (hphase : phase < length) :
    quittingRootSequencePureTimeTerminalValue reward
        (roots length) 1 (some phase) 0 = -1 + 2 / length := by
  rw [pureTimeValue_one_roots_eq_soloRoots]
  rw [show phase = 0 + phase by omega,
    quittingRootSequencePureTimeTerminalValue_some_eq_of_soloRoots
      reward (soloRoots length) (by norm_num : (1 : Player) ≠ 0)
      (fun time ↦ soloRoots_solo length time) 0 phase]
  simp only [Nat.zero_add]
  rw [soloRoots_opponentSurvival_one length phase hlength hphase.le,
    soloRoots_zero_false_toReal, soloRoots_zero_true_toReal]
  simp only [uniformHazard, if_pos hphase]
  simp [quittingSoloReward, quittingSingletonCollisionReward, reward]
  have hlengthNe : (length : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt hlength
  have hsubPos : 0 < length - phase := by omega
  have hsubNe : ((length - phase : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt hsubPos
  field_simp [hlengthNe, hsubNe]
  ring

theorem pureTimeValue_one_eq_neg_one_of_le
    (length phase : ℕ) (hlength : 0 < length) (hphase : length ≤ phase) :
    quittingRootSequencePureTimeTerminalValue reward
        (roots length) 1 (some phase) 0 = -1 := by
  rw [pureTimeValue_one_roots_eq_soloRoots]
  rw [show phase = 0 + phase by omega,
    quittingRootSequencePureTimeTerminalValue_some_eq_of_soloRoots
      reward (soloRoots length) (by norm_num : (1 : Player) ≠ 0)
      (fun time ↦ soloRoots_solo length time) 0 phase]
  simp only [Nat.zero_add]
  rw [soloRoots_opponentSurvival_one_eq_zero_of_le
    length phase hlength hphase]
  simp [quittingSoloReward, reward]

theorem pureTimeValue_one_none
    (length : ℕ) (hlength : 0 < length) :
    quittingRootSequencePureTimeTerminalValue reward
        (roots length) 1 none 0 = -1 := by
  rw [pureTimeValue_one_roots_eq_soloRoots]
  unfold quittingRootSequencePureTimeTerminalValue
    quittingRootSequenceHazardTerminalValue
  have hupdate : quittingRootSequenceUpdate
      (soloRoots length) 1 (fun _ ↦ PMF.pure false) = soloRoots length := by
    funext time who
    by_cases hwho : who = (1 : Player)
    · subst who
      simp [quittingRootSequenceUpdate, soloRoots]
    · simp [quittingRootSequenceUpdate, Function.update_of_ne hwho]
  rw [show quittingPureTimeHazard none = fun _ ↦ PMF.pure false by rfl,
    hupdate]
  have hvalue := quittingRootSequenceTerminalValue_eq_soloReward_of_absorbing
    reward (soloRoots length) 0 0 (fun time ↦ soloRoots_solo length time)
    (by
      rw [quittingLiveMassLimit_rootSequence_eq_jointSurvivalLimit]
      exact soloRoots_jointSurvivalLimit_eq_zero length hlength) 1
  simpa [quittingSoloReward, reward] using hvalue

/-- Player `1`'s unrestricted behavioral cap is its common in-window payoff. -/
theorem profile_bestResponse_one
    (length : ℕ) (hlength : 0 < length) :
    quittingContinuationBestResponseValue reward (profile length) 1 =
      -1 + 2 / length := by
  unfold quittingContinuationBestResponseValue
  rw [sSup_range_quittingTerminalPayoff_update_eq_pureTime]
  apply le_antisymm
  · apply csSup_le
    · exact Set.range_nonempty _
    · rintro payoff ⟨choice, rfl⟩
      change quittingTerminalPayoff reward
          (Function.update (profile length) 1
            (quittingPureTimeBehaviorStrategy reward 1 choice)) 1 ≤ _
      rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
      have hroots : quittingProfileLiveRoot reward (profile length) = roots length := by
        funext time
        exact profile_liveRoot length time
      rw [hroots]
      cases choice with
      | none =>
          rw [pureTimeValue_one_none length hlength]
          have hnonneg : (0 : ℝ) ≤ 2 / length := by positivity
          linarith
      | some phase =>
          by_cases hphase : phase < length
          · rw [pureTimeValue_one_eq length phase hlength hphase]
          · rw [pureTimeValue_one_eq_neg_one_of_le length phase hlength
              (Nat.le_of_not_gt hphase)]
            have hnonneg : (0 : ℝ) ≤ 2 / length := by positivity
            linarith
  · apply le_csSup
    · refine ⟨quittingRewardBound reward, ?_⟩
      rintro payoff ⟨choice, rfl⟩
      exact (le_abs_self _).trans
        (abs_quittingTerminalPayoff_le_quittingRewardBound reward _ 1)
    · refine ⟨some 0, ?_⟩
      change quittingTerminalPayoff reward
        (Function.update (profile length) 1
          (quittingPureTimeBehaviorStrategy reward 1 (some 0))) 1 = _
      rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
      have hroots : quittingProfileLiveRoot reward (profile length) = roots length := by
        funext time
        exact profile_liveRoot length time
      rw [hroots]
      exact pureTimeValue_one_eq length 0 hlength hlength

/-! ## Exact debt, exploitability, and vanishing comparison error -/

theorem profile_bestResponse_zero (length : ℕ) :
    quittingContinuationBestResponseValue reward (profile length) 0 = 1 := by
  change quittingRootSequenceBestResponseValue reward (roots length) 0 = 1
  exact rootSequenceBestResponseValue_zero_eq_one (roots length)

private theorem terminalPayoff_dummy_nonpos
    (candidate : (quittingGame reward).BehaviorProfile)
    (who : Player) (htwo : 2 ≤ who) :
    quittingTerminalPayoff reward candidate who ≤ 0 := by
  unfold quittingTerminalPayoff
  apply Finset.sum_nonpos
  intro terminal _
  apply mul_nonpos_of_nonneg_of_nonpos
  · exact quittingAbsorbedMassLimit_nonneg reward candidate terminal
  · fin_cases who <;> simp_all [reward]
    all_goals split <;> norm_num

theorem profile_bestResponse_dummy
    (length : ℕ) (hlength : 0 < length)
    (who : Player) (htwo : 2 ≤ who) :
    quittingContinuationBestResponseValue reward (profile length) who = 0 := by
  unfold quittingContinuationBestResponseValue
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, profile length who, rfl⟩
    · rintro payoff ⟨deviation, rfl⟩
      exact terminalPayoff_dummy_nonpos _ who htwo
  · apply le_csSup
    · exact bddAbove_range_quittingTerminalPayoff_update reward (profile length) who
    · refine ⟨profile length who, ?_⟩
      change quittingTerminalPayoff reward
        (Function.update (profile length) who (profile length who)) who = 0
      rw [Function.update_eq_self]
      rw [congrFun (profile_payoff length hlength) who]
      fin_cases who <;> simp_all [value]

/-- Exact unrestricted cap of every coordinate. -/
theorem profile_bestResponse
    (length : ℕ) (hlength : 0 < length) (who : Player) :
    quittingContinuationBestResponseValue reward (profile length) who =
      if who = 0 then (1 : ℝ)
      else if who = 1 then -1 + (2 : ℝ) / length else 0 := by
  fin_cases who
  · simpa using profile_bestResponse_zero length
  · simpa using profile_bestResponse_one length hlength
  · simpa using profile_bestResponse_dummy length hlength 2 (by norm_num)
  · simpa using profile_bestResponse_dummy length hlength 3 (by decide)

/-- Only player `0` has debt, equal to the probability penalty from tying
player `1` at one of the uniformly selected dates. -/
theorem profile_debt
    (length : ℕ) (hlength : 0 < length) (who : Player) :
    quittingTerminalDeviationDebt reward (profile length) who =
      if who = 0 then (2 : ℝ) / length else 0 := by
  unfold quittingTerminalDeviationDebt
  rw [profile_bestResponse length hlength who,
    congrFun (profile_payoff length hlength) who]
  fin_cases who <;> simp [value, hlength]
  all_goals ring

/-- The same-table global comparison has exact unrestricted exploitability
`2 / length`. -/
theorem profile_exploitability
    (length : ℕ) (hlength : 0 < length) :
    quittingTerminalSemanticExploitability
        (quittingTerminalSemanticPair reward (profile length)) =
      2 / length := by
  have herror : (0 : ℝ) ≤ 2 / length := by positivity
  apply le_antisymm
  · unfold quittingTerminalSemanticExploitability
    apply QuittingBoundaryHolonomy.finitePlayerMax_le
    intro who
    change max 0 (quittingTerminalDeviationDebt reward (profile length) who) ≤
      2 / length
    rw [profile_debt length hlength who]
    by_cases hwho : who = 0
    · rw [if_pos hwho, max_eq_right herror]
    · rw [if_neg hwho]
      simpa only [max_self] using herror
  · have hmax := QuittingBoundaryHolonomy.le_finitePlayerMax
      (fun who : Player ↦ max 0 (quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (profile length)) who))
      (0 : Player)
    change 2 / length ≤ quittingTerminalSemanticExploitability
      (quittingTerminalSemanticPair reward (profile length))
    rw [show quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (profile length)) 0 =
          quittingTerminalDeviationDebt reward (profile length) 0 by rfl,
      profile_debt length hlength 0, if_pos rfl, max_eq_right herror] at hmax
    exact hmax

/-- Exact executable exploitability of the comparison profile. -/
theorem profile_terminalExploitability
    (length : ℕ) (hlength : 0 < length) :
    quittingTerminalExploitability reward (profile length) = 2 / length := by
  rw [← quittingTerminalSemanticExploitability_pair]
  exact profile_exploitability length hlength

/-- Each comparison profile is terminal `2 / length`-Nash against all
behavioral deviations. -/
theorem profile_isTerminalNash
    (length : ℕ) (hlength : 0 < length) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ((2 : ℝ) / length) (profile length) := by
  intro who deviation
  have hbest := quittingTerminalPayoff_update_le_continuationBestResponseValue
    reward (profile length) who deviation
  have hdebt := profile_debt length hlength who
  unfold quittingTerminalDeviationDebt at hdebt
  by_cases hwho : who = 0
  · rw [if_pos hwho] at hdebt
    linarith
  · rw [if_neg hwho] at hdebt
    have herror : (0 : ℝ) ≤ 2 / length := by positivity
    linarith

/-- The limiting payoff selected by the global comparison family. -/
def target : Payoff Player := fun who ↦
  if who = 0 then 1 else if who = 1 then -1 else 0

private theorem tendsto_two_div_succ_zero :
    Tendsto (fun index : ℕ ↦ (2 : ℝ) / (index + 1 : ℕ)) atTop (nhds 0) := by
  have hbase := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hscaled := hbase.const_mul 2
  simpa [div_eq_mul_inv, Nat.cast_add, Nat.cast_one, add_comm] using hscaled

/-- The global comparison error converges to zero as the fresh clock grows. -/
theorem tendsto_profile_exploitability_zero :
    Tendsto (fun index : ℕ ↦ quittingTerminalExploitability reward
      (profile (index + 1))) atTop (nhds 0) := by
  apply tendsto_two_div_succ_zero.congr'
  filter_upwards [] with index
  exact (profile_terminalExploitability (index + 1) (by omega)).symm

private theorem tendsto_profile_payoff_target :
    Tendsto (fun index : ℕ ↦
      quittingTerminalPayoff reward (profile (index + 1))) atTop
      (nhds target) := by
  rw [tendsto_pi_nhds]
  intro who
  fin_cases who
  · have hconst : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hlimit := hconst.sub tendsto_two_div_succ_zero
    simpa [profile_payoff, value, target, sub_eq_add_neg, add_comm] using hlimit
  · have hconst : Tendsto (fun _ : ℕ ↦ (-1 : ℝ)) atTop (nhds (-1)) :=
      tendsto_const_nhds
    have hlimit := hconst.add tendsto_two_div_succ_zero
    simpa [profile_payoff, value, target, sub_eq_add_neg, add_comm] using hlimit
  · simp [profile_payoff, value, target]
  · simp [profile_payoff, value, target]

/-- The global comparison selects an actual uniform-equilibrium payoff for
the same table whose fixed two-date prefix has a `1 / 4` repair barrier. -/
theorem target_isUniformEquilibriumPayoff :
    (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  let error : ℕ → ℝ := fun index ↦ (2 : ℝ) / (index + 1 : ℕ)
  let profiles : ℕ → (quittingGame reward).BehaviorProfile :=
    fun index ↦ profile (index + 1)
  have herror : Tendsto error atTop (nhds 0) := by
    simpa [error] using tendsto_two_div_succ_zero
  have hnash : ∀ index,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (error index) (profiles index) := by
    intro index
    simpa [error, profiles] using
      profile_isTerminalNash (index + 1) (by omega)
  have htarget : Tendsto
      (fun index ↦ quittingTerminalPayoff reward (profiles index)) atTop
      (nhds target) := by
    simpa [profiles] using tendsto_profile_payoff_target
  exact quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto
    reward target error profiles herror
      (Frequently.of_forall hnash) htarget

/-- The true executable terminal-exploitability infimum of this reward table
is zero, despite its positive fixed-prefix repair barrier. -/
theorem terminalExploitabilityInf_eq_zero :
    quittingTerminalExploitabilityInf reward = 0 := by
  apply le_antisymm
  · have hbound : ∀ index : ℕ,
        quittingTerminalExploitabilityInf reward ≤
          (2 : ℝ) / (index + 1 : ℕ) := by
      intro index
      exact (quittingTerminalExploitabilityInf_le reward (profile (index + 1))).trans_eq
        (profile_terminalExploitability (index + 1) (by omega))
    exact ge_of_tendsto' tendsto_two_div_succ_zero hbound
  · unfold quittingTerminalExploitabilityInf
    apply le_csInf
    · exact ⟨_, profile 1, rfl⟩
    · rintro error ⟨candidate, rfl⟩
      exact quittingTerminalExploitability_nonneg reward candidate

/-- On the literal fixed-prefix table, the global terminal-exploitability
infimum is zero, strictly below `1 / 4`, while every behavioral tail attached
behind the selected two-date prefix has repair value at least `1 / 4`. -/
theorem terminalExploitabilityInf_eq_zero_lt_quarter_le_tailRepairValue :
    quittingTerminalExploitabilityInf reward = 0 ∧
      quittingTerminalExploitabilityInf reward < (1 / 4 : ℝ) ∧
      (1 / 4 : ℝ) ≤
        QuittingBoundaryHolonomy.behavioralTailRepairValue reward
          (quittingFiniteBoundaryHolonomy reward
            FixedPrefixArbitraryTailBarrier.plan 0 1) := by
  refine ⟨terminalExploitabilityInf_eq_zero, ?_, ?_⟩
  · rw [terminalExploitabilityInf_eq_zero]
    norm_num
  · exact FixedPrefixArbitraryTailBarrier.quarter_le_behavioralTailRepairValue

/-- Fixed-prefix behavioral-tail repair is strictly incomplete on this table:
its best suffix attachment remains separated from the global profile infimum. -/
theorem terminalExploitabilityInf_lt_tailRepairValue :
    quittingTerminalExploitabilityInf reward <
      QuittingBoundaryHolonomy.behavioralTailRepairValue reward
        (quittingFiniteBoundaryHolonomy reward
          FixedPrefixArbitraryTailBarrier.plan 0 1) := by
  exact lt_of_lt_of_le
    terminalExploitabilityInf_eq_zero_lt_quarter_le_tailRepairValue.2.1
    terminalExploitabilityInf_eq_zero_lt_quarter_le_tailRepairValue.2.2

end FixedPrefixSameTableGlobalComparison
end GameTheory

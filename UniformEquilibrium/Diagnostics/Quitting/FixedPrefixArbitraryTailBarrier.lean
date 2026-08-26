/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.PMFProduct.FiniteFubini
import UniformEquilibrium.Quitting.Boundary.Holonomy.InfiniteBehavioralTailEvaluation
import UniformEquilibrium.Quitting.Paths.BehaviorStoppingLaw

/-!
# A fixed-prefix barrier against arbitrary behavioral tails

This module gives a normalized four-player regression for fixed-prefix tail
attachment.  After the specific two-date active prefix below, every behavioral
tail leaves terminal exploitability at least `1 / 4`.

The cap calculation uses late deterministic quit times.  The relevant stopping
atoms tend to zero, so the cap is exactly one; no maximizing quit time is
claimed to exist.

This file does not formalize the separate global comparison by freshly
reselected finite clocks.  In particular, the comparison family for the
different hard-deadline table is not evidence for that same-table claim.
-/

noncomputable section

namespace GameTheory
namespace FixedPrefixArbitraryTailBarrier

open Filter Math.Probability Math.ProbabilityMassFunction Math.PMFProduct

abbrev Player := Fin 4

/-- Player `0` gets `-1` exactly on collisions with player `1`; player `1` is
its zero-sum opponent.  Players `2` and `3` are strict Continue dummies. -/
def reward (terminal : {S : Finset Player // S.Nonempty})
    (who : Player) : ℝ :=
  if who = 0 then
    if 0 ∈ terminal.1 ∧ 1 ∈ terminal.1 then -1 else 1
  else if who = 1 then
    if 0 ∈ terminal.1 ∧ 1 ∈ terminal.1 then 1 else -1
  else if who ∈ terminal.1 then -1 else 0

theorem abs_reward_le_one (terminal : {S : Finset Player // S.Nonempty})
    (who : Player) : |reward terminal who| ≤ 1 := by
  fin_cases who <;> simp only [reward] <;> split_ifs <;> norm_num

private def quarterHazard : PMF Bool :=
  bernoulliBool (1 / 4) (by norm_num) (by norm_num)

private def thirdHazard : PMF Bool :=
  bernoulliBool (1 / 3) (by norm_num) (by norm_num)

/-- Both active players use probability `1/4` at the first prefix date. -/
def firstRoot : Player → PMF Bool := fun who ↦
  if who = 0 ∨ who = 1 then quarterHazard else PMF.pure false

/-- Conditional on joint active survival, both active players use probability
`1/3` at the second prefix date. -/
def secondRoot : Player → PMF Bool := fun who ↦
  if who = 0 ∨ who = 1 then thirdHazard else PMF.pure false

/-- The fixed two-date prefix.  Values after date one are irrelevant. -/
def plan (time : ℕ) : Player → PMF Bool :=
  if time = 0 then firstRoot else secondRoot

theorem firstRoot_successorValue_zero (tail : ℝ) :
    quittingRootSuccessorPayoff reward (fun _ ↦ tail) firstRoot 0 =
      5 / 16 + 9 / 16 * tail := by
  unfold quittingRootSuccessorPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  simp [firstRoot, quarterHazard, reward, quittingRootPayoff,
    quittingQuitters, Math.Probability.expect_eq_sum]
  ring

theorem secondRoot_successorValue_zero (tail : ℝ) :
    quittingRootSuccessorPayoff reward (fun _ ↦ tail) secondRoot 0 =
      1 / 3 + 4 / 9 * tail := by
  unfold quittingRootSuccessorPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  simp [secondRoot, thirdHazard, reward, quittingRootPayoff,
    quittingQuitters, Math.Probability.expect_eq_sum]
  ring

theorem fixedOpponentsQuitValue_zero
    (roots : ℕ → Player → PMF Bool) (time : ℕ) :
    quittingFixedOpponentsQuitValue reward roots 0 time =
      1 - 2 * (roots time 1 true).toReal := by
  unfold quittingFixedOpponentsQuitValue quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  simp [reward, quittingRootPayoff, quittingQuitters,
    Math.Probability.expect_eq_sum]
  have hone : (roots time 1 false).toReal +
      (roots time 1 true).toReal = 1 := by
    simpa [Fintype.sum_bool, add_comm] using
      pmf_toReal_sum_one (roots time 1)
  have htwo : (roots time 2 false).toReal +
      (roots time 2 true).toReal = 1 := by
    simpa [Fintype.sum_bool, add_comm] using
      pmf_toReal_sum_one (roots time 2)
  have hthree : (roots time 3 false).toReal +
      (roots time 3 true).toReal = 1 := by
    simpa [Fintype.sum_bool, add_comm] using
      pmf_toReal_sum_one (roots time 3)
  calc
    _ = ((roots time 1 false).toReal - (roots time 1 true).toReal) *
          ((roots time 2 false).toReal + (roots time 2 true).toReal) *
          ((roots time 3 false).toReal + (roots time 3 true).toReal) := by ring
    _ = (roots time 1 false).toReal - (roots time 1 true).toReal := by
      rw [htwo, hthree]
      ring
    _ = 1 - 2 * (roots time 1 true).toReal := by linarith

theorem fixedOpponentsContinueMass_zero_eq
    (roots : ℕ → Player → PMF Bool) (time : ℕ) :
    quittingFixedOpponentsContinueMass roots 0 time =
      (roots time 1 false).toReal * (roots time 2 false).toReal *
        (roots time 3 false).toReal := by
  unfold quittingFixedOpponentsContinueMass
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  simp [Fin.prod_univ_succ]
  ring

theorem fixedOpponentsContinueReward_zero
    (roots : ℕ → Player → PMF Bool) (time : ℕ) :
    quittingFixedOpponentsContinueReward reward roots 0 time =
      1 - quittingFixedOpponentsContinueMass roots 0 time := by
  unfold quittingFixedOpponentsContinueReward
    quittingRootAbsorbingContribution quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  simp [reward, quittingRootPayoff, quittingQuitters,
    Math.Probability.expect_eq_sum]
  have hone : (roots time 1 false).toReal +
      (roots time 1 true).toReal = 1 := by
    simpa [Fintype.sum_bool, add_comm] using
      pmf_toReal_sum_one (roots time 1)
  have htwo : (roots time 2 false).toReal +
      (roots time 2 true).toReal = 1 := by
    simpa [Fintype.sum_bool, add_comm] using
      pmf_toReal_sum_one (roots time 2)
  have hthree : (roots time 3 false).toReal +
      (roots time 3 true).toReal = 1 := by
    simpa [Fintype.sum_bool, add_comm] using
      pmf_toReal_sum_one (roots time 3)
  have hthree' : (roots time 3 true).toReal =
      1 - (roots time 3 false).toReal := by linarith
  have hmass := fixedOpponentsContinueMass_zero_eq roots time
  have hfull :
      (roots time 2 true).toReal *
            ((roots time 3 true).toReal + (roots time 3 false).toReal) +
          (roots time 2 false).toReal *
            ((roots time 3 true).toReal + (roots time 3 false).toReal) = 1 := by
    rw [add_comm (roots time 3 true).toReal, hthree]
    simpa [add_comm] using htwo
  have hproper :
      (roots time 2 true).toReal *
            ((roots time 3 true).toReal + (roots time 3 false).toReal) +
          (roots time 2 false).toReal * (roots time 3 true).toReal =
        1 - (roots time 2 false).toReal * (roots time 3 false).toReal := by
    calc
      _ = (roots time 2 true).toReal +
            (roots time 2 false).toReal * (roots time 3 true).toReal := by
        rw [add_comm (roots time 3 true).toReal, hthree]
        ring
      _ = ((roots time 2 true).toReal + (roots time 2 false).toReal) -
            (roots time 2 false).toReal * (roots time 3 false).toReal := by
        rw [hthree']
        ring
      _ = _ := by rw [add_comm, htwo]
  rw [hfull, hproper, hmass]
  calc
    _ = ((roots time 1 false).toReal + (roots time 1 true).toReal) -
          (roots time 1 false).toReal * (roots time 2 false).toReal *
            (roots time 3 false).toReal := by ring
    _ = _ := by rw [hone]

/-- Player `0`'s deterministic quit-time payoff is one minus twice the
probability that player `1` first collides with that quit time. -/
theorem pureTimeValue_zero_eq_one_sub_two_mul
    (roots : ℕ → Player → PMF Bool) (start fuel : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward roots 0
        (some (start + fuel)) start =
      1 - 2 * quittingOpponentSurvivalWeight roots 0 start fuel *
        (roots (start + fuel) 1 true).toReal := by
  induction fuel generalizing start with
  | zero =>
      simp only [Nat.add_zero]
      rw [quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents,
        fixedOpponentsQuitValue_zero]
      simp [quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      have hne : start ≠ start + (fuel + 1) := by omega
      unfold quittingRootSequencePureTimeTerminalValue
      rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman,
        quittingPureTimeHazard_some_of_ne hne]
      simp only [PMF.pure_apply,
        if_neg (by decide : (true : Bool) ≠ false), ENNReal.toReal_zero,
        if_true, ENNReal.toReal_one, zero_mul, one_mul]
      rw [fixedOpponentsContinueReward_zero]
      have hindex : start + (fuel + 1) = start + 1 + fuel := by omega
      have htail := ih (start + 1)
      rw [hindex]
      change 0 + (1 - quittingFixedOpponentsContinueMass roots 0 start +
          quittingFixedOpponentsContinueMass roots 0 start *
            quittingRootSequencePureTimeTerminalValue reward roots 0
              (some (start + 1 + fuel)) (start + 1)) = _
      rw [htail]
      rw [show fuel + 1 = fuel.succ by rfl,
        quittingOpponentSurvivalWeight_succ_left]
      ring

/-- The collision atom relevant to player `0`'s late deterministic quit
deviation vanishes.  It is dominated by player `1`'s own stopping-law atom. -/
theorem tendsto_collisionAtom_zero
    (roots : ℕ → Player → PMF Bool) :
    Tendsto (fun time ↦
        quittingOpponentSurvivalWeight roots 0 0 time *
          (roots time 1 true).toReal) atTop (nhds 0) := by
  let oneHazard : ℕ → PMF Bool := fun time ↦ roots time 1
  have hsurvival : ∀ time,
      quittingOpponentSurvivalWeight roots 0 0 time ≤
        quittingHazardSurvival oneHazard time := by
    intro time
    unfold quittingOpponentSurvivalWeight
    rw [quittingHazardSurvival_eq_prod]
    apply Finset.prod_le_prod
    · intro offset _
      simpa only [Nat.zero_add] using
        quittingFixedOpponentsContinueMass_nonneg roots 0 offset
    · intro offset _
      simp only [Nat.zero_add]
      rw [fixedOpponentsContinueMass_zero_eq]
      have htwo0 := quittingHazard_continue_nonneg
        (fun time ↦ roots time 2) offset
      have htwo1 := quittingHazard_continue_le_one
        (fun time ↦ roots time 2) offset
      have hthree0 := quittingHazard_continue_nonneg
        (fun time ↦ roots time 3) offset
      have hthree1 := quittingHazard_continue_le_one
        (fun time ↦ roots time 3) offset
      have hone0 := quittingHazard_continue_nonneg oneHazard offset
      have htwothree : (roots offset 2 false).toReal *
          (roots offset 3 false).toReal ≤ 1 :=
        mul_le_one₀ htwo1 hthree0 hthree1
      change (oneHazard offset false).toReal *
          (roots offset 2 false).toReal * (roots offset 3 false).toReal ≤
        (oneHazard offset false).toReal
      calc
        _ = (oneHazard offset false).toReal *
              ((roots offset 2 false).toReal *
                (roots offset 3 false).toReal) := by ring
        _ ≤ (oneHazard offset false).toReal * 1 :=
          mul_le_mul_of_nonneg_left htwothree hone0
        _ = _ := by ring
  have hdominated : ∀ time,
      0 ≤ quittingOpponentSurvivalWeight roots 0 0 time *
          (roots time 1 true).toReal ∧
      quittingOpponentSurvivalWeight roots 0 0 time *
          (roots time 1 true).toReal ≤
        quittingHazardStopMass oneHazard time := by
    intro time
    have hquit0 := quittingHazard_quit_nonneg oneHazard time
    constructor
    · exact mul_nonneg (quittingOpponentSurvivalWeight_nonneg roots 0 0 time)
        hquit0
    · rw [quittingHazardStopMass_eq_survival_mul_stop]
      exact mul_le_mul_of_nonneg_right (hsurvival time) hquit0
  apply squeeze_zero' (g := quittingHazardStopMass oneHazard)
  · exact Eventually.of_forall fun time ↦ (hdominated time).1
  · exact Eventually.of_forall fun time ↦ (hdominated time).2
  · exact tendsto_quittingHazardStopMass_zero oneHazard

/-- Player `0`'s unrestricted behavioral best-response cap against any root
sequence is exactly one.  Late pure quit times approach one; they need not
attain it. -/
theorem rootSequenceBestResponseValue_zero_eq_one
    (roots : ℕ → Player → PMF Bool) :
    quittingRootSequenceBestResponseValue reward roots 0 = 1 := by
  let profile := quittingRootSequenceProfile reward roots 0
  apply le_antisymm
  · change quittingContinuationBestResponseValue reward profile 0 ≤ 1
    exact (le_abs_self _).trans
      (abs_quittingContinuationBestResponseValue_le reward profile 0
        abs_reward_le_one)
  · have hlimit : Tendsto (fun time ↦
        quittingRootSequencePureTimeTerminalValue reward roots 0
          (some time) 0) atTop (nhds 1) := by
      have hcollision := tendsto_collisionAtom_zero roots
      have hscaled : Tendsto (fun time ↦
          2 * (quittingOpponentSurvivalWeight roots 0 0 time *
            (roots time 1 true).toReal)) atTop (nhds 0) := by
        simpa using hcollision.const_mul 2
      have hsub : Tendsto (fun time ↦
          1 - 2 * (quittingOpponentSurvivalWeight roots 0 0 time *
            (roots time 1 true).toReal)) atTop (nhds 1) :=
        by simpa using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop
            (nhds 1)).sub hscaled
      convert hsub using 1
      funext time
      have hformula := pureTimeValue_zero_eq_one_sub_two_mul roots 0 time
      simpa only [Nat.zero_add, mul_assoc] using hformula
    apply le_of_tendsto' hlimit
    intro time
    change quittingRootSequencePureTimeTerminalValue reward roots 0
        (some time) 0 ≤ quittingContinuationBestResponseValue reward profile 0
    unfold quittingContinuationBestResponseValue
    have hle := le_csSup
      (bddAbove_range_quittingTerminalPayoff_update reward profile 0)
      (show quittingTerminalPayoff reward
          (Function.update profile 0
            (quittingPureTimeBehaviorStrategy reward 0 (some time))) 0 ∈
          Set.range fun deviation : (quittingGame reward).BehaviorStrategy 0 ↦
            quittingTerminalPayoff reward
              (Function.update profile 0 deviation) 0 from
        ⟨quittingPureTimeBehaviorStrategy reward 0 (some time), rfl⟩)
    rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
      quittingProfileLiveRoot_quittingRootSequenceProfile_zero] at hle
    exact hle

/-- The exact prescribed payoff after the fixed prefix.  The suffix enters
only through player `0`'s own conditional payoff `g`, with joint prefix reach
`1 / 4`. -/
theorem phaseSwitch_terminalPayoff_zero
    (punish : ℕ → Player → PMF Bool) :
    quittingTerminalPayoff reward
        (quittingPhaseSwitchProfile reward plan punish 2) 0 =
      1 / 2 + 1 / 4 *
        quittingRootSequenceTerminalValue reward punish 0 0 := by
  rw [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
    quittingProfileLiveRoot_quittingPhaseSwitchProfile]
  let phase := quittingPhaseSwitchRoots plan punish 2
  have hzero : phase 0 = firstRoot := by
    rw [show phase 0 = plan 0 by
      exact quittingPhaseSwitchRoots_of_lt plan punish (by omega)]
    simp [plan]
  have hone : phase 1 = secondRoot := by
    rw [show phase 1 = plan 1 by
      exact quittingPhaseSwitchRoots_of_lt plan punish (by omega)]
    simp [plan]
  have htwo : quittingRootSequenceTerminalValue reward phase 0 2 =
      quittingRootSequenceTerminalValue reward punish 0 0 := by
    exact quittingRootSequenceTerminalValue_quittingPhaseSwitchRoots_switch
      reward plan punish 2 0
  change quittingRootSequenceTerminalValue reward phase 0 0 = _
  rw [quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff,
    hzero, firstRoot_successorValue_zero]
  rw [quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff,
    hone, secondRoot_successorValue_zero, htwo]
  ring

/-- Consequently player `0`'s prescribed payoff lies in the exact interval
`[1 / 4, 3 / 4]`, for every behavioral suffix. -/
theorem phaseSwitch_terminalPayoff_zero_mem_Icc
    (punish : ℕ → Player → PMF Bool) :
    quittingTerminalPayoff reward
        (quittingPhaseSwitchProfile reward plan punish 2) 0 ∈
      Set.Icc (1 / 4) (3 / 4) := by
  have hg := abs_quittingRootSequenceTerminalValue_le reward punish 0 0
    (by norm_num : (0 : ℝ) ≤ 1) abs_reward_le_one
  rw [phaseSwitch_terminalPayoff_zero]
  constructor <;> rw [abs_le] at hg <;> linarith

/-- The exact all-behavior cap of player `0` after the fixed prefix. -/
theorem phaseSwitch_bestResponseValue_zero_eq_one
    (punish : ℕ → Player → PMF Bool) :
    quittingContinuationBestResponseValue reward
        (quittingPhaseSwitchProfile reward plan punish 2) 0 = 1 := by
  change quittingRootSequenceBestResponseValue reward
    (quittingPhaseSwitchRoots plan punish 2) 0 = 1
  exact rootSequenceBestResponseValue_zero_eq_one _

/-- Every behavioral suffix leaves literal all-behavior terminal
exploitability at least `1 / 4` after the fixed prefix. -/
theorem quarter_le_phaseSwitch_terminalExploitability
    (punish : ℕ → Player → PMF Bool) :
    1 / 4 ≤ quittingTerminalExploitability reward
      (quittingPhaseSwitchProfile reward plan punish 2) := by
  let profile := quittingPhaseSwitchProfile reward plan punish 2
  have hcap : quittingContinuationBestResponseValue reward profile 0 = 1 := by
    exact phaseSwitch_bestResponseValue_zero_eq_one punish
  have hg : quittingRootSequenceTerminalValue reward punish 0 0 ≤ 1 :=
    (le_abs_self _).trans
      (abs_quittingRootSequenceTerminalValue_le reward punish 0 0
        (by norm_num) abs_reward_le_one)
  have hgain : 1 / 4 ≤
      max 0 (quittingContinuationBestResponseValue reward profile 0 -
        quittingTerminalPayoff reward profile 0) := by
    rw [hcap, phaseSwitch_terminalPayoff_zero]
    exact (show 1 / 4 ≤ 1 -
        (1 / 2 + 1 / 4 *
          quittingRootSequenceTerminalValue reward punish 0 0) by
      linarith).trans (le_max_right _ _)
  exact hgain.trans
    (QuittingBoundaryHolonomy.le_finitePlayerMax
      (fun who ↦ max 0
        (quittingContinuationBestResponseValue reward profile who -
          quittingTerminalPayoff reward profile who)) 0)

/-- The fixed prefix's all-tail repair value is at least `1 / 4`.  This is an
infimum over every behavioral suffix, not merely finite-support tails. -/
theorem quarter_le_behavioralTailRepairValue :
    1 / 4 ≤ QuittingBoundaryHolonomy.behavioralTailRepairValue reward
      (quittingFiniteBoundaryHolonomy reward plan 0 1) := by
  rw [behavioralTailRepairValue_eq_sInf_phaseSwitch_terminalExploitability
    reward plan 2 (by omega)]
  apply le_csInf (Set.range_nonempty _)
  rintro value ⟨punish, rfl⟩
  exact quarter_le_phaseSwitch_terminalExploitability punish

end FixedPrefixArbitraryTailBarrier
end GameTheory

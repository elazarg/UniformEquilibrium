/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Paths.SixPlayerOnePairMassTargetLock
import UniformEquilibrium.Quitting.Chronology.TwoPairClockBoundary
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauIncidence
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauLocalizedOtherDefect

/-!
# Actual-profile clock adapter for the six-player target ledger

This module constructs the two-pair square-root clock from the literal live
roots of an arbitrary behavioral profile.  It identifies both squared target
amplitudes with the actual chronological target atoms and then with the
terminal outcome law.  No equilibrium hypothesis is used.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction Math.PMFProduct
open scoped Topology

namespace SixPlayerOnePair

/-- The four named target roles in the six-player table. -/
def twoPairGateRoles : QuittingTwoPairGateRoles SixPlayer where
  firstA := player1
  secondA := player2
  firstB := player3
  secondB := player4
  firstA_ne_secondA := by decide
  firstB_ne_secondB := by decide
  pairs_disjoint := by decide

/-- The square-root clock read from the actual live rows of one arbitrary
behavioral profile.  The last two players enter through the background
Continue amplitude. -/
def profileTwoPairHazardClock
    (reward : {S : Finset SixPlayer // S.Nonempty} → Payoff SixPlayer)
    (profile : (quittingGame reward).BehaviorProfile) :
    TwoPairHazardClock where
  first time := QuittingTwoPairGateRoles.rootSequenceHazard
    (quittingProfileLiveRoot reward profile) time player1
  second time := QuittingTwoPairGateRoles.rootSequenceHazard
    (quittingProfileLiveRoot reward profile) time player2
  third time := QuittingTwoPairGateRoles.rootSequenceHazard
    (quittingProfileLiveRoot reward profile) time player3
  fourth time := QuittingTwoPairGateRoles.rootSequenceHazard
    (quittingProfileLiveRoot reward profile) time player4
  background time := Real.sqrt
    ((1 - QuittingTwoPairGateRoles.rootSequenceHazard
        (quittingProfileLiveRoot reward profile) time player5) *
      (1 - QuittingTwoPairGateRoles.rootSequenceHazard
        (quittingProfileLiveRoot reward profile) time player6))
  survivalRoot time := Real.sqrt (quittingJointSurvivalWeight
    (quittingProfileLiveRoot reward profile) 0 time)
  first_mem time := QuittingTwoPairGateRoles.rootSequenceHazard_mem_Icc _ _ _
  second_mem time := QuittingTwoPairGateRoles.rootSequenceHazard_mem_Icc _ _ _
  third_mem time := QuittingTwoPairGateRoles.rootSequenceHazard_mem_Icc _ _ _
  fourth_mem time := QuittingTwoPairGateRoles.rootSequenceHazard_mem_Icc _ _ _
  background_mem time := by
    let roots := quittingProfileLiveRoot reward profile
    let fifth := QuittingTwoPairGateRoles.rootSequenceHazard roots time player5
    let sixth := QuittingTwoPairGateRoles.rootSequenceHazard roots time player6
    have hfifth := QuittingTwoPairGateRoles.rootSequenceHazard_mem_Icc
      roots time player5
    have hsixth := QuittingTwoPairGateRoles.rootSequenceHazard_mem_Icc
      roots time player6
    have hfifth' : fifth ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [fifth] using hfifth
    have hsixth' : sixth ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [sixth] using hsixth
    have hproduct : 0 ≤ (1 - fifth) * (1 - sixth) := by
      exact mul_nonneg (by linarith [hfifth'.2]) (by linarith [hsixth'.2])
    have hproductLe : (1 - fifth) * (1 - sixth) ≤ 1 := by
      calc
        (1 - fifth) * (1 - sixth) ≤ 1 * (1 - sixth) := by
          apply mul_le_mul_of_nonneg_right
          · linarith [hfifth'.1]
          · linarith [hsixth'.2]
        _ ≤ 1 := by linarith [hsixth'.1]
    constructor
    · exact Real.sqrt_nonneg _
    · nlinarith [Real.sq_sqrt hproduct]
  survivalRoot_nonneg time := Real.sqrt_nonneg _
  survivalRoot_zero := by
    simp [quittingJointSurvivalWeight, quittingFiniteContinueWeight]
  survivalRoot_step time := by
    let roots := quittingProfileLiveRoot reward profile
    let q1 := QuittingTwoPairGateRoles.rootSequenceHazard roots time player1
    let q2 := QuittingTwoPairGateRoles.rootSequenceHazard roots time player2
    let q3 := QuittingTwoPairGateRoles.rootSequenceHazard roots time player3
    let q4 := QuittingTwoPairGateRoles.rootSequenceHazard roots time player4
    let q5 := QuittingTwoPairGateRoles.rootSequenceHazard roots time player5
    let q6 := QuittingTwoPairGateRoles.rootSequenceHazard roots time player6
    have hsurvival := quittingJointSurvivalWeight_nonneg roots 0 time
    have hq1 := QuittingTwoPairGateRoles.rootSequenceHazard_mem_Icc roots time player1
    have hq2 := QuittingTwoPairGateRoles.rootSequenceHazard_mem_Icc roots time player2
    have hq3 := QuittingTwoPairGateRoles.rootSequenceHazard_mem_Icc roots time player3
    have hq4 := QuittingTwoPairGateRoles.rootSequenceHazard_mem_Icc roots time player4
    have hq5 := QuittingTwoPairGateRoles.rootSequenceHazard_mem_Icc roots time player5
    have hq6 := QuittingTwoPairGateRoles.rootSequenceHazard_mem_Icc roots time player6
    have hcontinue (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ 1 - q := by
      linarith [hq.2]
    change Real.sqrt (quittingJointSurvivalWeight roots 0 (time + 1)) =
      Real.sqrt (quittingJointSurvivalWeight roots 0 time) *
        Real.sqrt ((1 - q5) * (1 - q6)) *
          pairContinueAmplitude q1 q2 * pairContinueAmplitude q3 q4
    rw [quittingJointSurvivalWeight_succ]
    simp only [Nat.zero_add]
    rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    have hproduct :
        (∏ who : SixPlayer, (roots time who false).toReal) =
          (1 - q1) * (1 - q2) * (1 - q3) * (1 - q4) *
            (1 - q5) * (1 - q6) := by
      simp [q1, q2, q3, q4, q5, q6,
        QuittingTwoPairGateRoles.rootSequenceHazard,
        player1, player2, player3, player4, player5, player6,
        pmfBool_false_toReal, Fin.prod_univ_succ]
      ring
    rw [hproduct]
    unfold pairContinueAmplitude
    rw [Real.sqrt_mul hsurvival]
    rw [show (1 - q1) * (1 - q2) * (1 - q3) * (1 - q4) *
        (1 - q5) * (1 - q6) =
          ((1 - q5) * (1 - q6)) * ((1 - q1) * (1 - q2)) *
            ((1 - q3) * (1 - q4)) by ring]
    rw [Real.sqrt_mul (mul_nonneg
      (mul_nonneg (hcontinue q5 hq5) (hcontinue q6 hq6))
      (mul_nonneg (hcontinue q1 hq1) (hcontinue q2 hq2)))]
    rw [Real.sqrt_mul (mul_nonneg (hcontinue q5 hq5)
      (hcontinue q6 hq6))]
    ring

theorem profileTwoPairHazardClock_firstTargetAmplitude_sq
    (reward : {S : Finset SixPlayer // S.Nonempty} → Payoff SixPlayer)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    (profileTwoPairHazardClock reward profile).firstTargetAmplitude time ^ 2 =
      QuittingTwoPairGateRoles.rootSequenceStageCoalitionMass
        (quittingProfileLiveRoot reward profile) time targetA := by
  let roots := quittingProfileLiveRoot reward profile
  let q1 := QuittingTwoPairGateRoles.rootSequenceHazard roots time player1
  let q2 := QuittingTwoPairGateRoles.rootSequenceHazard roots time player2
  let q3 := QuittingTwoPairGateRoles.rootSequenceHazard roots time player3
  let q4 := QuittingTwoPairGateRoles.rootSequenceHazard roots time player4
  let q5 := QuittingTwoPairGateRoles.rootSequenceHazard roots time player5
  let q6 := QuittingTwoPairGateRoles.rootSequenceHazard roots time player6
  have hsurvival := quittingJointSurvivalWeight_nonneg roots 0 time
  have hq1 := QuittingTwoPairGateRoles.rootSequenceHazard_mem_Icc roots time player1
  have hq2 := QuittingTwoPairGateRoles.rootSequenceHazard_mem_Icc roots time player2
  have hq3 := QuittingTwoPairGateRoles.rootSequenceHazard_mem_Icc roots time player3
  have hq4 := QuittingTwoPairGateRoles.rootSequenceHazard_mem_Icc roots time player4
  have hq5 := QuittingTwoPairGateRoles.rootSequenceHazard_mem_Icc roots time player5
  have hq6 := QuittingTwoPairGateRoles.rootSequenceHazard_mem_Icc roots time player6
  have hcontinue (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ 1 - q := by
    linarith [hq.2]
  change (Real.sqrt (quittingJointSurvivalWeight roots 0 time) *
      Real.sqrt ((1 - q5) * (1 - q6)) * Real.sqrt (q1 * q2) *
        Real.sqrt ((1 - q3) * (1 - q4))) ^ 2 = _
  rw [show QuittingTwoPairGateRoles.rootSequenceStageCoalitionMass
      roots time targetA = quittingJointSurvivalWeight roots 0 time *
        (q1 * q2 * (1 - q3) * (1 - q4) * (1 - q5) * (1 - q6)) by
    unfold QuittingTwoPairGateRoles.rootSequenceStageCoalitionMass
      quittingRootCoalitionMass quittingRootQuitRates coalitionMass
    rw [show targetAᶜ =
      ({player3, player4, player5, player6} : Finset SixPlayer) by decide]
    simp [targetA, player1, player2, player3, player4, player5, player6,
      q1, q2, q3, q4, q5, q6,
      QuittingTwoPairGateRoles.rootSequenceHazard]
    ring_nf
    simp]
  rw [mul_pow, mul_pow, mul_pow]
  rw [Real.sq_sqrt hsurvival]
  rw [Real.sq_sqrt (mul_nonneg (hcontinue q5 hq5) (hcontinue q6 hq6))]
  rw [Real.sq_sqrt (mul_nonneg hq1.1 hq2.1)]
  rw [Real.sq_sqrt (mul_nonneg (hcontinue q3 hq3) (hcontinue q4 hq4))]
  ring

theorem profileTwoPairHazardClock_secondTargetAmplitude_sq
    (reward : {S : Finset SixPlayer // S.Nonempty} → Payoff SixPlayer)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    (profileTwoPairHazardClock reward profile).secondTargetAmplitude time ^ 2 =
      QuittingTwoPairGateRoles.rootSequenceStageCoalitionMass
        (quittingProfileLiveRoot reward profile) time targetB := by
  let roots := quittingProfileLiveRoot reward profile
  let q1 := QuittingTwoPairGateRoles.rootSequenceHazard roots time player1
  let q2 := QuittingTwoPairGateRoles.rootSequenceHazard roots time player2
  let q3 := QuittingTwoPairGateRoles.rootSequenceHazard roots time player3
  let q4 := QuittingTwoPairGateRoles.rootSequenceHazard roots time player4
  let q5 := QuittingTwoPairGateRoles.rootSequenceHazard roots time player5
  let q6 := QuittingTwoPairGateRoles.rootSequenceHazard roots time player6
  have hsurvival := quittingJointSurvivalWeight_nonneg roots 0 time
  have hq1 := QuittingTwoPairGateRoles.rootSequenceHazard_mem_Icc roots time player1
  have hq2 := QuittingTwoPairGateRoles.rootSequenceHazard_mem_Icc roots time player2
  have hq3 := QuittingTwoPairGateRoles.rootSequenceHazard_mem_Icc roots time player3
  have hq4 := QuittingTwoPairGateRoles.rootSequenceHazard_mem_Icc roots time player4
  have hq5 := QuittingTwoPairGateRoles.rootSequenceHazard_mem_Icc roots time player5
  have hq6 := QuittingTwoPairGateRoles.rootSequenceHazard_mem_Icc roots time player6
  have hcontinue (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ 1 - q := by
    linarith [hq.2]
  change (Real.sqrt (quittingJointSurvivalWeight roots 0 time) *
      Real.sqrt ((1 - q5) * (1 - q6)) * Real.sqrt ((1 - q1) * (1 - q2)) *
        Real.sqrt (q3 * q4)) ^ 2 = _
  rw [show QuittingTwoPairGateRoles.rootSequenceStageCoalitionMass
      roots time targetB = quittingJointSurvivalWeight roots 0 time *
        ((1 - q1) * (1 - q2) * q3 * q4 * (1 - q5) * (1 - q6)) by
    unfold QuittingTwoPairGateRoles.rootSequenceStageCoalitionMass
      quittingRootCoalitionMass quittingRootQuitRates coalitionMass
    rw [show targetBᶜ =
      ({player1, player2, player5, player6} : Finset SixPlayer) by decide]
    simp [targetB, player1, player2, player3, player4, player5, player6,
      q1, q2, q3, q4, q5, q6,
      QuittingTwoPairGateRoles.rootSequenceHazard]
    ring_nf
    simp]
  rw [mul_pow, mul_pow, mul_pow]
  rw [Real.sq_sqrt hsurvival]
  rw [Real.sq_sqrt (mul_nonneg (hcontinue q5 hq5) (hcontinue q6 hq6))]
  rw [Real.sq_sqrt (mul_nonneg (hcontinue q1 hq1) (hcontinue q2 hq2))]
  rw [Real.sq_sqrt (mul_nonneg hq3.1 hq4.1)]
  ring

/-- Every actual behavioral profile satisfies the sharp square-root budget for
the two displayed terminal target atoms at the root-sequence level. -/
theorem sqrt_rootSequenceTargetMass_add_sqrt_rootSequenceTargetMass_le_one
    (reward : {S : Finset SixPlayer // S.Nonempty} → Payoff SixPlayer)
    (profile : (quittingGame reward).BehaviorProfile) :
    Real.sqrt (QuittingTwoPairGateRoles.rootSequenceTerminalCoalitionMass
        (quittingProfileLiveRoot reward profile) targetA) +
      Real.sqrt (QuittingTwoPairGateRoles.rootSequenceTerminalCoalitionMass
        (quittingProfileLiveRoot reward profile) targetB) ≤ 1 := by
  let roots := quittingProfileLiveRoot reward profile
  let clock := profileTwoPairHazardClock reward profile
  have hfirstSummable :=
    QuittingTwoPairGateRoles.summable_rootSequenceStageCoalitionMass
      roots targetA targetA_nonempty
  have hsecondSummable :=
    QuittingTwoPairGateRoles.summable_rootSequenceStageCoalitionMass
      roots targetB (by simp [targetB])
  have hfirst : Tendsto (fun horizon => Real.sqrt
      (∑ time ∈ Finset.range horizon,
        QuittingTwoPairGateRoles.rootSequenceStageCoalitionMass
          roots time targetA)) atTop
      (nhds (Real.sqrt
        (QuittingTwoPairGateRoles.rootSequenceTerminalCoalitionMass
          roots targetA))) := by
    apply Real.continuous_sqrt.continuousAt.tendsto.comp
    exact hfirstSummable.hasSum.tendsto_sum_nat
  have hsecond : Tendsto (fun horizon => Real.sqrt
      (∑ time ∈ Finset.range horizon,
        QuittingTwoPairGateRoles.rootSequenceStageCoalitionMass
          roots time targetB)) atTop
      (nhds (Real.sqrt
        (QuittingTwoPairGateRoles.rootSequenceTerminalCoalitionMass
          roots targetB))) := by
    apply Real.continuous_sqrt.continuousAt.tendsto.comp
    exact hsecondSummable.hasSum.tendsto_sum_nat
  apply le_of_tendsto' (hfirst.add hsecond)
  intro horizon
  simpa only [clock, roots, profileTwoPairHazardClock_firstTargetAmplitude_sq,
    profileTwoPairHazardClock_secondTargetAmplitude_sq] using
      clock.finite_targetMass_sqrt_sum_le_one horizon

private theorem exactCoalitionMass_eq_apply_some
    (mass : CoalitionOutcome SixPlayer → ℝ) (target : Finset SixPlayer)
    (htarget : target.Nonempty) :
    exactCoalitionMass mass target = mass (some ⟨target, htarget⟩) := by
  classical
  unfold exactCoalitionMass coalitionEventMass
  rw [Fintype.sum_option]
  have hempty : ¬ (∅ : Finset SixPlayer) = target := by
    exact fun h => htarget.ne_empty h.symm
  have hiff : ∀ terminal : {S : Finset SixPlayer // S.Nonempty},
      terminal.val = target ↔ terminal = ⟨target, htarget⟩ := by
    intro terminal
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg Subtype.val h
  simp only [CoalitionOutcome.coalition, hempty, if_false, zero_add, hiff]
  exact Fintype.sum_ite_eq'
    (⟨target, htarget⟩ : {S : Finset SixPlayer // S.Nonempty})
    (fun terminal => mass (some terminal))

/-- The chronological coalition mass of the actual live roots is exactly the
corresponding atom of the behavioral profile's terminal outcome law. -/
theorem rootSequenceTerminalCoalitionMass_profileLiveRoot_eq_exactCoalitionMass
    (reward : {S : Finset SixPlayer // S.Nonempty} → Payoff SixPlayer)
    (profile : (quittingGame reward).BehaviorProfile)
    (target : Finset SixPlayer) (htarget : target.Nonempty) :
    QuittingTwoPairGateRoles.rootSequenceTerminalCoalitionMass
        (quittingProfileLiveRoot reward profile) target =
      exactCoalitionMass (quittingTerminalOutcomeMass reward profile) target := by
  rw [exactCoalitionMass_eq_apply_some]
  rw [quittingTerminalOutcomeMass_eq_timeDisintegration]
  unfold QuittingTwoPairGateRoles.rootSequenceTerminalCoalitionMass
  apply tsum_congr
  intro time
  unfold QuittingTwoPairGateRoles.rootSequenceStageCoalitionMass
  rw [← quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot reward profile time]
  rw [← quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass
    reward profile time ⟨target, htarget⟩]

/-- The two literal terminal pair masses of every behavioral profile satisfy
the square-root budget.  This is the actual-profile adapter missing from the
six-player target-lock packet. -/
theorem sqrt_firstPairMass_add_sqrt_secondPairMass_le_one
    (reward : {S : Finset SixPlayer // S.Nonempty} → Payoff SixPlayer)
    (profile : (quittingGame reward).BehaviorProfile) :
    Real.sqrt (firstPairMass reward profile) +
      Real.sqrt (secondPairMass reward profile) ≤ 1 := by
  rw [firstPairMass, secondPairMass]
  rw [← rootSequenceTerminalCoalitionMass_profileLiveRoot_eq_exactCoalitionMass
    reward profile targetA targetA_nonempty]
  rw [← rootSequenceTerminalCoalitionMass_profileLiveRoot_eq_exactCoalitionMass
    reward profile targetB (by simp [targetB])]
  exact sqrt_rootSequenceTargetMass_add_sqrt_rootSequenceTargetMass_le_one
    reward profile

/-- The conditional second-pair estimate from the six-player ledger is
unconditional for actual behavioral profiles. -/
theorem integerReward_secondPairMass_le
    (profile : (quittingGame integerReward).BehaviorProfile)
    {epsilon : ℝ}
    (hexploit : quittingTerminalExploitability integerReward profile ≤ epsilon)
    (hepsilon : epsilon < 31 / 66) :
    secondPairMass integerReward profile ≤
      (66 * epsilon / 31) ^ 2 /
        (4 * (1 - 66 * epsilon / 31)) := by
  exact integerReward_secondPairMass_le_of_clock profile hexploit hepsilon
    (sqrt_firstPairMass_add_sqrt_secondPairMass_le_one integerReward profile)

/-- At terminal exploitability at most one tenth, the second displayed pair
has the advertised small mass for every actual behavioral profile. -/
theorem integerReward_one_tenth_secondPairMass_le_actualProfile
    (profile : (quittingGame integerReward).BehaviorProfile)
    (hexploit : quittingTerminalExploitability integerReward profile ≤ 1 / 10) :
    secondPairMass integerReward profile ≤ 1089 / 75640 := by
  exact SixPlayerOnePair.integerReward_one_tenth_secondPairMass_le profile
    hexploit
    (sqrt_firstPairMass_add_sqrt_secondPairMass_le_one integerReward profile)

end SixPlayerOnePair

end GameTheory

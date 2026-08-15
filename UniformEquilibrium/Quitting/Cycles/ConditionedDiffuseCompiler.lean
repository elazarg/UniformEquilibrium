/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseStrategicRescaling
import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseLawComparison
import UniformEquilibrium.Quitting.Paths.JointPolicySeparatedErrorCompiler
import UniformEquilibrium.Quitting.Bellman.Finite.BooleanMobiusAdapter
import UniformEquilibrium.Quitting.Projective.AnalyticPacket

/-!
# Strategic compiler for the tight diffuse conditioned branch

The finite coalition-law comparisons are provided by
`ConditionedDiffuseLawComparison`.  This module assembles those comparisons
with strategic estimates into policy and equilibrium conclusions.  Boundary
tightness is explicit; no assertion is made on a strict phantom-boundary
coordinate.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

theorem conditionedSourceContinueBase_le_conditionedValue_sub_phantom
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    (time : ℕ) (who : ι)
    (hcurrent : 0 < quittingTailEventualAbsorption roots time)
    (hnext : 0 < quittingTailEventualAbsorption roots (time + 1)) :
    quittingStationaryFixedOpponentsContinueReward reward (roots time) who /
          quittingTailEventualAbsorption roots time +
        quittingStationaryFixedOpponentsContinueMass (roots time) who *
          quittingTailEventualAbsorption roots (time + 1) /
          quittingTailEventualAbsorption roots time *
          quittingTailConditionedValue roots value boundary (time + 1) who ≤
      quittingTailConditionedValue roots value boundary time who -
        quittingStationaryFixedOpponentsContinueMass (roots time) who *
          quittingTailDiffuseRescaledHazard roots time who *
          quittingJointSurvivalLimit roots (time + 1) * boundary who := by
  have hnashRoot :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward (value (time + 1)) (roots time)).1 (hnash time)
  have hcontinue :=
    quittingRootContinuePayoff_le_successor_of_isZeroNash
      reward (value (time + 1)) (roots time) who hnashRoot
  rw [quittingRootContinuePayoff_eq_fixedOpponents
    reward roots who (value (time + 1)) time] at hcontinue
  rw [← congrFun (hpolicy time) who] at hcontinue
  have hsurvival := quittingJointSurvivalLimit_eq_continue_mul_succ roots time
  have hcontinueMass :
      quittingStationaryContinueMass (roots time) =
        quittingStationaryFixedOpponentsContinueMass (roots time) who *
          (roots time who false).toReal :=
    quittingStationaryContinueMass_eq_forcedContinue_mul_own
      (roots time) who
  have hown : (roots time who false).toReal =
      1 - (roots time who true).toReal := by
    linarith [quittingRoot_continueProbability_add_quitProbability
      (roots time) who]
  have hscaled : (roots time who true).toReal =
      quittingTailEventualAbsorption roots time *
        quittingTailDiffuseRescaledHazard roots time who := by
    unfold quittingTailDiffuseRescaledHazard
    field_simp [hcurrent.ne']
  let sourceContinue :=
    quittingStationaryFixedOpponentsContinueMass (roots time) who
  let sourceReward :=
    quittingStationaryFixedOpponentsContinueReward reward (roots time) who
  let eventual := quittingTailEventualAbsorption roots time
  let phantom := quittingJointSurvivalLimit roots (time + 1)
  let ownScaled := quittingTailDiffuseRescaledHazard roots time who
  have hcontinue' : sourceReward + sourceContinue * value (time + 1) who ≤
      value time who := by
    simpa [sourceReward, sourceContinue,
      quittingStationaryFixedOpponentsContinueReward,
      quittingStationaryFixedOpponentsContinueMass] using hcontinue
  calc
    sourceReward / eventual +
          sourceContinue * quittingTailEventualAbsorption roots (time + 1) /
            eventual *
            quittingTailConditionedValue roots value boundary (time + 1) who =
        (sourceReward + sourceContinue * value (time + 1) who -
          sourceContinue * phantom * boundary who) / eventual := by
      unfold quittingTailConditionedValue
      dsimp only [eventual, phantom]
      field_simp [hcurrent.ne', hnext.ne']
      ring
    _ ≤ (value time who - sourceContinue * phantom * boundary who) /
        eventual := by
      exact div_le_div_of_nonneg_right (by linarith) hcurrent.le
    _ = quittingTailConditionedValue roots value boundary time who -
        sourceContinue * ownScaled * phantom * boundary who := by
      unfold quittingTailConditionedValue
      dsimp only [eventual, phantom, sourceContinue, ownScaled]
      rw [hsurvival, hcontinueMass, hown, hscaled]
      field_simp [hcurrent.ne']
      ring

/-- **Deleted-clock Continue estimate.**  On the singleton-tight diffuse
stratum, the rescaled Continue endpoint has only collision-order error plus
the explicitly controlled phantom own-clock term. -/
theorem rescaledContinuePayoff_le_conditionedValue_add_deletedCharge
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    (time : ℕ) (who : ι) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hconditionedBound :
      |quittingTailConditionedValue roots value boundary (time + 1) who| ≤ M)
    (hcurrent : 0 < quittingTailEventualAbsorption roots time)
    (hnext : 0 < quittingTailEventualAbsorption roots (time + 1))
    (htight : boundary who = quittingSoloBaseline reward who)
    (hsmall : Fintype.card ι *
      quittingTailConditionedAbsorptionWeight roots time ≤ 1)
    (hhalf : quittingTailConditionedAbsorptionWeight roots time ≤ 1 / 2) :
    quittingStationaryFixedOpponentsContinueReward reward
          (quittingTailDiffuseRescaledRoot roots time hcurrent) who +
        quittingStationaryFixedOpponentsContinueMass
            (quittingTailDiffuseRescaledRoot roots time hcurrent) who *
          quittingTailConditionedValue roots value boundary (time + 1) who ≤
      quittingTailConditionedValue roots value boundary time who +
        (4 * Fintype.card ι + 16) * M *
          quittingTailConditionedAbsorptionWeight roots time *
          quittingRootOpponentAbsorptionMass
            (quittingTailDiffuseRescaledRoot roots time hcurrent) who := by
  have hM :=
    quittingRewardCoordinateBound_nonneg_of_player reward who hreward
  let alpha := quittingTailConditionedAbsorptionWeight roots time
  let opponentTotal :=
    quittingTailDiffuseRescaledOpponentTotal roots time who
  let sourceOpponent := quittingTailConditionedOpponentWeight roots time who
  let targetOpponent := quittingRootOpponentAbsorptionMass
    (quittingTailDiffuseRescaledRoot roots time hcurrent) who
  let sourceContinue :=
    quittingStationaryFixedOpponentsContinueMass (roots time) who
  let targetContinue := quittingStationaryFixedOpponentsContinueMass
    (quittingTailDiffuseRescaledRoot roots time hcurrent) who
  let sourceReward :=
    quittingStationaryFixedOpponentsContinueReward reward (roots time) who
  let targetReward := quittingStationaryFixedOpponentsContinueReward reward
    (quittingTailDiffuseRescaledRoot roots time hcurrent) who
  let own := quittingTailDiffuseRescaledHazard roots time who
  let phantom := quittingJointSurvivalLimit roots (time + 1)
  let nextValue :=
    quittingTailConditionedValue roots value boundary (time + 1) who
  let currentValue :=
    quittingTailConditionedValue roots value boundary time who
  have hsource :=
    conditionedSourceContinueBase_le_conditionedValue_sub_phantom
      roots value boundary hpolicy hnash time who hcurrent hnext
  change sourceReward / quittingTailEventualAbsorption roots time +
      sourceContinue * quittingTailEventualAbsorption roots (time + 1) /
        quittingTailEventualAbsorption roots time * nextValue ≤
    currentValue - sourceContinue * own * phantom * boundary who at hsource
  have hrewards := abs_conditionedOpponentAbsorbingReward_sub_rescaled_le
    (reward := reward) roots time who hreward hcurrent
  change |sourceReward / quittingTailEventualAbsorption roots time -
      targetReward| ≤ 3 / 2 * M * opponentTotal ^ 2 at hrewards
  have hclock :=
    abs_conditionedOpponentWeight_sub_rescaledRoot_opponentAbsorption_le
      roots time who hcurrent
  change |sourceOpponent - targetOpponent| ≤ opponentTotal ^ 2 / 2 at hclock
  have hseam :=
    quittingTailDiffuse_deletedContinuation_rescaling_identity
      roots time who hcurrent
  have hsourceContinueEq : sourceContinue =
      1 - quittingRootOpponentAbsorptionMass (roots time) who := by
    unfold sourceContinue quittingStationaryFixedOpponentsContinueMass
      quittingFixedOpponentsContinueMass quittingRootOpponentAbsorptionMass
      quittingRootAbsorptionMass
    ring
  have htargetContinueEq : targetContinue =
      1 - quittingRootOpponentAbsorptionMass
        (quittingTailDiffuseRescaledRoot roots time hcurrent) who := by
    unfold targetContinue quittingStationaryFixedOpponentsContinueMass
      quittingFixedOpponentsContinueMass quittingRootOpponentAbsorptionMass
      quittingRootAbsorptionMass
    ring
  rw [← hsourceContinueEq, ← htargetContinueEq] at hseam
  change targetContinue -
      sourceContinue * quittingTailEventualAbsorption roots (time + 1) /
        quittingTailEventualAbsorption roots time =
    sourceOpponent - targetOpponent + sourceContinue * own * phantom at hseam
  have hdecompose :
      targetReward + targetContinue * nextValue =
        (sourceReward / quittingTailEventualAbsorption roots time +
          sourceContinue * quittingTailEventualAbsorption roots (time + 1) /
            quittingTailEventualAbsorption roots time * nextValue) +
        (targetReward -
          sourceReward / quittingTailEventualAbsorption roots time) +
        (sourceOpponent - targetOpponent) * nextValue +
        sourceContinue * own * phantom * nextValue := by
    have htargetContinue : targetContinue =
        sourceContinue * quittingTailEventualAbsorption roots (time + 1) /
            quittingTailEventualAbsorption roots time +
          sourceOpponent - targetOpponent + sourceContinue * own * phantom := by
      linarith [hseam]
    rw [htargetContinue]
    ring
  have hopponentTotal0 : 0 ≤ opponentTotal := by
    unfold opponentTotal quittingTailDiffuseRescaledOpponentTotal
    exact Finset.sum_nonneg fun player _ =>
      quittingTailDiffuseRescaledHazard_nonneg roots time player hcurrent
  have halpha0 : 0 ≤ alpha :=
    quittingTailConditionedAbsorptionWeight_nonneg roots time hcurrent
  have htargetOpponent0 : 0 ≤ targetOpponent := by
    unfold targetOpponent
    exact quittingRootAbsorptionMass_nonneg _
  have hsourceOpponent0 : 0 ≤ sourceOpponent := by
    exact quittingTailConditionedOpponentWeight_nonneg roots time who hcurrent
  have htotalUpper : opponentTotal ≤ Fintype.card ι * alpha :=
    (quittingTailDiffuseRescaledOpponentTotal_le_total
      roots time who hcurrent).trans
      (quittingTailDiffuseRescaledTotal_le_card_mul_conditionedWeight
        roots time hcurrent)
  have htotalOne : opponentTotal ≤ 1 := htotalUpper.trans hsmall
  have htargetLower :=
    quittingTailDiffuseRescaledOpponentTotal_sub_sq_div_two_le_opponentAbsorption
      roots time who hcurrent
  change opponentTotal - opponentTotal ^ 2 / 2 ≤ targetOpponent at htargetLower
  have htotalHalf : opponentTotal / 2 ≤ targetOpponent := by
    nlinarith [sq_nonneg opponentTotal]
  have hsquare : opponentTotal ^ 2 ≤
      2 * (Fintype.card ι * alpha) * targetOpponent := by
    nlinarith [mul_nonneg
      (sub_nonneg.mpr htotalUpper) (sub_nonneg.mpr (by
        linarith [htotalHalf] : opponentTotal ≤ 2 * targetOpponent))]
  have hsourceClock :=
    half_conditionedOpponentWeight_le_rescaledRoot_opponentAbsorption
      roots time who hcurrent hsmall
  change sourceOpponent / 2 ≤ targetOpponent at hsourceClock
  have hsourceContinue0 : 0 ≤ sourceContinue := by
    exact quittingStationaryFixedOpponentsContinueMass_nonneg (roots time) who
  have hsourceContinue1 : sourceContinue ≤ 1 := by
    exact quittingStationaryFixedOpponentsContinueMass_le_one (roots time) who
  have hown0 : 0 ≤ own :=
    quittingTailDiffuseRescaledHazard_nonneg roots time who hcurrent
  have hownAlpha : own ≤ alpha :=
    quittingTailDiffuseRescaledHazard_le_conditionedWeight
      roots time who hcurrent
  have hphantom0 : 0 ≤ phantom :=
    quittingJointSurvivalLimit_nonneg roots (time + 1)
  have hphantom1 : phantom ≤ 1 := by
    have hnextNonneg :=
      (quittingTailEventualAbsorption_mem_unitInterval roots (time + 1)).1
    unfold phantom quittingTailEventualAbsorption at hnextNonneg
    linarith
  have hownTerm :
      sourceContinue * own * phantom * (nextValue - boundary who) ≤
        16 * M * alpha * targetOpponent := by
    by_cases hownZero : own = 0
    · rw [hownZero, mul_zero, zero_mul]
      have h16M : 0 ≤ (16 : ℝ) * M :=
        mul_nonneg (by norm_num) hM
      have hnonneg := mul_nonneg (mul_nonneg h16M halpha0) htargetOpponent0
      simpa only [zero_mul] using hnonneg
    · have hownPos : 0 < own := lt_of_le_of_ne hown0 (Ne.symm hownZero)
      have hactive : 0 < (roots time who true).toReal := by
        have hscaledOwn : (roots time who true).toReal =
            quittingTailEventualAbsorption roots time * own := by
          unfold own quittingTailDiffuseRescaledHazard
          field_simp [hcurrent.ne']
        rw [hscaledOwn]
        positivity
      have hgap :=
        abs_quittingTailConditionedValue_succ_sub_singleton_le
          roots value boundary hpolicy hnash time who hreward hcurrent hnext
            hactive htight hhalf
      have hboundary : boundary who =
          reward (quittingSingletonTerminal who) who := by
        simpa [quittingSoloBaseline, quittingSoloReward,
          quittingSingletonTerminal] using htight
      rw [← hboundary] at hgap
      change |nextValue - boundary who| ≤ 8 * M * sourceOpponent at hgap
      have hnextGap : |nextValue - boundary who| ≤
          16 * M * targetOpponent := by
        nlinarith [mul_nonneg hM hsourceOpponent0,
          mul_nonneg hM htargetOpponent0]
      have hprefix0 : 0 ≤ sourceContinue * own * phantom :=
        mul_nonneg (mul_nonneg hsourceContinue0 hown0) hphantom0
      have habsTerm := mul_le_mul_of_nonneg_left hnextGap hprefix0
      have hcombined : sourceContinue * phantom ≤ 1 := by
        nlinarith [mul_nonneg hsourceContinue0 hphantom0,
          mul_nonneg (sub_nonneg.mpr hsourceContinue1)
            (sub_nonneg.mpr hphantom1)]
      have hprefixOwn : sourceContinue * own * phantom ≤ own := by
        calc
          sourceContinue * own * phantom = own * (sourceContinue * phantom) := by
            ring
          _ ≤ own * 1 := mul_le_mul_of_nonneg_left hcombined hown0
          _ = own := mul_one _
      have hcoefficient0 : 0 ≤ 16 * M * targetOpponent :=
        mul_nonneg (mul_nonneg (by norm_num) hM) htargetOpponent0
      have habsUpper : sourceContinue * own * phantom *
            |nextValue - boundary who| ≤
          16 * M * alpha * targetOpponent := by
        calc
          sourceContinue * own * phantom * |nextValue - boundary who| ≤
              sourceContinue * own * phantom *
                (16 * M * targetOpponent) := habsTerm
          _ ≤ own * (16 * M * targetOpponent) := by
            exact mul_le_mul_of_nonneg_right hprefixOwn hcoefficient0
          _ ≤ alpha * (16 * M * targetOpponent) :=
            mul_le_mul_of_nonneg_right hownAlpha hcoefficient0
          _ = 16 * M * alpha * targetOpponent := by ring
      calc
        sourceContinue * own * phantom * (nextValue - boundary who) ≤
            |sourceContinue * own * phantom *
              (nextValue - boundary who)| := le_abs_self _
        _ = sourceContinue * own * phantom *
              |nextValue - boundary who| := by
          rw [abs_mul, abs_of_nonneg hprefix0]
        _ ≤ 16 * M * alpha * targetOpponent := habsUpper
  have hrewardsUpper : targetReward -
      sourceReward / quittingTailEventualAbsorption roots time ≤
        3 / 2 * M * opponentTotal ^ 2 := by
    have := neg_le_of_abs_le hrewards
    linarith
  have hclockTerm : (sourceOpponent - targetOpponent) * nextValue ≤
      M * (opponentTotal ^ 2 / 2) := by
    calc
      (sourceOpponent - targetOpponent) * nextValue ≤
          |sourceOpponent - targetOpponent| * |nextValue| := by
        exact (le_abs_self _).trans_eq (abs_mul _ _)
      _ ≤ (opponentTotal ^ 2 / 2) * M :=
        mul_le_mul hclock hconditionedBound (abs_nonneg _)
          (by positivity)
      _ = M * (opponentTotal ^ 2 / 2) := by ring
  rw [hdecompose]
  calc
    _ ≤ (currentValue - sourceContinue * own * phantom * boundary who) +
          (3 / 2 * M * opponentTotal ^ 2) +
          M * (opponentTotal ^ 2 / 2) +
          sourceContinue * own * phantom * nextValue := by
      gcongr
    _ = currentValue + 3 / 2 * M * opponentTotal ^ 2 +
          M * (opponentTotal ^ 2 / 2) +
          sourceContinue * own * phantom * (nextValue - boundary who) := by
      ring
    _ ≤ currentValue + 3 / 2 * M * opponentTotal ^ 2 +
          M * (opponentTotal ^ 2 / 2) +
          16 * M * alpha * targetOpponent := by
      gcongr
    _ = currentValue + 2 * M * opponentTotal ^ 2 +
          16 * M * alpha * targetOpponent := by ring
    _ ≤ currentValue +
          4 * M * (Fintype.card ι * alpha) * targetOpponent +
          16 * M * alpha * targetOpponent := by
      have hcoefficient : 0 ≤ 2 * M := by positivity
      have hscaled := mul_le_mul_of_nonneg_left hsquare hcoefficient
      have hscaled' : 2 * M * opponentTotal ^ 2 ≤
          4 * M * (Fintype.card ι * alpha) * targetOpponent := by
        calc
          2 * M * opponentTotal ^ 2 ≤
              2 * M *
                (2 * (Fintype.card ι * alpha) * targetOpponent) := hscaled
          _ = 4 * M * (Fintype.card ι * alpha) * targetOpponent := by ring
      simpa [add_comm, add_left_comm, add_assoc] using
        (add_le_add_right (add_le_add_left hscaled' currentValue)
          (16 * M * alpha * targetOpponent))
    _ = currentValue +
        (4 * Fintype.card ι + 16) * M * alpha * targetOpponent := by ring

/-- The conditioned source coalition law evaluates exactly to the
conditioned Bellman state. -/
theorem sum_conditionedCoalitionMass_mul_stagePayoff_eq_conditionedValue
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (time : ℕ)
    (hcurrent : 0 < quittingTailEventualAbsorption roots time)
    (hnext : 0 < quittingTailEventualAbsorption roots (time + 1))
    (who : ι) :
    (∑ coalition,
        quittingTailConditionedCoalitionMass roots time coalition *
          quittingStageCoalitionPayoff reward
            (quittingTailConditionedValue roots value boundary (time + 1))
            coalition who) =
      quittingTailConditionedValue roots value boundary time who := by
  let next := quittingTailConditionedValue roots value boundary (time + 1)
  let currentScale := quittingTailEventualAbsorption roots time
  let nextScale := quittingTailEventualAbsorption roots (time + 1)
  let continueMass := quittingStationaryContinueMass (roots time)
  have habsorbing :
      (∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
          quittingRootCoalitionMass (roots time) coalition *
            quittingStageCoalitionPayoff reward next coalition who) =
        quittingRootAbsorbingContribution reward (roots time) who := by
    rw [quittingRootAbsorbingContribution_eq_sum_coalitionMass]
    change _ = ∑ coalition,
      quittingRootCoalitionMass (roots time) coalition *
        quittingProjectiveCoalitionReward reward coalition who
    rw [← Finset.add_sum_erase Finset.univ
      (fun coalition => quittingRootCoalitionMass (roots time) coalition *
        quittingProjectiveCoalitionReward reward coalition who)
      (Finset.mem_univ ∅)]
    simp only [quittingProjectiveCoalitionReward_empty, mul_zero, zero_add]
    apply Finset.sum_congr rfl
    intro coalition hcoalition
    have hne : coalition.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase hcoalition)
    simp [quittingStageCoalitionPayoff, quittingProjectiveCoalitionReward,
      hne]
  have hsum :
      (∑ coalition,
          quittingTailConditionedCoalitionMass roots time coalition *
            quittingStageCoalitionPayoff reward next coalition who) =
        (quittingRootAbsorbingContribution reward (roots time) who +
          continueMass * nextScale * next who) / currentScale := by
    rw [← Finset.add_sum_erase Finset.univ
      (fun coalition =>
        quittingTailConditionedCoalitionMass roots time coalition *
          quittingStageCoalitionPayoff reward next coalition who)
      (Finset.mem_univ ∅)]
    have herase :
        (∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
          quittingTailConditionedCoalitionMass roots time coalition *
            quittingStageCoalitionPayoff reward next coalition who) =
          quittingRootAbsorbingContribution reward (roots time) who /
            currentScale := by
      calc
        _ = (∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
            quittingRootCoalitionMass (roots time) coalition *
              quittingStageCoalitionPayoff reward next coalition who) /
              currentScale := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro coalition hcoalition
          have hne : coalition ≠ ∅ := Finset.ne_of_mem_erase hcoalition
          simp only [quittingTailConditionedCoalitionMass, hne, if_false]
          ring
        _ = _ := by rw [habsorbing]
    rw [herase]
    simp only [quittingTailConditionedCoalitionMass, if_pos,
      quittingStageCoalitionPayoff, Finset.not_nonempty_empty, dite_false]
    dsimp only [currentScale, nextScale, continueMass]
    ring
  rw [hsum]
  have hstep := congrFun (hpolicy time) who
  rw [quittingRootSuccessorPayoff_apply_eq_affine] at hstep
  have hsurvival := quittingJointSurvivalLimit_eq_continue_mul_succ roots time
  dsimp only [next, currentScale, nextScale, continueMass]
  have hnextValue :
      quittingTailEventualAbsorption roots (time + 1) *
          quittingTailConditionedValue roots value boundary (time + 1) who =
        value (time + 1) who -
          quittingJointSurvivalLimit roots (time + 1) * boundary who := by
    unfold quittingTailConditionedValue
    field_simp [hnext.ne']
  rw [mul_assoc, hnextValue]
  unfold quittingTailConditionedValue
  rw [hstep, hsurvival]
  field_simp [hcurrent.ne', hnext.ne']
  ring

omit [DecidableEq ι] in
/-- **Quadratic policy error of diffuse product rescaling.** -/
theorem abs_conditionedValue_sub_rescaledSuccessorPayoff_le
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hconditionedBound : ∀ time player,
      |quittingTailConditionedValue roots value boundary time player| ≤ M)
    (time : ℕ)
    (hcurrent : 0 < quittingTailEventualAbsorption roots time)
    (hnext : 0 < quittingTailEventualAbsorption roots (time + 1))
    (who : ι) :
    |quittingTailConditionedValue roots value boundary time who -
        quittingRootSuccessorPayoff reward
          (quittingTailConditionedValue roots value boundary (time + 1))
          (quittingTailDiffuseRescaledRoot roots time hcurrent) who| ≤
      2 * M * quittingTailDiffuseRescaledTotal roots time ^ 2 := by
  have hM :=
    quittingRewardCoordinateBound_nonneg_of_player reward who hreward
  classical
  let next := quittingTailConditionedValue roots value boundary (time + 1)
  let observable : Finset ι → ℝ := fun coalition =>
    quittingStageCoalitionPayoff reward next coalition who
  have hobservable : ∀ coalition, |observable coalition| ≤ M := by
    intro coalition
    by_cases hnonempty : coalition.Nonempty
    · simpa [observable, quittingStageCoalitionPayoff, hnonempty] using
        hreward ⟨coalition, hnonempty⟩ who
    · simpa [observable, quittingStageCoalitionPayoff, hnonempty, next] using
        hconditionedBound (time + 1) who
  have hlaw := abs_conditionedCoalitionExpectation_sub_rescaled_le
    roots time observable hM hobservable hcurrent
  have hsource :=
    sum_conditionedCoalitionMass_mul_stagePayoff_eq_conditionedValue
      roots value boundary hpolicy time hcurrent hnext who
  have htarget := quittingRootExpectedPayoff_eq_sum_coalitionMass
    reward next (quittingTailDiffuseRescaledRoot roots time hcurrent) who
  change |quittingTailConditionedValue roots value boundary time who -
      quittingRootExpectedPayoff reward next
        (quittingTailDiffuseRescaledRoot roots time hcurrent) who| ≤ _
  rw [htarget]
  rw [← hsource]
  exact hlaw

/-! ## Infinite-path certificate -/

omit [DecidableEq ι] in
/-- Quadratic policy error rewritten as a joint-clock charge under a uniform
mesh cap. -/
theorem abs_conditionedValue_sub_rescaledSuccessorPayoff_le_jointCharge
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    {M rho : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hconditionedBound : ∀ time player,
      |quittingTailConditionedValue roots value boundary time player| ≤ M)
    (time : ℕ) (who : ι)
    (hcurrent : 0 < quittingTailEventualAbsorption roots time)
    (hnext : 0 < quittingTailEventualAbsorption roots (time + 1))
    (hmesh : quittingTailConditionedAbsorptionWeight roots time ≤ rho)
    (hsmall : Fintype.card ι *
      quittingTailConditionedAbsorptionWeight roots time ≤ 1) :
    |quittingTailConditionedValue roots value boundary time who -
        quittingRootSuccessorPayoff reward
          (quittingTailConditionedValue roots value boundary (time + 1))
          (quittingTailDiffuseRescaledRoot roots time hcurrent) who| ≤
      (4 * M * Fintype.card ι * rho) *
        quittingRootAbsorptionMass
          (quittingTailDiffuseRescaledRoot roots time hcurrent) := by
  have hM :=
    quittingRewardCoordinateBound_nonneg_of_player reward who hreward
  let alpha := quittingTailConditionedAbsorptionWeight roots time
  let total := quittingTailDiffuseRescaledTotal roots time
  let absorption := quittingRootAbsorptionMass
    (quittingTailDiffuseRescaledRoot roots time hcurrent)
  have hbase := abs_conditionedValue_sub_rescaledSuccessorPayoff_le
    (reward := reward) roots value boundary hpolicy hreward hconditionedBound
      time hcurrent hnext who
  change |_ - _| ≤ 2 * M * total ^ 2 at hbase
  have halpha0 : 0 ≤ alpha :=
    quittingTailConditionedAbsorptionWeight_nonneg roots time hcurrent
  have hrho0 : 0 ≤ rho := halpha0.trans hmesh
  have htotal0 : 0 ≤ total := by
    unfold total quittingTailDiffuseRescaledTotal
    exact Finset.sum_nonneg fun player _ =>
      quittingTailDiffuseRescaledHazard_nonneg roots time player hcurrent
  have htotalUpper : total ≤ Fintype.card ι * alpha :=
    quittingTailDiffuseRescaledTotal_le_card_mul_conditionedWeight
      roots time hcurrent
  have htotalOne : total ≤ 1 := htotalUpper.trans hsmall
  have hbonferroni :=
    quittingTailDiffuseRescaledTotal_sub_sq_div_two_le_absorptionMass
      roots time hcurrent
  change total - total ^ 2 / 2 ≤ absorption at hbonferroni
  have hhalfTotal : total / 2 ≤ absorption := by
    nlinarith [sq_nonneg total]
  have habsorption0 : 0 ≤ absorption := by
    unfold absorption
    exact quittingRootAbsorptionMass_nonneg _
  have hsquare : total ^ 2 ≤
      2 * (Fintype.card ι * rho) * absorption := by
    have htotalRho : total ≤ Fintype.card ι * rho :=
      htotalUpper.trans (mul_le_mul_of_nonneg_left hmesh (Nat.cast_nonneg _))
    have htotalAbsorption : total ≤ 2 * absorption := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr htotalRho)
      (sub_nonneg.mpr htotalAbsorption)]
  have hcoefficient : 0 ≤ 2 * M := mul_nonneg (by norm_num) hM
  calc
    |_ - _| ≤ 2 * M * total ^ 2 := hbase
    _ ≤ 2 * M * (2 * (Fintype.card ι * rho) * absorption) :=
      mul_le_mul_of_nonneg_left hsquare hcoefficient
    _ = (4 * M * Fintype.card ι * rho) * absorption := by ring

/-- A source spectator needs no singleton-boundary estimate for its Continue
endpoint.  Diffuse rescaling keeps the player at literal Never, so its
prescribed endpoint is pure Continue and the joint policy error is already a
deleted-clock error for that player. -/
theorem rescaledContinuePayoff_le_conditionedValue_add_jointCharge_of_source_pure_false
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    {M rho : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hconditionedBound : ∀ time player,
      |quittingTailConditionedValue roots value boundary time player| ≤ M)
    (time : ℕ) (who : ι)
    (hcurrent : 0 < quittingTailEventualAbsorption roots time)
    (hnext : 0 < quittingTailEventualAbsorption roots (time + 1))
    (hinactive : roots time who = PMF.pure false)
    (hmesh : quittingTailConditionedAbsorptionWeight roots time ≤ rho)
    (hsmall : Fintype.card ι *
      quittingTailConditionedAbsorptionWeight roots time ≤ 1) :
    quittingStationaryFixedOpponentsContinueReward reward
          (quittingTailDiffuseRescaledRoot roots time hcurrent) who +
        quittingStationaryFixedOpponentsContinueMass
            (quittingTailDiffuseRescaledRoot roots time hcurrent) who *
          quittingTailConditionedValue roots value boundary (time + 1) who ≤
      quittingTailConditionedValue roots value boundary time who +
        (4 * M * Fintype.card ι * rho) *
          quittingRootOpponentAbsorptionMass
            (quittingTailDiffuseRescaledRoot roots time hcurrent) who := by
  let targetRoot := quittingTailDiffuseRescaledRoot roots time hcurrent
  let next := quittingTailConditionedValue roots value boundary (time + 1)
  have htargetInactive : targetRoot who = PMF.pure false :=
    quittingTailDiffuseRescaledRoot_eq_pure_false_of_source_eq_pure_false
      roots time who hcurrent hinactive
  have hsuccessor :
      quittingRootSuccessorPayoff reward next targetRoot who =
        quittingStationaryFixedOpponentsContinueReward reward targetRoot who +
          quittingStationaryFixedOpponentsContinueMass targetRoot who *
            next who := by
    rw [quittingRootSuccessorPayoff_eq_endpointMix, htargetInactive]
    simp [PMF.pure_apply]
    simpa [quittingStationaryFixedOpponentsContinueReward,
      quittingStationaryFixedOpponentsContinueMass] using
        quittingRootContinuePayoff_eq_fixedOpponents
          reward (fun _ => targetRoot) who next 0
  have habsorption : quittingRootAbsorptionMass targetRoot =
      quittingRootOpponentAbsorptionMass targetRoot who := by
    unfold quittingRootOpponentAbsorptionMass
    congr 1
    funext player
    by_cases hplayer : player = who
    · subst player
      simp [htargetInactive]
    · simp [Function.update_of_ne hplayer]
  have hpolicyBound :=
    abs_conditionedValue_sub_rescaledSuccessorPayoff_le_jointCharge
      (reward := reward) roots value boundary hpolicy hreward
        hconditionedBound time who hcurrent hnext hmesh hsmall
  have hupper := neg_le_of_abs_le hpolicyBound
  dsimp only [targetRoot, next] at hsuccessor habsorption
  rw [hsuccessor, habsorption] at hupper
  linarith

/-- **Compiler for the singleton-tight deleted-complete diffuse branch.**
Every hypothesis is local to the conditioned source chronology.  The target
product path has separated joint-policy and deleted-refusal errors, hence is
an explicit asymptotic approximate Nash profile. -/
theorem conditionedDiffuseRescaledRoots_isεAsymptoticNash_and_approximates
    [Nonempty ι]
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    {M rho : ℝ} (hrho : 0 ≤ rho)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : ∀ time,
      0 < quittingTailEventualAbsorption roots time)
    (hconditionedBound : ∀ time player,
      |quittingTailConditionedValue roots value boundary time player| ≤ M)
    (htight : ∀ who,
      boundary who = quittingSoloBaseline reward who)
    (hmesh : ∀ time,
      quittingTailConditionedAbsorptionWeight roots time ≤ rho)
    (hsmall : ∀ time, Fintype.card ι *
      quittingTailConditionedAbsorptionWeight roots time ≤ 1)
    (hhalf : ∀ time,
      quittingTailConditionedAbsorptionWeight roots time ≤ 1 / 2)
    (hdeletedComplete : ∀ who start,
      ¬Summable (fun offset =>
        quittingTailConditionedOpponentWeight roots (start + offset) who)) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward)
        ((4 * M * Fintype.card ι * rho) +
          (6 * M * Fintype.card ι * rho) +
          ((4 * Fintype.card ι + 16) * M * rho))
        (quittingInfinitePathProfile reward
          (quittingTailDiffuseRescaledRoots roots hpositive)) ∧
      ∀ who,
        |quittingTerminalPayoff reward
            (quittingInfinitePathProfile reward
              (quittingTailDiffuseRescaledRoots roots hpositive)) who -
          quittingTailConditionedValue roots value boundary 0 who| ≤
        4 * M * Fintype.card ι * rho := by
  have hM := quittingRewardCoordinateBound_nonneg_of_nonempty reward hreward
  let policyCoefficient := 4 * M * Fintype.card ι * rho
  let quitError := 6 * M * Fintype.card ι * rho
  let refusalCoefficient := (4 * Fintype.card ι + 16) * M * rho
  let target := quittingTailConditionedValue roots value boundary 0
  let targetRoots := quittingTailDiffuseRescaledRoots roots hpositive
  let targetValue : ℕ → Payoff ι := fun time =>
    quittingTailConditionedValue roots value boundary time
  have hopponentSurvival : ∀ who start,
      Tendsto (quittingOpponentSurvivalWeight targetRoots who start)
        atTop (nhds 0) := by
    intro who start
    exact tendsto_zero_opponentSurvivalWeight_quittingTailDiffuseRescaledRoots
      roots hpositive hsmall who start (hdeletedComplete who start)
  have hjointSurvival : ∀ start,
      Tendsto (quittingJointSurvivalWeight targetRoots start)
        atTop (nhds 0) := by
    intro start
    let who : ι := Classical.choice (inferInstance : Nonempty ι)
    exact squeeze_zero
      (fun fuel => quittingJointSurvivalWeight_nonneg targetRoots start fuel)
      (fun fuel =>
        quittingJointSurvivalWeight_le_quittingOpponentSurvivalWeight
          targetRoots who start fuel)
      (hopponentSurvival who start)
  let certificate : QuittingInfinitePathJointPolicySeparatedErrorCertificate
      reward target policyCoefficient quitError refusalCoefficient M :=
    { roots := targetRoots
      value := targetValue
      value_zero := rfl
      joint_survival := hjointSurvival
      opponent_survival := hopponentSurvival
      value_bound := hconditionedBound
      policy_error := by
        intro time who
        exact abs_conditionedValue_sub_rescaledSuccessorPayoff_le_jointCharge
          (reward := reward) roots value boundary hpolicy hreward
            hconditionedBound time who (hpositive time) (hpositive (time + 1))
              (hmesh time) (hsmall time)
      quit_le := by
        intro time who
        have hquit :=
          quittingStationaryFixedOpponentsQuitValue_rescaledRoot_le_conditionedValue_add_of_nash
            (reward := reward) roots value boundary hpolicy hnash time who
              hreward (hpositive time) (htight who) (hsmall time)
        change _ ≤ targetValue time who + quitError
        dsimp only [targetValue, quitError]
        calc
          _ ≤ quittingTailConditionedValue roots value boundary time who +
              6 * M * Fintype.card ι *
                quittingTailConditionedAbsorptionWeight roots time := hquit
          _ ≤ quittingTailConditionedValue roots value boundary time who +
              6 * M * Fintype.card ι * rho := by
            have hcoefficient : 0 ≤ 6 * M * (Fintype.card ι : ℝ) := by
              positivity
            simpa [add_comm] using
              (add_le_add_left
                (mul_le_mul_of_nonneg_left (hmesh time) hcoefficient)
                (quittingTailConditionedValue roots value boundary time who))
      continue_le := by
        intro time who
        have hcontinue :=
          rescaledContinuePayoff_le_conditionedValue_add_deletedCharge
            (reward := reward) roots value boundary hpolicy hnash time who
              hreward (hconditionedBound (time + 1) who) (hpositive time)
                (hpositive (time + 1)) (htight who) (hsmall time) (hhalf time)
        change _ ≤ targetValue time who + refusalCoefficient *
          (1 - quittingStationaryFixedOpponentsContinueMass
            (targetRoots time) who)
        have hopponentIdentity :
            1 - quittingStationaryFixedOpponentsContinueMass
                (targetRoots time) who =
              quittingRootOpponentAbsorptionMass (targetRoots time) who := by
          unfold quittingStationaryFixedOpponentsContinueMass
            quittingFixedOpponentsContinueMass
            quittingRootOpponentAbsorptionMass quittingRootAbsorptionMass
          ring
        rw [hopponentIdentity]
        dsimp only [targetRoots, targetValue, refusalCoefficient]
        change _ ≤ _ + _ *
          quittingRootOpponentAbsorptionMass
            (quittingTailDiffuseRescaledRoot roots time (hpositive time)) who
        calc
          _ ≤ quittingTailConditionedValue roots value boundary time who +
              (4 * Fintype.card ι + 16) * M *
                quittingTailConditionedAbsorptionWeight roots time *
                quittingRootOpponentAbsorptionMass
                  (quittingTailDiffuseRescaledRoot roots time
                    (hpositive time)) who := hcontinue
          _ ≤ quittingTailConditionedValue roots value boundary time who +
              ((4 * Fintype.card ι + 16) * M * rho) *
                quittingRootOpponentAbsorptionMass
                  (quittingTailDiffuseRescaledRoot roots time
                    (hpositive time)) who := by
            have hfactor : 0 ≤
                (4 * Fintype.card ι + 16) * M := by positivity
            have hcharge := mul_le_mul_of_nonneg_left (hmesh time) hfactor
            have hopponent0 := quittingRootAbsorptionMass_nonneg
              (Function.update
                (quittingTailDiffuseRescaledRoot roots time (hpositive time))
                who (PMF.pure false))
            gcongr }
  have hpolicyCoefficient : 0 ≤ policyCoefficient := by
    unfold policyCoefficient
    positivity
  have hquitError : 0 ≤ quitError := by
    unfold quitError
    positivity
  have hrefusal : 0 ≤ refusalCoefficient := by
    unfold refusalCoefficient
    positivity
  simpa [certificate, policyCoefficient, quitError, refusalCoefficient,
    target, targetRoots] using
    (certificate.isεAsymptoticNash_and_approximates reward target
      hpolicyCoefficient hquitError hrefusal hM hreward)

/-- **Proper-face diffuse compiler.**  A late source row may contain both
singleton-tight active players and literal-Never spectators.  Tight players
use the deleted-clock strategic estimate.  Spectators remain pure Continue
after rescaling, so their Continue endpoint is controlled by the joint
policy estimate; only their pure-Quit endpoint must be supplied separately.

This is the exact compiler interface for the proper singleton-tight face:
strict plateau coordinates cost no Continue error and expose only an
immediate-Quit obstruction. -/
theorem
    conditionedDiffuseRescaledRoots_isεAsymptoticNash_and_approximates_of_tight_or_inactive
    [Nonempty ι]
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    {M rho quitError : ℝ} (hrho : 0 ≤ rho)
    (hquitError : 0 ≤ quitError)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : ∀ time,
      0 < quittingTailEventualAbsorption roots time)
    (hconditionedBound : ∀ time player,
      |quittingTailConditionedValue roots value boundary time player| ≤ M)
    (htightOrInactive : ∀ time who,
      boundary who = quittingSoloBaseline reward who ∨
        roots time who = PMF.pure false)
    (hquit_le : ∀ time who,
      quittingStationaryFixedOpponentsQuitValue reward
          (quittingTailDiffuseRescaledRoot roots time (hpositive time)) who ≤
        quittingTailConditionedValue roots value boundary time who +
          quitError)
    (hmesh : ∀ time,
      quittingTailConditionedAbsorptionWeight roots time ≤ rho)
    (hsmall : ∀ time, Fintype.card ι *
      quittingTailConditionedAbsorptionWeight roots time ≤ 1)
    (hhalf : ∀ time,
      quittingTailConditionedAbsorptionWeight roots time ≤ 1 / 2)
    (hdeletedComplete : ∀ who start,
      ¬Summable (fun offset =>
        quittingTailConditionedOpponentWeight roots (start + offset) who)) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward)
        ((4 * M * Fintype.card ι * rho) + quitError +
          ((4 * Fintype.card ι + 16) * M * rho))
        (quittingInfinitePathProfile reward
          (quittingTailDiffuseRescaledRoots roots hpositive)) ∧
      ∀ who,
        |quittingTerminalPayoff reward
            (quittingInfinitePathProfile reward
              (quittingTailDiffuseRescaledRoots roots hpositive)) who -
          quittingTailConditionedValue roots value boundary 0 who| ≤
        4 * M * Fintype.card ι * rho := by
  have hM := quittingRewardCoordinateBound_nonneg_of_nonempty reward hreward
  let policyCoefficient := 4 * M * Fintype.card ι * rho
  let refusalCoefficient := (4 * Fintype.card ι + 16) * M * rho
  let target := quittingTailConditionedValue roots value boundary 0
  let targetRoots := quittingTailDiffuseRescaledRoots roots hpositive
  let targetValue : ℕ → Payoff ι := fun time =>
    quittingTailConditionedValue roots value boundary time
  have hopponentSurvival : ∀ who start,
      Tendsto (quittingOpponentSurvivalWeight targetRoots who start)
        atTop (nhds 0) := by
    intro who start
    exact tendsto_zero_opponentSurvivalWeight_quittingTailDiffuseRescaledRoots
      roots hpositive hsmall who start (hdeletedComplete who start)
  have hjointSurvival : ∀ start,
      Tendsto (quittingJointSurvivalWeight targetRoots start)
        atTop (nhds 0) := by
    intro start
    let who : ι := Classical.choice (inferInstance : Nonempty ι)
    exact squeeze_zero
      (fun fuel => quittingJointSurvivalWeight_nonneg targetRoots start fuel)
      (fun fuel =>
        quittingJointSurvivalWeight_le_quittingOpponentSurvivalWeight
          targetRoots who start fuel)
      (hopponentSurvival who start)
  have hpolicy_le_refusal :
      4 * M * Fintype.card ι * rho ≤
        (4 * Fintype.card ι + 16) * M * rho := by
    have hMrho : 0 ≤ M * rho := mul_nonneg hM hrho
    calc
      4 * M * Fintype.card ι * rho =
          (4 * Fintype.card ι) * (M * rho) := by ring
      _ ≤ (4 * Fintype.card ι + 16) * (M * rho) := by
        exact mul_le_mul_of_nonneg_right (by
          have hcard : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
          linarith) hMrho
      _ = (4 * Fintype.card ι + 16) * M * rho := by ring
  let certificate : QuittingInfinitePathJointPolicySeparatedErrorCertificate
      reward target policyCoefficient quitError refusalCoefficient M :=
    { roots := targetRoots
      value := targetValue
      value_zero := rfl
      joint_survival := hjointSurvival
      opponent_survival := hopponentSurvival
      value_bound := hconditionedBound
      policy_error := by
        intro time who
        exact abs_conditionedValue_sub_rescaledSuccessorPayoff_le_jointCharge
          (reward := reward) roots value boundary hpolicy hreward
            hconditionedBound time who (hpositive time) (hpositive (time + 1))
              (hmesh time) (hsmall time)
      quit_le := by
        intro time who
        exact hquit_le time who
      continue_le := by
        intro time who
        have hopponentIdentity :
            1 - quittingStationaryFixedOpponentsContinueMass
                (targetRoots time) who =
              quittingRootOpponentAbsorptionMass (targetRoots time) who := by
          unfold quittingStationaryFixedOpponentsContinueMass
            quittingFixedOpponentsContinueMass
            quittingRootOpponentAbsorptionMass quittingRootAbsorptionMass
          ring
        rw [hopponentIdentity]
        rcases htightOrInactive time who with htight | hinactive
        · have hcontinue :=
            rescaledContinuePayoff_le_conditionedValue_add_deletedCharge
              (reward := reward) roots value boundary hpolicy hnash time who
                hreward (hconditionedBound (time + 1) who) (hpositive time)
                  (hpositive (time + 1)) htight (hsmall time) (hhalf time)
          dsimp only [targetRoots, targetValue, refusalCoefficient]
          change _ ≤ _ + _ *
            quittingRootOpponentAbsorptionMass
              (quittingTailDiffuseRescaledRoot roots time (hpositive time)) who
          calc
            _ ≤ quittingTailConditionedValue roots value boundary time who +
                (4 * Fintype.card ι + 16) * M *
                  quittingTailConditionedAbsorptionWeight roots time *
                  quittingRootOpponentAbsorptionMass
                    (quittingTailDiffuseRescaledRoot roots time
                      (hpositive time)) who := hcontinue
            _ ≤ quittingTailConditionedValue roots value boundary time who +
                ((4 * Fintype.card ι + 16) * M * rho) *
                  quittingRootOpponentAbsorptionMass
                    (quittingTailDiffuseRescaledRoot roots time
                      (hpositive time)) who := by
              have hfactor : 0 ≤ (4 * Fintype.card ι + 16) * M := by
                positivity
              have hcharge := mul_le_mul_of_nonneg_left (hmesh time) hfactor
              have hopponent0 := quittingRootAbsorptionMass_nonneg
                (Function.update
                  (quittingTailDiffuseRescaledRoot roots time (hpositive time))
                  who (PMF.pure false))
              gcongr
        · have hcontinue :=
            rescaledContinuePayoff_le_conditionedValue_add_jointCharge_of_source_pure_false
              (reward := reward) roots value boundary hpolicy hreward
                hconditionedBound time who (hpositive time)
                  (hpositive (time + 1)) hinactive (hmesh time) (hsmall time)
          dsimp only [targetRoots, targetValue, refusalCoefficient]
          change _ ≤ _ + _ *
            quittingRootOpponentAbsorptionMass
              (quittingTailDiffuseRescaledRoot roots time (hpositive time)) who
          calc
            _ ≤ quittingTailConditionedValue roots value boundary time who +
                (4 * M * Fintype.card ι * rho) *
                  quittingRootOpponentAbsorptionMass
                    (quittingTailDiffuseRescaledRoot roots time
                      (hpositive time)) who := hcontinue
            _ ≤ quittingTailConditionedValue roots value boundary time who +
                ((4 * Fintype.card ι + 16) * M * rho) *
                  quittingRootOpponentAbsorptionMass
                    (quittingTailDiffuseRescaledRoot roots time
                      (hpositive time)) who := by
              have hopponent0 := quittingRootAbsorptionMass_nonneg
                (Function.update
                  (quittingTailDiffuseRescaledRoot roots time (hpositive time))
                  who (PMF.pure false))
              gcongr }
  have hpolicyCoefficient : 0 ≤ policyCoefficient := by
    unfold policyCoefficient
    positivity
  have hrefusal : 0 ≤ refusalCoefficient := by
    unfold refusalCoefficient
    positivity
  simpa [certificate, policyCoefficient, refusalCoefficient, target,
    targetRoots] using
    (certificate.isεAsymptoticNash_and_approximates reward target
      hpolicyCoefficient hquitError hrefusal hM hreward)

end GameTheory

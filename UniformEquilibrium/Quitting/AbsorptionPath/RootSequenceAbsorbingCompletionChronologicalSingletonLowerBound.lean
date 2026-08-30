/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.FiniteRootSequenceCDFCut
import UniformEquilibrium.Quitting.AbsorptionPath.RootSequenceAbsorbingCompletionChronologicalJumpPerfection
import UniformEquilibrium.Quitting.Paths.QuitEndpointOpponentBound

/-!
# Singleton lower bound at continuous-clock points of chronological limits

At every nonterminal path time, the finite source CDF has a right staircase
inverse.  One further strict source subsequence makes the selected cut clock,
its successor clock, and every cumulative coalition coordinate converge to
the same decoded path time and value.  The intervening root therefore has
vanishing absorption mass.

The reached-stage Nash inequality, the finite prefix/tail payoff identity,
and the one-stage pure-Quit endpoint bound then prove the lower continuous
sequential-perfection inequality literally for every player.

This module proves only that singleton lower bound.  It does not prove that a
positive singleton right derivative forces `absorptionPathPayoff` to equal the
corresponding `singletonReward`, full sequential perfection, or an
unconditional source family.
-/

noncomputable section

namespace GameTheory

open Filter Finset Set
open QuittingAbsorptionPath.QuittingFiniteRootSequenceAbsorption
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
/-- A reached-cut consumer for the lower continuous-clock perfection
inequality.  Its hypotheses expose exactly the source clock, continuation,
and current-row opponent mass used by the proof. -/
theorem quittingSingletonReward_le_of_reachedCuts
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ℕ → ι → PMF Bool) (error : ℕ → ℝ)
    (hnash : ∀ rank, IsεQuittingRootSequenceNash reward
      (error rank) (roots rank))
    (herror : Tendsto error atTop (nhds 0))
    (cut : ℕ → ℕ) (who : ι) {time continuation : ℝ}
    (htime : time < 1)
    (hclock : Tendsto (fun rank ↦
      QuittingAbsorptionPath.quittingRootSequenceClock
        (roots rank) (cut rank)) atTop (nhds time))
    (htail : Tendsto (fun rank ↦
      quittingRootSequenceTerminalValue reward
        (roots rank) who (cut rank)) atTop (nhds continuation))
    (hopponent : Tendsto (fun rank ↦
      quittingRootOpponentAbsorptionMass
        (roots rank (cut rank)) who) atTop (nhds 0)) :
    reward (quittingSingletonTerminal who) who ≤ continuation := by
  let survival : ℕ → ℝ := fun rank ↦
    QuittingAbsorptionPath.quittingRootSequenceSurvival
      (roots rank) (cut rank)
  have hsurvival : Tendsto survival atTop (nhds (1 - time)) := by
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa [survival, QuittingAbsorptionPath.quittingRootSequenceClock] using
      hone.sub hclock
  have hsurvival_pos : ∀ᶠ rank in atTop, 0 < survival rank :=
    hsurvival.eventually (Ioi_mem_nhds (sub_pos.mpr htime))
  have htolerance : Tendsto (fun rank ↦ error rank / survival rank)
      atTop (nhds 0) := by
    change Tendsto (error / survival) atTop (nhds 0)
    simpa only [zero_div] using herror.div hsurvival
      (sub_ne_zero.mpr htime.ne')
  let upper : ℕ → ℝ := fun rank ↦
    quittingRootSequenceTerminalValue reward
        (roots rank) who (cut rank) +
      error rank / survival rank +
      2 * quittingRewardBound reward *
        quittingRootOpponentAbsorptionMass
          (roots rank (cut rank)) who
  have hupper : Tendsto upper atTop (nhds continuation) := by
    have hpenalty : Tendsto (fun rank ↦
        2 * quittingRewardBound reward *
          quittingRootOpponentAbsorptionMass
            (roots rank (cut rank)) who) atTop (nhds 0) := by
      simpa using hopponent.const_mul (2 * quittingRewardBound reward)
    simpa [upper] using (htail.add htolerance).add hpenalty
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hupper
  filter_upwards [hsurvival_pos] with rank hrank
  have hrow :=
    isεQuittingRootNash_tailVector_of_isεQuittingRootSequenceNash
      reward (roots rank) (hnash rank) (cut rank) hrank
  have hquit := quittingRootQuitPayoff_le_successor_add_of_isεNash
    reward
    (quittingRootSequenceTailVector reward (roots rank) (cut rank + 1))
    (error rank / survival rank) (roots rank (cut rank)) who hrow
  rw [← quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector]
    at hquit
  have hendpoint :=
    abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
      reward
      (quittingRootSequenceTailVector reward (roots rank) (cut rank + 1))
      (roots rank (cut rank)) who (quittingRewardBound reward)
      (abs_reward_le_quittingRewardBound reward)
  change reward (quittingSingletonTerminal who) who ≤ upper rank
  dsimp only [upper]
  linarith [abs_le.mp hendpoint |>.1]

omit [Nonempty ι] in
/-- Two adjacent source clocks converging to the same nonterminal time force
the conditional absorption mass of the intervening root to vanish. -/
theorem tendsto_rootAbsorptionMass_zero_of_adjacentClocks
    (roots : ℕ → ℕ → ι → PMF Bool) (cut : ℕ → ℕ)
    {time : ℝ} (htime : time < 1)
    (hclock : Tendsto (fun rank ↦
      QuittingAbsorptionPath.quittingRootSequenceClock
        (roots rank) (cut rank)) atTop (nhds time))
    (hclock_succ : Tendsto (fun rank ↦
      QuittingAbsorptionPath.quittingRootSequenceClock
        (roots rank) (cut rank + 1)) atTop (nhds time)) :
    Tendsto (fun rank ↦
      quittingRootAbsorptionMass (roots rank (cut rank)))
      atTop (nhds 0) := by
  let survival : ℕ → ℝ := fun rank ↦
    QuittingAbsorptionPath.quittingRootSequenceSurvival
      (roots rank) (cut rank)
  let stageMass : ℕ → ℝ := fun rank ↦
    QuittingAbsorptionPath.quittingRootSequenceClock
        (roots rank) (cut rank + 1) -
      QuittingAbsorptionPath.quittingRootSequenceClock
        (roots rank) (cut rank)
  have hsurvival : Tendsto survival atTop (nhds (1 - time)) := by
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa [survival, QuittingAbsorptionPath.quittingRootSequenceClock] using
      hone.sub hclock
  have hstageMass : Tendsto stageMass atTop (nhds 0) := by
    simpa [stageMass] using hclock_succ.sub hclock
  have hquotient : Tendsto (fun rank ↦ stageMass rank / survival rank)
      atTop (nhds 0) := by
    change Tendsto (stageMass / survival) atTop (nhds 0)
    simpa only [zero_div] using hstageMass.div hsurvival
      (sub_ne_zero.mpr htime.ne.symm)
  apply hquotient.congr'
  have hsurvival_pos : ∀ᶠ rank in atTop, 0 < survival rank :=
    hsurvival.eventually (Ioi_mem_nhds (sub_pos.mpr htime))
  filter_upwards [hsurvival_pos] with rank hpositive
  rw [div_eq_iff hpositive.ne']
  dsimp only [stageMass, survival]
  rw [clock_succ_sub_clock_eq_sum_stageCoalitionMass]
  simpa only [mul_comm] using
    QuittingAbsorptionPath.sum_stageCoalitionMass_eq_survival_mul_absorptionMass
      (roots rank) (cut rank)

namespace QuittingRootSequenceAbsorbingCompletionDiagonal

variable
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {source : QuittingRootSequenceVanishingNashFamily reward}
    {diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source}

namespace ChronologicalLimit

/-- A source subsequence and finite cuts which approach one continuous path
time from both adjacent source clocks.  The same cuts recover every coalition
coordinate. -/
structure ChronologicalPathTimeAdjacentCutLimit
    (limit : diagonal.ChronologicalLimit) (time : ℝ) where
  rank : ℕ → ℕ
  rank_strictMono : StrictMono rank
  cut : ℕ → ℕ
  clock_tendsto : Tendsto (fun index ↦
    QuittingAbsorptionPath.quittingRootSequenceClock
      (diagonal.completedRoots (limit.subsequence (rank index))) (cut index))
    atTop (nhds time)
  clock_succ_tendsto : Tendsto (fun index ↦
    QuittingAbsorptionPath.quittingRootSequenceClock
      (diagonal.completedRoots (limit.subsequence (rank index)))
        (cut index + 1)) atTop (nhds time)
  cumulative_tendsto : ∀ coalition, Tendsto (fun index ↦
    QuittingAbsorptionPath.quittingRootSequenceCumulativeCoalitionMass
      (diagonal.completedRoots (limit.subsequence (rank index)))
        (cut index) coalition) atTop
      (nhds (limit.path.value time coalition))

omit [Nonempty ι] in
/-- Every nonterminal path time has a shared adjacent source-cut
approximation.  The cut is the staircase inverse of the source CDF at the
fixed time; a controlled continuity point above the time bounds its next
clock. -/
theorem nonempty_chronologicalPathTimeAdjacentCutLimit
    (limit : diagonal.ChronologicalLimit) {time : ℝ}
    (htime : time ∈ QuittingAbsorptionPath.pathTimes limit.path)
    (htime_ne_one : time ≠ 1) :
    Nonempty (limit.ChronologicalPathTimeAdjacentCutLimit time) := by
  classical
  let distribution :=
    QuittingAbsorptionPath.chronologicalClockCDF limit.law
  have htime_lt_one : time < 1 :=
    lt_of_le_of_ne htime.1.2 htime_ne_one
  have hdistributionPath (point : ℝ) (hpoint : point ≤ 1) :
      QuittingAbsorptionPath.pathTotal limit.path point =
        distribution point := by
    exact
      QuittingAbsorptionPath.pathTotal_chronologicalCadlagPath_eq_chronologicalClockCDF
        limit.law hpoint
  have hfixed : distribution time = time := by
    rw [← hdistributionPath time htime.1.2]
    exact htime.2
  have hdomination (point : ℝ) (hpoint : point < 1) :
      point ≤ distribution point := by
    by_cases hpoint_nonneg : 0 ≤ point
    · rw [← hdistributionPath point hpoint.le]
      exact limit.le_pathTotal point ⟨hpoint_nonneg, hpoint.le⟩
    · exact (not_le.mp hpoint_nonneg).le.trans
        (ProbabilityTheory.cdf_nonneg _ point)
  have hcontinuousTime : ContinuousAt distribution time :=
    MathUE.HasClockGap.continuousAt_of_fixedPoint
      (ProbabilityTheory.monotone_cdf
        (QuittingAbsorptionPath.chronologicalClockLaw limit.law))
      (fun point ↦
        (ProbabilityTheory.cdf
          (QuittingAbsorptionPath.chronologicalClockLaw limit.law))
            |>.right_continuous point)
      hdomination htime_lt_one hfixed
  let controlled := Classical.choice <|
    MathUE.HasClockGap.nonempty_controlledRightSequence
      limit.hasClockGap_chronologicalClockCDF
      (ProbabilityTheory.monotone_cdf
        (QuittingAbsorptionPath.chronologicalClockLaw limit.law))
      (fun point ↦
        (ProbabilityTheory.cdf
          (QuittingAbsorptionPath.chronologicalClockLaw limit.law))
            |>.right_continuous point)
      hdomination
      (fun point ↦ ProbabilityTheory.cdf_le_one _ point)
      htime_lt_one hfixed
  let laws := fun rank : ℕ ↦
    diagonal.chronologicalLaw (limit.subsequence rank)
  let certificates := fun rank : ℕ ↦
    (diagonal.completion (limit.subsequence rank))
      |>.finiteAbsorptionCertificate
  have hfiniteClock (rank : ℕ) (point : ℝ) :
      QuittingAbsorptionPath.chronologicalClockCDF (laws rank) point =
        QuittingAbsorptionPath.pathTotal
          (certificates rank).cadlagPath point := by
    dsimp [laws, certificates,
      QuittingRootSequenceAbsorbingCompletionDiagonal.chronologicalLaw]
    rw [QuittingAbsorptionPath.chronologicalClockCDF_eq_clockEvent_real,
      chronologicalLaw_clockEvent_real_eq_pathTotal]
  have hfiniteCoalition (rank : ℕ) (point : ℝ)
      (hpoint : point ≤ 1)
      (coalition : {S : Finset ι // S.Nonempty}) :
      QuittingAbsorptionPath.chronologicalCoalitionCDF
          (laws rank) coalition point =
        (certificates rank).value point coalition := by
    dsimp [laws, certificates,
      QuittingRootSequenceAbsorbingCompletionDiagonal.chronologicalLaw]
    rw [QuittingAbsorptionPath.chronologicalCoalitionCDF_eq_clockCoalitionEvent_real
        _ _ hpoint,
      chronologicalLaw_clockCoalitionEvent_real_eq_value]
  let accuracy := fun index : ℕ ↦ (1 : ℝ) / ((index : ℝ) + 1)
  have haccuracy_pos (index : ℕ) : 0 < accuracy index := by
    dsimp [accuracy]
    positivity
  have hclockTime : Tendsto (fun rank ↦
      QuittingAbsorptionPath.chronologicalClockCDF (laws rank) time)
      atTop (nhds time) := by
    have h :=
      QuittingAbsorptionPath.tendsto_chronologicalClockCDF_of_continuousAt
        limit.law_tendsto hcontinuousTime
    simpa [laws, distribution, hfixed] using h
  have hsourceEventually (index : ℕ) : ∀ᶠ rank in atTop,
      QuittingAbsorptionPath.chronologicalClockCDF (laws rank) time <
          controlled.point index ∧
        |QuittingAbsorptionPath.chronologicalClockCDF (laws rank)
            (controlled.point index) -
          distribution (controlled.point index)| < accuracy index := by
    have hbelow := hclockTime.eventually_lt_const
      (controlled.point_mem index).1
    have hupper :=
      QuittingAbsorptionPath.tendsto_chronologicalClockCDF_of_continuousAt
        limit.law_tendsto (controlled.continuousAt index)
    have hnear := hupper.eventually
      (Metric.ball_mem_nhds _ (haccuracy_pos index))
    filter_upwards [hbelow, hnear] with rank hrank hnearRank
    exact ⟨hrank, by simpa only [Real.dist_eq] using hnearRank⟩
  obtain ⟨rank, hrank, hsource⟩ :=
    Filter.extraction_forall_of_eventually hsourceEventually
  let cuts : ∀ index,
      QuittingAbsorptionPath.QuittingFiniteCDFCut
        (certificates (rank index)) time (controlled.point index) :=
    fun index ↦ Classical.choice <|
      QuittingAbsorptionPath.nonempty_quittingFiniteCDFCut
        (certificates (rank index)) htime.1.1
        (controlled.point_mem index).1
        (by
          rw [← hfiniteClock]
          exact (hsource index).1)
        (controlled.point_mem index).2
  have hclock : Tendsto (fun index ↦
      QuittingAbsorptionPath.quittingRootSequenceClock
        (diagonal.completedRoots (limit.subsequence (rank index)))
          (cuts index).cut) atTop (nhds time) := by
    apply hclockTime.comp hrank.tendsto_atTop |>.congr'
    filter_upwards [] with index
    have heq := (cuts index).clock_eq
    change QuittingAbsorptionPath.chronologicalClockCDF
        (laws (rank index)) time =
      QuittingAbsorptionPath.quittingRootSequenceClock
        (diagonal.completedRoots (limit.subsequence (rank index)))
          (cuts index).cut
    rw [hfiniteClock]
    simpa [certificates,
      QuittingRootSequenceAbsorbingCompletionDiagonal.completedRoots,
      QuittingRootSequenceAbsorbingCompletionDiagonal.selectedRoots]
      using heq.symm
  have hlimitUpper : Tendsto (fun index ↦
      distribution (controlled.point index)) atTop (nhds time) := by
    have h := hcontinuousTime.tendsto.comp controlled.tendsto
    change Tendsto (distribution ∘ controlled.point) atTop (nhds time)
    simpa [hfixed] using h
  have haccuracy : Tendsto accuracy atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hsourceUpper : Tendsto (fun index ↦
      QuittingAbsorptionPath.chronologicalClockCDF (laws (rank index))
        (controlled.point index)) atTop (nhds time) := by
    have hdiff : Tendsto (fun index ↦
        QuittingAbsorptionPath.chronologicalClockCDF (laws (rank index))
            (controlled.point index) -
          distribution (controlled.point index)) atTop (nhds 0) := by
      rw [tendsto_zero_iff_abs_tendsto_zero]
      apply squeeze_zero
      · intro index
        exact abs_nonneg _
      · intro index
        exact (hsource index).2.le
      · exact haccuracy
    have hadd := hdiff.add hlimitUpper
    convert hadd using 1
    · funext index
      ring
    · simp
  have hclockSucc : Tendsto (fun index ↦
      QuittingAbsorptionPath.quittingRootSequenceClock
        (diagonal.completedRoots (limit.subsequence (rank index)))
          ((cuts index).cut + 1)) atTop (nhds time) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hclock hsourceUpper
    · intro index
      exact QuittingAbsorptionPath.monotone_quittingRootSequenceClock _
        (Nat.le_succ _)
    · intro index
      have hle := (cuts index).clock_succ_le_upperCDF
      change QuittingAbsorptionPath.quittingRootSequenceClock
          (diagonal.completedRoots (limit.subsequence (rank index)))
            ((cuts index).cut + 1) ≤
        QuittingAbsorptionPath.chronologicalClockCDF
          (laws (rank index)) (controlled.point index)
      rw [hfiniteClock]
      simpa [certificates,
        QuittingRootSequenceAbsorbingCompletionDiagonal.completedRoots,
        QuittingRootSequenceAbsorbingCompletionDiagonal.selectedRoots]
        using hle
  have hcumulative (coalition : {S : Finset ι // S.Nonempty}) :
      Tendsto (fun index ↦
        QuittingAbsorptionPath.quittingRootSequenceCumulativeCoalitionMass
          (diagonal.completedRoots (limit.subsequence (rank index)))
          (cuts index).cut coalition) atTop
        (nhds (limit.path.value time coalition)) := by
    have hcoordinate :=
      QuittingAbsorptionPath.tendsto_chronologicalCoalitionCDF_of_clockCDF_continuousAt
        limit.law_tendsto htime.1.2 hcontinuousTime coalition
    have hcoordinate' := hcoordinate.comp hrank.tendsto_atTop
    apply hcoordinate'.congr'
    filter_upwards [] with index
    have heq := (cuts index).cumulative_eq coalition
    change QuittingAbsorptionPath.chronologicalCoalitionCDF
        (laws (rank index)) coalition time =
      QuittingAbsorptionPath.quittingRootSequenceCumulativeCoalitionMass
        (diagonal.completedRoots (limit.subsequence (rank index)))
          (cuts index).cut coalition
    rw [hfiniteCoalition (rank index) time htime.1.2 coalition]
    simpa [certificates,
      QuittingRootSequenceAbsorbingCompletionDiagonal.completedRoots,
      QuittingRootSequenceAbsorbingCompletionDiagonal.selectedRoots]
      using heq.symm
  exact ⟨{
    rank := rank
    rank_strictMono := hrank
    cut := fun index ↦ (cuts index).cut
    clock_tendsto := hclock
    clock_succ_tendsto := hclockSucc
    cumulative_tendsto := hcumulative
  }⟩

/-- Cumulative coalition convergence at source cuts identifies their
conditional tail vectors with the continuation payoff of the decoded path. -/
theorem tailVector_tendsto_absorptionPathPayoff_of_cumulativeSubsequenceCuts
    (limit : diagonal.ChronologicalLimit) {time : ℝ}
    (htime : time ∈ QuittingAbsorptionPath.pathTimes limit.path)
    (htime_ne_one : time ≠ 1)
    (rank cut : ℕ → ℕ) (hrank : StrictMono rank)
    (hclock : Tendsto (fun index ↦
      QuittingAbsorptionPath.quittingRootSequenceClock
        (diagonal.completedRoots (limit.subsequence (rank index)))
          (cut index)) atTop (nhds time))
    (hcumulative : ∀ coalition, Tendsto (fun index ↦
      QuittingAbsorptionPath.quittingRootSequenceCumulativeCoalitionMass
        (diagonal.completedRoots (limit.subsequence (rank index)))
          (cut index) coalition) atTop
        (nhds (limit.path.value time coalition))) :
    Tendsto (fun index ↦
      quittingRootSequenceTailVector reward
        (diagonal.completedRoots (limit.subsequence (rank index)))
          (cut index)) atTop
      (nhds (QuittingAbsorptionPath.absorptionPathPayoff
        reward limit.absorptionPath time)) := by
  rw [tendsto_pi_nhds]
  intro who
  let roots : ℕ → ℕ → ι → PMF Bool := fun index ↦
    diagonal.completedRoots (limit.subsequence (rank index))
  let survival : ℕ → ℝ := fun index ↦
    QuittingAbsorptionPath.quittingRootSequenceSurvival
      (roots index) (cut index)
  let prefixPayoff : ℕ → ℝ := fun index ↦
    ∑ coalition,
      QuittingAbsorptionPath.quittingRootSequenceCumulativeCoalitionMass
        (roots index) (cut index) coalition * reward coalition who
  have hterminal : Tendsto (fun index ↦
      quittingRootSequenceTerminalValue reward (roots index) who 0)
      atTop (nhds (limit.payoff who)) := by
    have h := limit.completedTerminalPayoff_tendsto.comp
      hrank.tendsto_atTop
    simpa only [roots, Function.comp_apply,
      quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
      quittingProfileLiveRoot_quittingRootSequenceProfile_zero] using
        (tendsto_pi_nhds.mp h) who
  have hprefix : Tendsto prefixPayoff atTop
      (nhds (∑ coalition, limit.path.value time coalition *
        reward coalition who)) := by
    apply tendsto_finsetSum
    intro coalition _
    exact (hcumulative coalition).mul_const _
  have hsurvival : Tendsto survival atTop (nhds (1 - time)) := by
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa [survival, roots,
      QuittingAbsorptionPath.quittingRootSequenceClock] using hone.sub hclock
  have hsurvival_pos : ∀ᶠ index in atTop, 0 < survival index :=
    hsurvival.eventually (Ioi_mem_nhds (sub_pos.mpr <|
      lt_of_le_of_ne htime.1.2 htime_ne_one))
  have hquotient : Tendsto (fun index ↦
      (quittingRootSequenceTerminalValue reward (roots index) who 0 -
        prefixPayoff index) / survival index) atTop
      (nhds ((limit.payoff who -
        ∑ coalition, limit.path.value time coalition *
          reward coalition who) / (1 - time))) := by
    exact (hterminal.sub hprefix).div hsurvival
      (sub_ne_zero.mpr htime_ne_one.symm)
  have htail : Tendsto (fun index ↦
      quittingRootSequenceTailVector reward
        (roots index) (cut index) who) atTop
      (nhds ((limit.payoff who -
        ∑ coalition, limit.path.value time coalition *
          reward coalition who) / (1 - time))) := by
    apply hquotient.congr'
    filter_upwards [hsurvival_pos] with index hpositive
    have hdecomposition :=
      QuittingAbsorptionPath.quittingRootSequenceTerminalValue_eq_prefixReward_add_survival_mul_tail
        reward (roots index) who (cut index)
    dsimp only [prefixPayoff, survival]
    rw [div_eq_iff hpositive.ne']
    linarith
  convert htail using 1
  have htotal : QuittingAbsorptionPath.pathTotal limit.path time < 1 := by
    rw [htime.2]
    exact lt_of_le_of_ne htime.1.2 htime_ne_one
  congr 1
  rw [QuittingAbsorptionPath.absorptionPathPayoff, if_pos htime.1]
  change (if QuittingAbsorptionPath.pathTotal limit.path time < 1 then
    fun player ↦ (∑ coalition,
      (limit.path.value 1 coalition - limit.path.value time coalition) *
        reward coalition player) /
      (1 - QuittingAbsorptionPath.pathTotal limit.path time) else 0) who = _
  rw [if_pos htotal]
  have hendpoint : limit.payoff who =
      ∑ coalition, limit.path.value 1 coalition * reward coalition who := rfl
  have hdenom : 1 - QuittingAbsorptionPath.pathTotal limit.path time =
      1 - time := by
    rw [htime.2]
  rw [hdenom]
  congr 1
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  linarith

/-- The lower continuous-clock sequential-perfection clause for the actual
chronological source family. -/
theorem singletonReward_le_absorptionPathPayoff
    (limit : diagonal.ChronologicalLimit) (who : ι) {time : ℝ}
    (htime : time ∈ QuittingAbsorptionPath.pathTimes limit.path)
    (htime_ne_one : time ≠ 1) :
    reward (quittingSingletonTerminal who) who ≤
      QuittingAbsorptionPath.absorptionPathPayoff
        reward limit.absorptionPath time who := by
  let approximation := Classical.choice <|
    limit.nonempty_chronologicalPathTimeAdjacentCutLimit
      htime htime_ne_one
  let roots : ℕ → ℕ → ι → PMF Bool := fun index ↦
    diagonal.completedRoots
      (limit.subsequence (approximation.rank index))
  have htailVector :=
    limit.tailVector_tendsto_absorptionPathPayoff_of_cumulativeSubsequenceCuts
      htime htime_ne_one approximation.rank approximation.cut
      approximation.rank_strictMono approximation.clock_tendsto
      approximation.cumulative_tendsto
  have htail := (tendsto_pi_nhds.mp htailVector) who
  have hroot := tendsto_rootAbsorptionMass_zero_of_adjacentClocks
    roots approximation.cut
    (lt_of_le_of_ne htime.1.2 htime_ne_one)
    approximation.clock_tendsto approximation.clock_succ_tendsto
  have hopponent : Tendsto (fun index ↦
      quittingRootOpponentAbsorptionMass
        (roots index (approximation.cut index)) who) atTop (nhds 0) := by
    apply squeeze_zero
    · intro index
      exact quittingRootOpponentAbsorptionMass_nonneg _ who
    · intro index
      exact quittingRootOpponentAbsorptionMass_le_absorptionMass _ who
    · exact hroot
  exact quittingSingletonReward_le_of_reachedCuts
    reward roots
    (fun index ↦ diagonal.completedError
      (limit.subsequence (approximation.rank index)))
    (fun index ↦ diagonal.nash
      (limit.subsequence (approximation.rank index)))
    (diagonal.completedError_tendsto_zero.comp
      ((limit.subsequence_strictMono.comp approximation.rank_strictMono)
        |>.tendsto_atTop))
    approximation.cut who
    (lt_of_le_of_ne htime.1.2 htime_ne_one)
    approximation.clock_tendsto htail hopponent

end ChronologicalLimit

end QuittingRootSequenceAbsorbingCompletionDiagonal

end GameTheory

/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Order.Filter.AtTopBot.Basic
import UniformEquilibrium.Quitting.AbsorptionPath.ChronologicalMarkedRootSequenceJumpLimit
import UniformEquilibrium.Quitting.AbsorptionPath.RootSequenceAbsorbingCompletionChronologicalLimit

/-!
# Product-root jump realization for chronological absorbing-completion limits

At every nonterminal jump of a chronological absorbing-completion limit, one
shared subsequence of finite dominant stages has clocks converging to the jump,
simplex roots converging to one product root, and every coalition stage mass
converging to the corresponding path jump.  This proves product-root
realization at every jump of the decoded limit.

No assertion of singleton derivative support, sequential perfection, or a
bundled full absorption path is made here.
-/

noncomputable section

namespace GameTheory

open Filter Finset MeasureTheory Set StochasticGame
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

namespace QuittingRootSequenceAbsorbingCompletionDiagonal

variable
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {source : QuittingRootSequenceVanishingNashFamily reward}
    {diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source}

namespace ChronologicalLimit

/-- One shared finite-stage approximation of a nonterminal chronological
jump.  The same source ranks and stages work for every coalition coordinate. -/
structure ChronologicalJumpStageLimit
    (limit : diagonal.ChronologicalLimit) (time : ℝ) where
  rank : ℕ → ℕ
  rank_strictMono : StrictMono rank
  stage : ℕ → ℕ
  root : QuittingRootSimplex ι
  clock_tendsto : Tendsto (fun index ↦
    QuittingAbsorptionPath.quittingRootSequenceClock
      (diagonal.completedRoots (limit.subsequence (rank index)))
      (stage index)) atTop (nhds time)
  root_tendsto : Tendsto (fun index ↦ quittingSimplexOfRoot
    (diagonal.completedRoots (limit.subsequence (rank index))
      (stage index))) atTop (nhds root)
  stageCoalitionMass_tendsto : ∀ coalition,
    Tendsto (fun index ↦
      QuittingAbsorptionPath.quittingRootSequenceStageCoalitionMass
        (diagonal.completedRoots (limit.subsequence (rank index)))
        (stage index) coalition) atTop
      (nhds (QuittingAbsorptionPath.pathJump limit.path time coalition))
  preCumulativeMass_tendsto : ∀ coalition,
    Tendsto (fun index ↦
      QuittingAbsorptionPath.quittingRootSequenceCumulativeCoalitionMass
        (diagonal.completedRoots (limit.subsequence (rank index)))
        (stage index) coalition) atTop
      (nhds (limit.path.leftValue time coalition))
  postCumulativeMass_tendsto : ∀ coalition,
    Tendsto (fun index ↦
      QuittingAbsorptionPath.quittingRootSequenceCumulativeCoalitionMass
        (diagonal.completedRoots (limit.subsequence (rank index)))
        (stage index + 1) coalition) atTop
      (nhds (limit.path.value time coalition))

omit [Nonempty ι] in
/-- Clock domination rules out a jump at terminal clock one. -/
theorem pathJump_one_eq_zero
    (limit : diagonal.ChronologicalLimit)
    (coalition : {S : Finset ι // S.Nonempty}) :
    QuittingAbsorptionPath.pathJump limit.path 1 coalition = 0 := by
  exact QuittingAbsorptionPath.pathJump_chronologicalCadlagPath_one_eq_zero_of_clock_le_pathTotal
      limit.law limit.le_pathTotal coalition

omit [Nonempty ι] in
/-- Every nonterminal jump has a one-shared-subsequence dominant-stage
approximation. -/
theorem nonempty_chronologicalJumpStageLimit
    (limit : diagonal.ChronologicalLimit) {time : ℝ}
    (htime : time ∈ QuittingAbsorptionPath.pathJumps limit.path) :
    Nonempty (limit.ChronologicalJumpStageLimit time) := by
  classical
  obtain ⟨witness, hwitness_ne⟩ := htime.2
  have htime_le_one : time ≤ 1 := htime.1.2
  have hjumpFiber (coalition : {S : Finset ι // S.Nonempty}) :
      QuittingAbsorptionPath.pathJump limit.path time coalition =
        (limit.law : Measure
          (QuittingAbsorptionPath.QuittingChronologicalEvent reward)).real
          (QuittingAbsorptionPath.chronologicalClockCoalitionFiber
            time coalition) := by
    change QuittingAbsorptionPath.pathJump
      (QuittingAbsorptionPath.chronologicalCadlagPath limit.law)
        time coalition = _
    exact QuittingAbsorptionPath.pathJump_chronologicalCadlagPath_eq_clockCoalitionFiber_real
        limit.law time htime_le_one coalition
  have hwitness_nonneg :
      0 ≤ QuittingAbsorptionPath.pathJump limit.path time witness := by
    rw [hjumpFiber witness]
    exact ENNReal.toReal_nonneg
  have hwitness_pos :
      0 < QuittingAbsorptionPath.pathJump limit.path time witness :=
    lt_of_le_of_ne hwitness_nonneg (Ne.symm hwitness_ne)
  let windows := Classical.choice
    (QuittingAbsorptionPath.nonempty_chronologicalNullWindowSequence
      limit.law time)
  have hwidthEventually : ∀ᶠ windowRank in atTop,
      windows.upper windowRank - windows.lower windowRank <
        QuittingAbsorptionPath.pathJump limit.path time witness :=
    windows.width_tendsto_zero.eventually_lt_const hwitness_pos
  obtain ⟨firstWindow, hfirstWindow⟩ := eventually_atTop.mp hwidthEventually
  let windowRank := fun rank : ℕ ↦ firstWindow + rank
  have hwindowRank_strict : StrictMono windowRank := by
    intro first second hfirstSecond
    dsimp [windowRank]
    omega
  have hwindowRank_tendsto : Tendsto windowRank atTop atTop :=
    hwindowRank_strict.tendsto_atTop
  let laws := fun rank : ℕ ↦ diagonal.chronologicalLaw
    (limit.subsequence rank)
  let certificate := fun rank : ℕ ↦
    (diagonal.completion (limit.subsequence rank))
      |>.finiteAbsorptionCertificate
  have hfiber_subset_window (rank : ℕ) :
      QuittingAbsorptionPath.chronologicalClockCoalitionFiber
          (reward := reward) time witness ⊆
        QuittingAbsorptionPath.chronologicalOpenClockWindow
          (windows.lower (windowRank rank))
          (windows.upper (windowRank rank)) := by
    intro event hevent
    constructor
    · rw [hevent.1]
      exact windows.lower_lt_time (windowRank rank)
    · rw [hevent.1]
      exact windows.time_lt_upper (windowRank rank)
  have hlimitWindow (rank : ℕ) :
      windows.upper (windowRank rank) - windows.lower (windowRank rank) <
        (limit.law : Measure
          (QuittingAbsorptionPath.QuittingChronologicalEvent reward)).real
          (QuittingAbsorptionPath.chronologicalOpenClockWindow
            (windows.lower (windowRank rank))
            (windows.upper (windowRank rank))) := by
    have hwidth := hfirstWindow (windowRank rank) (by
      dsimp [windowRank]
      omega)
    apply hwidth.trans_le
    rw [hjumpFiber witness]
    unfold Measure.real
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    exact measure_mono (hfiber_subset_window rank)
  let accuracy := fun rank : ℕ ↦ (1 : ℝ) / ((rank : ℝ) + 1)
  have haccuracy_pos (rank : ℕ) : 0 < accuracy rank := by
    dsimp [accuracy]
    positivity
  have hsourceEventually (rank : ℕ) : ∀ᶠ sourceRank in atTop,
      windows.upper (windowRank rank) - windows.lower (windowRank rank) <
          (laws sourceRank : Measure
            (QuittingAbsorptionPath.QuittingChronologicalEvent reward)).real
            (QuittingAbsorptionPath.chronologicalOpenClockWindow
              (windows.lower (windowRank rank))
              (windows.upper (windowRank rank))) ∧
        (∀ coalition,
          |(laws sourceRank : Measure
              (QuittingAbsorptionPath.QuittingChronologicalEvent reward)).real
                (QuittingAbsorptionPath.chronologicalOpenClockCoalitionWindow
                  (windows.lower (windowRank rank))
                  (windows.upper (windowRank rank)) coalition) -
            (limit.law : Measure
              (QuittingAbsorptionPath.QuittingChronologicalEvent reward)).real
                (QuittingAbsorptionPath.chronologicalOpenClockCoalitionWindow
                  (windows.lower (windowRank rank))
                  (windows.upper (windowRank rank)) coalition)| < accuracy rank) ∧
        ∀ coalition,
          |QuittingAbsorptionPath.chronologicalCoalitionCDF
              (laws sourceRank) coalition (windows.lower (windowRank rank)) -
            QuittingAbsorptionPath.chronologicalCoalitionCDF
              limit.law coalition (windows.lower (windowRank rank))| <
            accuracy rank := by
    have htotal := (windows.tendsto_openClockWindow_real
      limit.law_tendsto (windowRank rank)).eventually_const_lt
        (hlimitWindow rank)
    have hcoalition : ∀ coalition,
        ∀ᶠ sourceRank in atTop,
          |(laws sourceRank : Measure
              (QuittingAbsorptionPath.QuittingChronologicalEvent reward)).real
                (QuittingAbsorptionPath.chronologicalOpenClockCoalitionWindow
                  (windows.lower (windowRank rank))
                  (windows.upper (windowRank rank)) coalition) -
            (limit.law : Measure
              (QuittingAbsorptionPath.QuittingChronologicalEvent reward)).real
                (QuittingAbsorptionPath.chronologicalOpenClockCoalitionWindow
                  (windows.lower (windowRank rank))
                  (windows.upper (windowRank rank)) coalition)| < accuracy rank := by
      intro coalition
      have hnear := (windows.tendsto_openClockCoalitionWindow_real
        limit.law_tendsto (windowRank rank) coalition).eventually
          (Metric.ball_mem_nhds _ (haccuracy_pos rank))
      simpa only [Real.dist_eq] using hnear
    rw [← Filter.eventually_all] at hcoalition
    have hlower : ∀ coalition,
        ∀ᶠ sourceRank in atTop,
          |QuittingAbsorptionPath.chronologicalCoalitionCDF
              (laws sourceRank) coalition (windows.lower (windowRank rank)) -
            QuittingAbsorptionPath.chronologicalCoalitionCDF
              limit.law coalition (windows.lower (windowRank rank))| <
            accuracy rank := by
      intro coalition
      have htendsto := windows.tendsto_chronologicalCoalitionCDF_at_lower
        limit.law_tendsto (windowRank rank)
        ((windows.lower_lt_time (windowRank rank)).le.trans htime.1.2)
        coalition
      have hnear := htendsto.eventually
        (Metric.ball_mem_nhds _ (haccuracy_pos rank))
      simpa only [Real.dist_eq] using hnear
    rw [← Filter.eventually_all] at hlower
    exact htotal.and (hcoalition.and hlower)
  obtain ⟨sourceRank, hsourceRank_strict, hsource⟩ :=
    Filter.extraction_forall_of_eventually hsourceEventually
  let dominant : ∀ rank,
      (certificate (sourceRank rank)).QuittingFiniteDominantClockWindowStage
        reward (windows.lower (windowRank rank))
          (windows.upper (windowRank rank)) := fun rank ↦ Classical.choice
        ((certificate (sourceRank rank))
          |>.exists_dominantClockWindowStage_of_width_lt_real
            (windows.lower_lt_upper (windowRank rank)) (hsource rank).1)
  let rootPoint := fun rank : ℕ ↦ quittingSimplexOfRoot
    (diagonal.completedRoots (limit.subsequence (sourceRank rank))
      (dominant rank).stage)
  obtain ⟨root, rootRank, hrootRank_strict, hrootTendsto⟩ :=
    CompactSpace.tendsto_subseq rootPoint
  let finalRank := sourceRank ∘ rootRank
  let finalStage := fun rank ↦ (dominant (rootRank rank)).stage
  have hclockTendsto : Tendsto (fun rank ↦
      QuittingAbsorptionPath.quittingRootSequenceClock
        (diagonal.completedRoots (limit.subsequence (finalRank rank)))
        (finalStage rank)) atTop (nhds time) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (windows.lower_tendsto.comp
        (hwindowRank_tendsto.comp hrootRank_strict.tendsto_atTop))
      (windows.upper_tendsto.comp
        (hwindowRank_tendsto.comp hrootRank_strict.tendsto_atTop))
    · intro rank
      exact (dominant (rootRank rank)).clock_mem.1.le
    · intro rank
      exact (dominant (rootRank rank)).clock_mem.2.le
  have hresidual (coalition : {S : Finset ι // S.Nonempty}) :
      Tendsto (fun rank ↦ (dominant (rootRank rank)).residual coalition)
        atTop (nhds 0) := by
    apply squeeze_zero
    · exact fun rank ↦ (dominant (rootRank rank)).residual_nonneg coalition
    · intro rank
      exact (Finset.single_le_sum
        (fun other _ ↦ (dominant (rootRank rank)).residual_nonneg other)
        (Finset.mem_univ coalition)).trans
          (dominant (rootRank rank)).sum_residual_lt_width.le
    · exact windows.width_tendsto_zero.comp
        (hwindowRank_tendsto.comp hrootRank_strict.tendsto_atTop)
  have haccuracy : Tendsto accuracy atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hsourceWindow (coalition : {S : Finset ι // S.Nonempty}) :
      Tendsto (fun rank ↦
        (laws (finalRank rank) : Measure
          (QuittingAbsorptionPath.QuittingChronologicalEvent reward)).real
          (QuittingAbsorptionPath.chronologicalOpenClockCoalitionWindow
            (windows.lower (windowRank (rootRank rank)))
            (windows.upper (windowRank (rootRank rank))) coalition)) atTop
        (nhds ((limit.law : Measure
          (QuittingAbsorptionPath.QuittingChronologicalEvent reward)).real
          (QuittingAbsorptionPath.chronologicalClockCoalitionFiber
            time coalition))) := by
    let limitWindow := fun rank ↦
      (limit.law : Measure
        (QuittingAbsorptionPath.QuittingChronologicalEvent reward)).real
        (QuittingAbsorptionPath.chronologicalOpenClockCoalitionWindow
          (windows.lower (windowRank (rootRank rank)))
          (windows.upper (windowRank (rootRank rank))) coalition)
    have hlimitWindowTendsto : Tendsto limitWindow atTop
        (nhds ((limit.law : Measure
          (QuittingAbsorptionPath.QuittingChronologicalEvent reward)).real
          (QuittingAbsorptionPath.chronologicalClockCoalitionFiber
            time coalition))) := by
      exact (windows.openClockCoalitionWindow_real_tendsto_fiber_real
        coalition).comp
          (hwindowRank_tendsto.comp hrootRank_strict.tendsto_atTop)
    have hdiff : Tendsto (fun rank ↦
        |(laws (finalRank rank) : Measure
          (QuittingAbsorptionPath.QuittingChronologicalEvent reward)).real
          (QuittingAbsorptionPath.chronologicalOpenClockCoalitionWindow
            (windows.lower (windowRank (rootRank rank)))
            (windows.upper (windowRank (rootRank rank))) coalition) -
          limitWindow rank|) atTop (nhds 0) := by
      apply squeeze_zero
      · exact fun _ ↦ abs_nonneg _
      · exact fun rank ↦ (hsource (rootRank rank)).2.1 coalition |>.le
      · exact haccuracy.comp hrootRank_strict.tendsto_atTop
    have hdifference : Tendsto (fun rank ↦
        (laws (finalRank rank) : Measure
          (QuittingAbsorptionPath.QuittingChronologicalEvent reward)).real
          (QuittingAbsorptionPath.chronologicalOpenClockCoalitionWindow
            (windows.lower (windowRank (rootRank rank)))
            (windows.upper (windowRank (rootRank rank))) coalition) -
          limitWindow rank) atTop (nhds 0) := by
      rw [tendsto_zero_iff_abs_tendsto_zero]
      simpa [Function.comp_def] using hdiff
    have hadd := hdifference.add hlimitWindowTendsto
    convert hadd using 1
    · funext rank
      ring
    · simp
  have hstageMass (coalition : {S : Finset ι // S.Nonempty}) :
      Tendsto (fun rank ↦
        QuittingAbsorptionPath.quittingRootSequenceStageCoalitionMass
          (diagonal.completedRoots (limit.subsequence (finalRank rank)))
          (finalStage rank) coalition) atTop
        (nhds (QuittingAbsorptionPath.pathJump limit.path time coalition)) := by
    have hmass := (hsourceWindow coalition).sub (hresidual coalition)
    rw [hjumpFiber coalition]
    have hmass' : Tendsto (fun rank ↦
        (laws (finalRank rank) : Measure
          (QuittingAbsorptionPath.QuittingChronologicalEvent reward)).real
          (QuittingAbsorptionPath.chronologicalOpenClockCoalitionWindow
            (windows.lower (windowRank (rootRank rank)))
            (windows.upper (windowRank (rootRank rank))) coalition) -
          (dominant (rootRank rank)).residual coalition) atTop
        (nhds ((limit.law : Measure
          (QuittingAbsorptionPath.QuittingChronologicalEvent reward)).real
          (QuittingAbsorptionPath.chronologicalClockCoalitionFiber
            time coalition))) := by
      simpa using hmass
    apply hmass'.congr'
    filter_upwards [] with rank
    have hdecomposition :=
      (dominant (rootRank rank)).window_eq_stage_add_residual coalition
    have hdecomposition' :
        (laws (finalRank rank) : Measure
          (QuittingAbsorptionPath.QuittingChronologicalEvent reward)).real
          (QuittingAbsorptionPath.chronologicalOpenClockCoalitionWindow
            (windows.lower (windowRank (rootRank rank)))
            (windows.upper (windowRank (rootRank rank))) coalition) =
          QuittingAbsorptionPath.quittingRootSequenceStageCoalitionMass
            (diagonal.completedRoots
              (limit.subsequence (finalRank rank)))
            (finalStage rank) coalition +
          (dominant (rootRank rank)).residual coalition := by
      simpa [laws, certificate, finalRank, finalStage,
        QuittingRootSequenceAbsorbingCompletionDiagonal.chronologicalLaw,
        QuittingRootSequenceAbsorbingCompletionDiagonal.completedRoots,
        QuittingRootSequenceAbsorbingCompletionDiagonal.selectedRoots] using
          hdecomposition
    linarith
  have hpreCumulative (coalition : {S : Finset ι // S.Nonempty}) :
      Tendsto (fun rank ↦
        QuittingAbsorptionPath.quittingRootSequenceCumulativeCoalitionMass
          (diagonal.completedRoots (limit.subsequence (finalRank rank)))
          (finalStage rank) coalition) atTop
        (nhds (limit.path.leftValue time coalition)) := by
    let limitLower := fun rank ↦
      QuittingAbsorptionPath.chronologicalCoalitionCDF limit.law coalition
        (windows.lower (windowRank (rootRank rank)))
    have hlowerWithin : Tendsto
        (fun rank ↦ windows.lower (windowRank (rootRank rank))) atTop
        (nhdsWithin time (Set.Iio time)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨windows.lower_tendsto.comp
          (hwindowRank_tendsto.comp hrootRank_strict.tendsto_atTop),
        Filter.Eventually.of_forall fun rank ↦
          windows.lower_lt_time (windowRank (rootRank rank))⟩
    have hlimitLower : Tendsto limitLower atTop
        (nhds (limit.path.leftValue time coalition)) := by
      have hleft := (ProbabilityTheory.monotone_cdf
        (QuittingAbsorptionPath.chronologicalCoalitionClockLaw
          limit.law coalition)).tendsto_leftLim time
      change Tendsto (fun rank ↦ ProbabilityTheory.cdf
          (QuittingAbsorptionPath.chronologicalCoalitionClockLaw
            limit.law coalition : Measure ℝ)
          (windows.lower (windowRank (rootRank rank)))) atTop
        (nhds (Function.leftLim (ProbabilityTheory.cdf
          (QuittingAbsorptionPath.chronologicalCoalitionClockLaw
            limit.law coalition : Measure ℝ)) time))
      exact hleft.comp hlowerWithin
    have hdiffAbs : Tendsto (fun rank ↦
        |QuittingAbsorptionPath.chronologicalCoalitionCDF
            (laws (finalRank rank)) coalition
              (windows.lower (windowRank (rootRank rank))) -
          limitLower rank|) atTop (nhds 0) := by
      apply squeeze_zero
      · exact fun _ ↦ abs_nonneg _
      · exact fun rank ↦ (hsource (rootRank rank)).2.2 coalition |>.le
      · exact haccuracy.comp hrootRank_strict.tendsto_atTop
    have hdiff : Tendsto (fun rank ↦
        QuittingAbsorptionPath.chronologicalCoalitionCDF
            (laws (finalRank rank)) coalition
              (windows.lower (windowRank (rootRank rank))) -
          limitLower rank) atTop (nhds 0) := by
      rw [tendsto_zero_iff_abs_tendsto_zero]
      simpa [Function.comp_def] using hdiffAbs
    have hsourceLower := hdiff.add hlimitLower
    have hsourceLower' : Tendsto (fun rank ↦
        QuittingAbsorptionPath.chronologicalCoalitionCDF
            (laws (finalRank rank)) coalition
              (windows.lower (windowRank (rootRank rank)))) atTop
        (nhds (limit.path.leftValue time coalition)) := by
      convert hsourceLower using 1
      · funext rank
        simp [limitLower]
      · simp
    have hsum := hsourceLower'.add (hresidual coalition)
    have hsum' : Tendsto (fun rank ↦
        QuittingAbsorptionPath.quittingRootSequenceCumulativeCoalitionMass
          (diagonal.completedRoots (limit.subsequence (finalRank rank)))
          (finalStage rank) coalition) atTop
        (nhds (limit.path.leftValue time coalition + 0)) := by
      apply hsum.congr'
      filter_upwards [] with rank
      exact (dominant (rootRank rank)).cumulative_eq_lowerCDF_add_residual
        coalition |>.symm
    simpa using hsum'
  have hpostCumulative (coalition : {S : Finset ι // S.Nonempty}) :
      Tendsto (fun rank ↦
        QuittingAbsorptionPath.quittingRootSequenceCumulativeCoalitionMass
          (diagonal.completedRoots (limit.subsequence (finalRank rank)))
          (finalStage rank + 1) coalition) atTop
        (nhds (limit.path.value time coalition)) := by
    have hadd := (hpreCumulative coalition).add (hstageMass coalition)
    have hadd' : Tendsto (fun rank ↦
        QuittingAbsorptionPath.quittingRootSequenceCumulativeCoalitionMass
          (diagonal.completedRoots (limit.subsequence (finalRank rank)))
          (finalStage rank + 1) coalition) atTop
        (nhds (limit.path.leftValue time coalition +
          QuittingAbsorptionPath.pathJump limit.path time coalition)) := by
      apply hadd.congr'
      filter_upwards [] with rank
      exact (QuittingAbsorptionPath.quittingRootSequenceCumulativeCoalitionMass_succ
        (diagonal.completedRoots (limit.subsequence (finalRank rank)))
        (finalStage rank) coalition).symm
    have hvalue : limit.path.leftValue time coalition +
        QuittingAbsorptionPath.pathJump limit.path time coalition =
        limit.path.value time coalition := by
      unfold QuittingAbsorptionPath.pathJump
      ring
    rwa [hvalue] at hadd'
  refine ⟨{
    rank := finalRank
    rank_strictMono := hsourceRank_strict.comp hrootRank_strict
    stage := finalStage
    root := root
    clock_tendsto := hclockTendsto
    root_tendsto := by
      simpa [rootPoint, finalRank, finalStage, Function.comp_def] using hrootTendsto
    stageCoalitionMass_tendsto := hstageMass
    preCumulativeMass_tendsto := hpreCumulative
    postCumulativeMass_tendsto := hpostCumulative
  }⟩

omit [Nonempty ι] in
/-- The product root recovered from a dominant-stage limit realizes every
normalized nonterminal jump coordinate. -/
theorem ChronologicalJumpStageLimit.jump_relation
    {limit : diagonal.ChronologicalLimit} {time : ℝ}
    (approximation : limit.ChronologicalJumpStageLimit time)
    (htime_lt_one : time < 1) (coalition : {S : Finset ι // S.Nonempty}) :
    QuittingAbsorptionPath.pathJump limit.path time coalition / (1 - time) =
      quittingRootCoalitionMass
        (quittingRootOfSimplex approximation.root) coalition.1 := by
  have hproduct : Tendsto (fun rank ↦
      (1 - QuittingAbsorptionPath.quittingRootSequenceClock
        (diagonal.completedRoots
          (limit.subsequence (approximation.rank rank)))
        (approximation.stage rank)) *
      quittingRootCoalitionMass
        (diagonal.completedRoots
          (limit.subsequence (approximation.rank rank))
          (approximation.stage rank)) coalition.1) atTop
      (nhds ((1 - time) * quittingRootCoalitionMass
        (quittingRootOfSimplex approximation.root) coalition.1)) := by
    apply (tendsto_const_nhds.sub approximation.clock_tendsto).mul
    simpa [Function.comp_def] using
      (continuous_quittingRootCoalitionMass_simplex coalition.1).continuousAt
        |>.tendsto.comp approximation.root_tendsto
  have hstage := approximation.stageCoalitionMass_tendsto coalition
  have hstageProduct : Tendsto (fun rank ↦
      QuittingAbsorptionPath.quittingRootSequenceStageCoalitionMass
        (diagonal.completedRoots
          (limit.subsequence (approximation.rank rank)))
        (approximation.stage rank) coalition) atTop
      (nhds ((1 - time) * quittingRootCoalitionMass
        (quittingRootOfSimplex approximation.root) coalition.1)) := by
    apply hproduct.congr'
    filter_upwards [] with rank
    exact (QuittingAbsorptionPath.quittingRootSequenceStageCoalitionMass_eq_one_sub_clock_mul
        (diagonal.completedRoots
          (limit.subsequence (approximation.rank rank)))
        (approximation.stage rank) coalition).symm
  have heq := tendsto_nhds_unique hstage hstageProduct
  rw [heq]
  field_simp [sub_ne_zero.mpr (Ne.symm htime_lt_one.ne)]

omit [Nonempty ι] in
/-- Every jump of the decoded chronological limit is realized by a product
root. -/
theorem everyPathJump_hasProductRoot
    (limit : diagonal.ChronologicalLimit) :
    ∀ time ∈ QuittingAbsorptionPath.pathJumps limit.path,
      ∃ root : ι → PMF Bool, ∀ coalition,
        QuittingAbsorptionPath.pathJump limit.path time coalition /
            (1 - time) =
          quittingRootCoalitionMass root coalition.1 := by
  intro time htime
  by_cases hterminal : time = 1
  · obtain ⟨coalition, hcoalition⟩ := htime.2
    rw [hterminal, limit.pathJump_one_eq_zero coalition] at hcoalition
    exact (hcoalition rfl).elim
  · have htime_lt_one : time < 1 :=
      lt_of_le_of_ne htime.1.2 hterminal
    let approximation := Classical.choice
      (limit.nonempty_chronologicalJumpStageLimit htime)
    exact ⟨quittingRootOfSimplex approximation.root,
      approximation.jump_relation htime_lt_one⟩

end ChronologicalLimit

end QuittingRootSequenceAbsorbingCompletionDiagonal

end GameTheory

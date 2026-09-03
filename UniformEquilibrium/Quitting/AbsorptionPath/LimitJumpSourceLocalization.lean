/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.PreviousBoundaryJumpLocalization

/-!
# Literal source localization at a weak-limit jump

At a fixed jump of a unit-bounded weak limit, choose continuity probes from
the right and diagonalize the source sequence at those probes. The last
source partition boundary before each probe is then a literal jump. Its time
and post-jump cumulative coordinates converge to the fixed limit jump.

This produces the moving source boundaries needed before passing the
normalized jump identity to a product-root limit. Product-root convergence is
added in the next layer.
-/

noncomputable section

namespace GameTheory.QuittingAbsorptionPath

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A fixed limit jump localized by literal source jumps along one strict
subsequence, before choosing a convergent subsequence of their product rows. -/
structure LimitJumpBoundarySubsequence
    (sequence : ℕ → AbsorptionPath (ι := ι))
    (limit : AbsorptionPath (ι := ι)) (time : ℝ) where
  limit_jump : time ∈ pathJumps limit.1
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  sourceTimes : ℕ → ℝ
  source_jump : ∀ index,
    sourceTimes index ∈ pathJumps (sequence (subsequence index)).1
  times_tendsto : Tendsto sourceTimes atTop (nhds time)
  values_tendsto : ∀ coalition,
    Tendsto (fun index ↦
      (sequence (subsequence index)).1.value (sourceTimes index) coalition)
      atTop (nhds (limit.1.value time coalition))

private def limitJumpLocalizationAccuracy (rank : ℕ) : ℝ :=
  1 / ((rank : ℝ) + 1)

private theorem limitJumpLocalizationAccuracy_pos (rank : ℕ) :
    0 < limitJumpLocalizationAccuracy rank := by
  unfold limitJumpLocalizationAccuracy
  positivity

private theorem limitJumpLocalizationAccuracy_tendsto_zero :
    Tendsto limitJumpLocalizationAccuracy atTop (nhds 0) := by
  unfold limitJumpLocalizationAccuracy
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- A jump time of a unit-bounded absorption path is strictly below clock
one. -/
theorem limitJump_lt_one_of_unitBoundedTotalMass
    (path : AbsorptionPath (ι := ι))
    (hbounded : HasUnitBoundedTotalMass path)
    {time : ℝ} (htime : time ∈ pathJumps path.1) :
    time < 1 := by
  exact (lt_pathTotal_of_mem_pathJumps path htime).trans_le
    (hbounded time htime.1)

/-- Unit-bounded weak convergence localizes one fixed limit jump by literal
source jumps along a strict subsequence, with convergent jump times and
post-jump cumulative coordinates. -/
theorem nonempty_limitJumpBoundarySubsequence_of_unitBoundedWeakLimit
    {sequence : ℕ → AbsorptionPath (ι := ι)}
    {limit : AbsorptionPath (ι := ι)}
    (hsourceBounded : ∀ index, HasUnitBoundedTotalMass (sequence index))
    (hlimitBounded : HasUnitBoundedTotalMass limit)
    (hweak : WeaklyConvergesAbsorptionPaths sequence limit)
    {time : ℝ} (htime : time ∈ pathJumps limit.1) :
    Nonempty (LimitJumpBoundarySubsequence sequence limit time) := by
  have htimeLtTotal : time < pathTotal limit.1 time :=
    lt_pathTotal_of_mem_pathJumps limit htime
  have htimeLtOne : time < 1 :=
    limitJump_lt_one_of_unitBoundedTotalMass limit hlimitBounded htime
  have hdense : Dense ((pathJumps limit.1)ᶜ) :=
    (countable_pathJumps limit.1).dense_compl ℝ
  obtain ⟨probe, _hprobeStrictAnti, hprobeMem, hprobeTendsto⟩ :=
    hdense.exists_seq_strictAnti_tendsto_of_lt htimeLtTotal
  have hprobeIcc (rank : ℕ) : probe rank ∈ Icc (0 : ℝ) 1 :=
    ⟨htime.1.1.trans (hprobeMem rank).1.1.le,
      (hprobeMem rank).1.2.le.trans
        (hlimitBounded time htime.1)⟩
  have hprobeWithin : Tendsto probe atTop
      (nhdsWithin time (Icc time 1)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hprobeTendsto, Filter.Eventually.of_forall fun rank ↦
      ⟨(hprobeMem rank).1.1.le, (hprobeIcc rank).2⟩⟩
  have hlimitProbeValue (coalition : {S : Finset ι // S.Nonempty}) :
      Tendsto (fun rank ↦ limit.1.value (probe rank) coalition) atTop
        (nhds (limit.1.value time coalition)) :=
    (limit.1.right_continuous coalition time htime.1).comp hprobeWithin
  have hsourceEventually : ∀ rank, ∀ᶠ sourceRank in atTop,
      probe rank < pathTotal (sequence sourceRank).1 (probe rank) ∧
        ∀ coalition,
          |(sequence sourceRank).1.value (probe rank) coalition -
            limit.1.value (probe rank) coalition| <
              limitJumpLocalizationAccuracy rank := by
    intro rank
    have hsourceTotal : Tendsto (fun sourceRank ↦
        pathTotal (sequence sourceRank).1 (probe rank)) atTop
        (nhds (pathTotal limit.1 (probe rank))) := by
      unfold pathTotal
      exact tendsto_finsetSum Finset.univ fun coalition _ ↦
        tendsto_pi_nhds.mp
          (hweak (probe rank) (hprobeIcc rank) (hprobeMem rank).2) coalition
    have hlimitTotal : pathTotal limit.1 time ≤
        pathTotal limit.1 (probe rank) :=
      monotoneOn_pathTotal limit.1 htime.1 (hprobeIcc rank)
        (hprobeMem rank).1.1.le
    have hprobeTotal : probe rank < pathTotal limit.1 (probe rank) :=
      (hprobeMem rank).1.2.trans_le hlimitTotal
    have htotalEventually : ∀ᶠ sourceRank in atTop,
        probe rank < pathTotal (sequence sourceRank).1 (probe rank) :=
      hsourceTotal.eventually_const_lt hprobeTotal
    have hcoordinateEventually : ∀ coalition,
        ∀ᶠ sourceRank in atTop,
          |(sequence sourceRank).1.value (probe rank) coalition -
            limit.1.value (probe rank) coalition| <
              limitJumpLocalizationAccuracy rank := by
      intro coalition
      have hcoordinate := tendsto_pi_nhds.mp
        (hweak (probe rank) (hprobeIcc rank) (hprobeMem rank).2) coalition
      have hnear := hcoordinate.eventually
        (Metric.ball_mem_nhds _ (limitJumpLocalizationAccuracy_pos rank))
      simpa only [Real.dist_eq] using hnear
    rw [← Filter.eventually_all] at hcoordinateEventually
    exact htotalEventually.and hcoordinateEventually
  obtain ⟨sourceRank, hsourceRankStrict, hsource⟩ :=
    Filter.extraction_forall_of_eventually hsourceEventually
  let sourceTimes := fun rank ↦
    previousPartitionBoundary (sequence (sourceRank rank)) (probe rank)
  have hsourceJumpAndValue (rank : ℕ) :
      sourceTimes rank ∈ pathJumps (sequence (sourceRank rank)).1 ∧
        ∀ coalition,
          (sequence (sourceRank rank)).1.value (sourceTimes rank) coalition =
            (sequence (sourceRank rank)).1.value (probe rank) coalition := by
    exact previousPartitionBoundary_mem_pathJumps_and_value_eq
      (sequence (sourceRank rank)) (hsourceBounded (sourceRank rank))
        (hprobeIcc rank) (hsource rank).1
  have hprobeSourceValue (coalition : {S : Finset ι // S.Nonempty}) :
      Tendsto (fun rank ↦
        (sequence (sourceRank rank)).1.value (probe rank) coalition) atTop
        (nhds (limit.1.value time coalition)) := by
    have herror : Tendsto (fun rank ↦
        (sequence (sourceRank rank)).1.value (probe rank) coalition -
          limit.1.value (probe rank) coalition) atTop (nhds 0) := by
      rw [tendsto_zero_iff_abs_tendsto_zero]
      apply squeeze_zero
      · exact fun _ ↦ abs_nonneg _
      · exact fun rank ↦ (hsource rank).2 coalition |>.le
      · exact limitJumpLocalizationAccuracy_tendsto_zero
    have hadd := herror.add (hlimitProbeValue coalition)
    convert hadd using 1
    · funext rank
      ring
    · simp
  have hsourceValue (coalition : {S : Finset ι // S.Nonempty}) :
      Tendsto (fun rank ↦
        (sequence (sourceRank rank)).1.value (sourceTimes rank) coalition)
        atTop (nhds (limit.1.value time coalition)) := by
    exact (hprobeSourceValue coalition).congr'
      (Filter.Eventually.of_forall fun rank ↦
        (hsourceJumpAndValue rank).2 coalition |>.symm)
  have hsourceTimesTendsto : Tendsto sourceTimes atTop (nhds time) := by
    apply tendsto_order.2
    constructor
    · intro lower hlower
      by_cases htimeZero : time = 0
      · subst time
        filter_upwards [] with rank
        exact hlower.trans_le
          (previousPartitionBoundary_mem_and_le
            (sequence (sourceRank rank)) (hprobeIcc rank)).2.1
      · have htimePos : 0 < time :=
          lt_of_le_of_ne htime.1.1 (Ne.symm htimeZero)
        have hlowerMax : max 0 lower < time :=
          max_lt htimePos hlower
        obtain ⟨leftProbe, hleftProbeNotJump, hleftProbeMem⟩ :=
          hdense.exists_between hlowerMax
        have hleftProbeIcc : leftProbe ∈ Icc (0 : ℝ) 1 :=
          ⟨(le_max_left 0 lower).trans hleftProbeMem.1.le,
            hleftProbeMem.2.le.trans htime.1.2⟩
        have hsourceLeftProbe : Tendsto (fun rank ↦
            (sequence (sourceRank rank)).1.value leftProbe
              (Classical.choose htime.2)) atTop
            (nhds (limit.1.value leftProbe (Classical.choose htime.2))) :=
          (tendsto_pi_nhds.mp
            (hweak leftProbe hleftProbeIcc hleftProbeNotJump)
              (Classical.choose htime.2)).comp hsourceRankStrict.tendsto_atTop
        have hjumpWitness := Classical.choose_spec htime.2
        have hleftBelow : limit.1.value leftProbe
            (Classical.choose htime.2) <
          limit.1.value time (Classical.choose htime.2) := by
          have hpre := limit.1.value_le_leftValue_of_lt
            (Classical.choose htime.2) hleftProbeIcc htime.1
              hleftProbeMem.2
          have hjumpPositive : 0 < pathJump limit.1 time
              (Classical.choose htime.2) :=
            lt_of_le_of_ne (pathJump_nonneg limit.1 htime.1 _)
              (Ne.symm hjumpWitness)
          unfold pathJump at hjumpPositive
          exact hpre.trans_lt (sub_pos.mp hjumpPositive)
        have heventuallyValue : ∀ᶠ rank in atTop,
            (sequence (sourceRank rank)).1.value leftProbe
                (Classical.choose htime.2) <
              (sequence (sourceRank rank)).1.value (sourceTimes rank)
                (Classical.choose htime.2) :=
          (hsourceLeftProbe.eventually_lt
            (hsourceValue (Classical.choose htime.2))) hleftBelow
        filter_upwards [heventuallyValue] with rank hvalueStrict
        have hleftBefore : leftProbe < sourceTimes rank := by
          by_contra hnot
          have htimeOrder : sourceTimes rank ≤ leftProbe := le_of_not_gt hnot
          have hmonotone := (sequence (sourceRank rank)).1.monotone
            (Classical.choose htime.2)
            (hsourceJumpAndValue rank).1.1 hleftProbeIcc htimeOrder
          exact (not_le_of_gt hvalueStrict) hmonotone
        exact (le_max_right 0 lower).trans_lt
          (hleftProbeMem.1.trans hleftBefore)
    · intro upper hupper
      filter_upwards [hprobeTendsto.eventually (Iio_mem_nhds hupper)]
        with rank hprobeUpper
      exact (previousPartitionBoundary_mem_and_le
        (sequence (sourceRank rank)) (hprobeIcc rank)).2.2.trans_lt hprobeUpper
  exact ⟨{
    limit_jump := htime
    subsequence := sourceRank
    subsequence_strictMono := hsourceRankStrict
    sourceTimes := sourceTimes
    source_jump := fun rank ↦ (hsourceJumpAndValue rank).1
    times_tendsto := hsourceTimesTendsto
    values_tendsto := hsourceValue
  }⟩

end GameTheory.QuittingAbsorptionPath

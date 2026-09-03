/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.LimitJumpSourceLocalization
import UniformEquilibrium.Quitting.AbsorptionPath.JumpSubsequenceWeakLimit
import UniformEquilibrium.Quitting.Root.SimplexCoalitionMass

/-!
# Product-root localization at weak-limit jumps

The canonical compactness argument is stated for an unbundled càdlàg
candidate. Existing bundled localization declarations are thin specializations.
-/

noncomputable section

namespace GameTheory.QuittingAbsorptionPath

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Literal source jumps and their product rows converging to a normalized
product root for one jump of an unbundled càdlàg limit. -/
structure CadlagLimitJumpRootApproximation
    (sequence : ℕ → AbsorptionPath (ι := ι))
    (limit : CadlagPath (ι := ι)) (time : ℝ) where
  limit_jump : time ∈ pathJumps limit
  root : ι → PMF Bool
  root_relation : ∀ coalition,
    pathJump limit time coalition / (1 - time) =
      quittingRootCoalitionMass root coalition.1
  sourceTimes : ℕ → ℝ
  source_jump : ∀ index,
    sourceTimes index ∈ pathJumps (sequence index).1
  times_tendsto : Tendsto sourceTimes atTop (nhds time)
  values_tendsto : ∀ coalition,
    Tendsto (fun index ↦
      (sequence index).1.value (sourceTimes index) coalition) atTop
      (nhds (limit.value time coalition))
  roots_tendsto : Tendsto (fun index ↦ quittingSimplexOfRoot
      (absorptionPathJumpRoot (sequence index) (sourceTimes index))) atTop
    (nhds (quittingSimplexOfRoot root))

private abbrev CadlagLimitJumpRootCompactState (player : Type)
    [Fintype player] :=
  ({coalition : Finset player // coalition.Nonempty} → Icc (0 : ℝ) 1) ×
    QuittingRootSimplex player

private def CadlagLimitJumpBoundarySubsequence.rootCompactState
    {sequence : ℕ → AbsorptionPath (ι := ι)}
    {limit : CadlagPath (ι := ι)} {time : ℝ}
    (data : CadlagLimitJumpBoundarySubsequence sequence limit time)
    (rank : ℕ) : CadlagLimitJumpRootCompactState ι :=
  (fun coalition ↦
    ⟨(sequence (data.subsequence rank)).1.leftValue
        (data.sourceTimes rank) coalition,
      by
        have htime := (data.source_jump rank).1
        constructor
        · calc
            0 = (sequence (data.subsequence rank)).1.leftValue 0
                coalition :=
              ((sequence (data.subsequence rank)).1.left_zero
                coalition).symm
            _ ≤ (sequence (data.subsequence rank)).1.leftValue
                (data.sourceTimes rank) coalition :=
              (sequence (data.subsequence rank)).1.leftValue_mono
                coalition (by norm_num) htime htime.1
        · exact
            ((sequence (data.subsequence rank)).1.leftValue_le_value
              coalition htime).trans
                ((sequence (data.subsequence rank)).1.value_mem
                  (data.sourceTimes rank) htime coalition).2⟩,
    quittingSimplexOfRoot
      (absorptionPathJumpRoot (sequence (data.subsequence rank))
        (data.sourceTimes rank)))

private theorem CadlagLimitJumpBoundarySubsequence.limitLeftValue_le_compactLimit
    {sequence : ℕ → AbsorptionPath (ι := ι)}
    {limit : CadlagPath (ι := ι)} {time : ℝ}
    (hweak : WeaklyConvergesAbsorptionPathsToCadlag sequence limit)
    (data : CadlagLimitJumpBoundarySubsequence sequence limit time)
    (compactLimit : CadlagLimitJumpRootCompactState ι)
    (further : ℕ → ℕ) (hfurther : StrictMono further)
    (hcompact : Tendsto (data.rootCompactState ∘ further) atTop
      (nhds compactLimit))
    (coalition : {coalition : Finset ι // coalition.Nonempty}) :
    limit.leftValue time coalition ≤ compactLimit.1 coalition := by
  have hleftTendsto : Tendsto (fun rank ↦
      (sequence (data.subsequence (further rank))).1.leftValue
        (data.sourceTimes (further rank)) coalition) atTop
      (nhds (compactLimit.1 coalition : ℝ)) := by
    have hcontinuous : Continuous
        (fun state : CadlagLimitJumpRootCompactState ι ↦
          (state.1 coalition : ℝ)) := by
      fun_prop
    simpa [Function.comp_def,
      CadlagLimitJumpBoundarySubsequence.rootCompactState] using
        (hcontinuous.tendsto compactLimit).comp hcompact
  by_cases htimeZero : time = 0
  · subst time
    rw [limit.left_zero]
    exact (compactLimit.1 coalition).property.1
  · have htimePos : 0 < time :=
      lt_of_le_of_ne data.limit_jump.1.1 (Ne.symm htimeZero)
    have hdense : Dense ((pathJumps limit)ᶜ) :=
      (countable_pathJumps limit).dense_compl ℝ
    obtain ⟨approach, _happroachStrict, happroachMem,
        happroachTendsto⟩ :=
      hdense.exists_seq_strictMono_tendsto_of_lt (α := ℝ) htimePos
    have happroachWithin : Tendsto approach atTop
        (nhdsWithin time (Icc (0 : ℝ) time \ {time})) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨happroachTendsto,
        Filter.Eventually.of_forall fun rank ↦
          ⟨⟨(happroachMem rank).1.1.le,
            (happroachMem rank).1.2.le⟩,
            (happroachMem rank).1.2.ne⟩⟩
    have hlimitApproach : Tendsto
        (fun rank ↦ limit.value (approach rank) coalition) atTop
        (nhds (limit.leftValue time coalition)) :=
      (limit.left_limit coalition time data.limit_jump.1).comp
        happroachWithin
    apply le_of_tendsto hlimitApproach
    filter_upwards [] with probeRank
    have hprobeIcc : approach probeRank ∈ Icc (0 : ℝ) 1 :=
      ⟨(happroachMem probeRank).1.1.le,
        (happroachMem probeRank).1.2.le.trans data.limit_jump.1.2⟩
    have hsourceAtProbe : Tendsto (fun rank ↦
        (sequence (data.subsequence (further rank))).1.value
          (approach probeRank) coalition) atTop
        (nhds (limit.value (approach probeRank) coalition)) := by
      exact (tendsto_pi_nhds.mp
        (hweak (approach probeRank) hprobeIcc
          (happroachMem probeRank).2) coalition).comp
            (data.subsequence_strictMono.comp hfurther).tendsto_atTop
    have hsourceTimes : Tendsto (data.sourceTimes ∘ further) atTop
        (nhds time) :=
      data.times_tendsto.comp hfurther.tendsto_atTop
    have hprobeBefore : ∀ᶠ rank in atTop,
        approach probeRank < data.sourceTimes (further rank) :=
      hsourceTimes.eventually_const_lt (happroachMem probeRank).1.2
    have hsourceLe : ∀ᶠ rank in atTop,
        (sequence (data.subsequence (further rank))).1.value
            (approach probeRank) coalition ≤
          (sequence (data.subsequence (further rank))).1.leftValue
            (data.sourceTimes (further rank)) coalition := by
      filter_upwards [hprobeBefore] with rank hbefore
      exact (sequence (data.subsequence (further rank))).1
        |>.value_le_leftValue_of_lt coalition hprobeIcc
          (data.source_jump (further rank)).1 hbefore
    exact le_of_tendsto_of_tendsto hsourceAtProbe hleftTendsto hsourceLe

private theorem CadlagLimitJumpBoundarySubsequence.compactLimit_leftValue_eq
    {sequence : ℕ → AbsorptionPath (ι := ι)}
    {limit : CadlagPath (ι := ι)} {time : ℝ}
    (hlimitLeft : pathLeftTotal limit time = time)
    (hweak : WeaklyConvergesAbsorptionPathsToCadlag sequence limit)
    (data : CadlagLimitJumpBoundarySubsequence sequence limit time)
    (compactLimit : CadlagLimitJumpRootCompactState ι)
    (further : ℕ → ℕ) (hfurther : StrictMono further)
    (hcompact : Tendsto (data.rootCompactState ∘ further) atTop
      (nhds compactLimit)) :
    ∀ coalition,
      (compactLimit.1 coalition : ℝ) = limit.leftValue time coalition := by
  have hleftTendsto (coalition : {coalition : Finset ι // coalition.Nonempty}) :
      Tendsto (fun rank ↦
        (sequence (data.subsequence (further rank))).1.leftValue
          (data.sourceTimes (further rank)) coalition) atTop
        (nhds (compactLimit.1 coalition : ℝ)) := by
    have hcontinuous : Continuous
        (fun state : CadlagLimitJumpRootCompactState ι ↦
          (state.1 coalition : ℝ)) := by
      fun_prop
    simpa [Function.comp_def,
      CadlagLimitJumpBoundarySubsequence.rootCompactState] using
        (hcontinuous.tendsto compactLimit).comp hcompact
  have hcompactTotal : Tendsto (fun rank ↦
      pathLeftTotal (sequence (data.subsequence (further rank))).1
        (data.sourceTimes (further rank))) atTop
      (nhds (∑ coalition, (compactLimit.1 coalition : ℝ))) := by
    unfold pathLeftTotal
    exact tendsto_finsetSum Finset.univ fun coalition _ ↦
      hleftTendsto coalition
  have hsourceTime : Tendsto (fun rank ↦
      pathLeftTotal (sequence (data.subsequence (further rank))).1
        (data.sourceTimes (further rank))) atTop (nhds time) := by
    exact (data.times_tendsto.comp hfurther.tendsto_atTop).congr'
      (Filter.Eventually.of_forall fun rank ↦
        (pathLeftTotal_eq_of_mem_pathJumps
          (sequence (data.subsequence (further rank)))
            (data.source_jump (further rank))).symm)
  have hcompactSum : (∑ coalition,
      (compactLimit.1 coalition : ℝ)) = time :=
    tendsto_nhds_unique hcompactTotal hsourceTime
  have hlimitSum : (∑ coalition,
      limit.leftValue time coalition) = time := by
    simpa only [pathLeftTotal] using hlimitLeft
  have hcoordinateLe (coalition : {coalition : Finset ι // coalition.Nonempty}) :
      limit.leftValue time coalition ≤ compactLimit.1 coalition :=
    data.limitLeftValue_le_compactLimit hweak compactLimit further
      hfurther hcompact coalition
  have hnonneg : ∀ coalition ∈
      (Finset.univ : Finset {coalition : Finset ι // coalition.Nonempty}),
      0 ≤ (compactLimit.1 coalition : ℝ) -
        limit.leftValue time coalition := by
    intro coalition _
    exact sub_nonneg.mpr (hcoordinateLe coalition)
  have hsumZero : (∑ coalition,
      ((compactLimit.1 coalition : ℝ) -
        limit.leftValue time coalition)) = 0 := by
    rw [Finset.sum_sub_distrib, hcompactSum, hlimitSum, sub_self]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsumZero
  intro coalition
  have := hzero coalition (Finset.mem_univ coalition)
  linarith

/-- Joint compactness of source pre-jump coordinates and product rows passes
the normalized product-root identity to a localized jump of an unbundled
càdlàg weak limit while retaining the convergent literal source data. -/
theorem CadlagLimitJumpBoundarySubsequence.exists_rootApproximation_subsequence
    {sequence : ℕ → AbsorptionPath (ι := ι)}
    {limit : CadlagPath (ι := ι)} {time : ℝ}
    (hlimitLeft : pathLeftTotal limit time = time)
    (htimeLtOne : time < 1)
    (hweak : WeaklyConvergesAbsorptionPathsToCadlag sequence limit)
    (data : CadlagLimitJumpBoundarySubsequence sequence limit time) :
    ∃ further : ℕ → ℕ, StrictMono further ∧
      Nonempty (CadlagLimitJumpRootApproximation
        ((sequence ∘ data.subsequence) ∘ further) limit time) := by
  obtain ⟨compactLimit, further, hfurther, hcompact⟩ :=
    CompactSpace.tendsto_subseq data.rootCompactState
  have hleftEq := data.compactLimit_leftValue_eq hlimitLeft hweak
    compactLimit further hfurther hcompact
  have hrootTendsto : Tendsto (fun rank ↦ quittingSimplexOfRoot
      (absorptionPathJumpRoot
        (sequence (data.subsequence (further rank)))
          (data.sourceTimes (further rank)))) atTop
      (nhds compactLimit.2) := by
    have hcontinuous : Continuous
        (fun state : CadlagLimitJumpRootCompactState ι ↦ state.2) := by
      fun_prop
    simpa [Function.comp_def,
      CadlagLimitJumpBoundarySubsequence.rootCompactState] using
        (hcontinuous.tendsto compactLimit).comp hcompact
  have hsourceLeftTendsto
      (coalition : {coalition : Finset ι // coalition.Nonempty}) :
      Tendsto (fun rank ↦
        (sequence (data.subsequence (further rank))).1.leftValue
          (data.sourceTimes (further rank)) coalition) atTop
        (nhds (limit.leftValue time coalition)) := by
    have hcontinuous : Continuous
        (fun state : CadlagLimitJumpRootCompactState ι ↦
          (state.1 coalition : ℝ)) := by
      fun_prop
    have hsource := (hcontinuous.tendsto compactLimit).comp hcompact
    rw [← hleftEq coalition]
    simpa [Function.comp_def,
      CadlagLimitJumpBoundarySubsequence.rootCompactState] using hsource
  have hrelation : ∀ coalition,
      pathJump limit time coalition / (1 - time) =
        quittingRootCoalitionMass
          (quittingRootOfSimplex compactLimit.2) coalition.1 := by
    intro coalition
    have hleftSide : Tendsto (fun rank ↦
        pathJump (sequence (data.subsequence (further rank))).1
            (data.sourceTimes (further rank)) coalition /
          (1 - data.sourceTimes (further rank))) atTop
        (nhds (pathJump limit time coalition / (1 - time))) := by
      unfold pathJump
      exact (((data.values_tendsto coalition).comp
          hfurther.tendsto_atTop).sub (hsourceLeftTendsto coalition)).div
            (tendsto_const_nhds.sub
              (data.times_tendsto.comp hfurther.tendsto_atTop))
                (sub_ne_zero.mpr htimeLtOne.ne')
    have hrightSide : Tendsto (fun rank ↦
        quittingRootCoalitionMass
          (absorptionPathJumpRoot
            (sequence (data.subsequence (further rank)))
              (data.sourceTimes (further rank))) coalition.1) atTop
        (nhds (quittingRootCoalitionMass
          (quittingRootOfSimplex compactLimit.2) coalition.1)) := by
      simpa [Function.comp_def] using
        (continuous_quittingRootCoalitionMass_simplex coalition.1
          |>.tendsto compactLimit.2).comp hrootTendsto
    have hrightAsLeft := hrightSide.congr'
      (Filter.Eventually.of_forall fun rank ↦
        (absorptionPathJumpRoot_relation
          (sequence (data.subsequence (further rank)))
            (data.source_jump (further rank)) coalition).symm)
    exact tendsto_nhds_unique hleftSide hrightAsLeft
  refine ⟨further, hfurther, ⟨{
    limit_jump := data.limit_jump
    root := quittingRootOfSimplex compactLimit.2
    root_relation := hrelation
    sourceTimes := data.sourceTimes ∘ further
    source_jump := fun rank ↦ ?_
    times_tendsto := data.times_tendsto.comp hfurther.tendsto_atTop
    values_tendsto := fun coalition ↦
      (data.values_tendsto coalition).comp hfurther.tendsto_atTop
    roots_tendsto := ?_
  }⟩⟩
  · simpa only [Function.comp_apply] using data.source_jump (further rank)
  · simpa only [Function.comp_apply,
      quittingSimplexOfRoot_rootOfSimplex] using hrootTendsto

/-- The retained source approximation in particular supplies one normalized
product root for the unbundled limit jump. -/
theorem CadlagLimitJumpBoundarySubsequence.exists_normalizedJumpRoot
    {sequence : ℕ → AbsorptionPath (ι := ι)}
    {limit : CadlagPath (ι := ι)} {time : ℝ}
    (hlimitLeft : pathLeftTotal limit time = time)
    (htimeLtOne : time < 1)
    (hweak : WeaklyConvergesAbsorptionPathsToCadlag sequence limit)
    (data : CadlagLimitJumpBoundarySubsequence sequence limit time) :
    ∃ root : ι → PMF Bool, ∀ coalition,
      pathJump limit time coalition / (1 - time) =
        quittingRootCoalitionMass root coalition.1 := by
  obtain ⟨_further, _hfurther, happroximation⟩ :=
    data.exists_rootApproximation_subsequence hlimitLeft htimeLtOne hweak
  let approximation := Classical.choice happroximation
  exact ⟨approximation.root, approximation.root_relation⟩

/-- Every jump of an unbundled unit-bounded weak limit with the absorption
clock and gap laws has a product root realizing its normalized jump law. -/
theorem everyJump_hasNormalizedRoot_of_unitBoundedWeakLimit
    {sequence : ℕ → AbsorptionPath (ι := ι)}
    {limit : CadlagPath (ι := ι)}
    (hclock : ∀ point ∈ Icc (0 : ℝ) 1, point ≤ pathTotal limit point)
    (hbound : ∀ point ∈ Icc (0 : ℝ) 1, pathTotal limit point ≤ 1)
    (hgap : MathUE.HasClockGapOn (pathTotal limit) (Icc 0 1))
    (hsourceBounded : ∀ index, HasUnitBoundedTotalMass (sequence index))
    (hweak : WeaklyConvergesAbsorptionPathsToCadlag sequence limit) :
    ∀ time ∈ pathJumps limit, ∃ root : ι → PMF Bool,
      ∀ coalition,
        pathJump limit time coalition / (1 - time) =
          quittingRootCoalitionMass root coalition.1 := by
  intro time htime
  have hlimitLeft : pathLeftTotal limit time = time :=
    pathLeftTotal_eq_time_of_jump_of_clockGap limit hclock hgap htime
  have htimeLtOne : time < 1 :=
    jump_time_lt_one_of_clockGap_and_unitBound
      limit hclock hbound hgap htime
  let data := Classical.choice
    (nonempty_cadlagLimitJumpBoundarySubsequence hbound
      hsourceBounded hweak htime hlimitLeft)
  exact data.exists_normalizedJumpRoot hlimitLeft htimeLtOne hweak


/-- Bundled root localization follows by specializing the retained càdlàg
source/root approximation and identifying its normalized root with the
selected root of the bundled limit. -/
theorem LimitJumpBoundarySubsequence.exists_sourceApproximation_subsequence
    {sequence : ℕ → AbsorptionPath (ι := ι)}
    {limit : AbsorptionPath (ι := ι)} {time : ℝ}
    (hlimitBounded : HasUnitBoundedTotalMass limit)
    (hweak : WeaklyConvergesAbsorptionPaths sequence limit)
    (data : LimitJumpBoundarySubsequence sequence limit time) :
    ∃ further : ℕ → ℕ, StrictMono further ∧
      Nonempty (LimitJumpSourceApproximation
        ((sequence ∘ data.subsequence) ∘ further) limit time) := by
  let cadlagData : CadlagLimitJumpBoundarySubsequence sequence limit.1 time := {
    limit_jump := data.limit_jump
    subsequence := data.subsequence
    subsequence_strictMono := data.subsequence_strictMono
    sourceTimes := data.sourceTimes
    source_jump := data.source_jump
    times_tendsto := data.times_tendsto
    values_tendsto := data.values_tendsto
  }
  have hlimitLeft : pathLeftTotal limit.1 time = time :=
    pathLeftTotal_eq_of_mem_pathJumps limit data.limit_jump
  have htimeLtOne : time < 1 :=
    (lt_pathTotal_of_mem_pathJumps limit data.limit_jump).trans_le
      (hlimitBounded time data.limit_jump.1)
  obtain ⟨further, hfurther, happroximation⟩ :=
    cadlagData.exists_rootApproximation_subsequence
      hlimitLeft htimeLtOne hweak
  let approximation := Classical.choice happroximation
  have hrootEq : approximation.root = absorptionPathJumpRoot limit time :=
    AbsorptionPathJumpRelation.eq approximation.root_relation
      (absorptionPathJumpRoot_relation limit data.limit_jump)
  refine ⟨further, hfurther, ⟨{
    limit_jump := data.limit_jump
    sourceTimes := approximation.sourceTimes
    source_jump := approximation.source_jump
    times_tendsto := approximation.times_tendsto
    values_tendsto := approximation.values_tendsto
    roots_tendsto := ?_
  }⟩⟩
  simpa only [cadlagData, Function.comp_assoc, hrootEq] using
    approximation.roots_tendsto

/-- Unit-bounded coordinatewise weak convergence supplies, for every limit
jump, a strict source subsequence whose literal jump times, cumulative
coordinates, and product rows converge to that limit jump. -/
theorem unitBoundedWeakLimitJumpSubsequenceLocalization :
    UnitBoundedWeakLimitJumpSubsequenceLocalization (ι := ι) := by
  intro sequence limit hsourceBounded hlimitBounded hweak time htime
  let data := Classical.choice
    (nonempty_limitJumpBoundarySubsequence_of_unitBoundedWeakLimit
      hsourceBounded hlimitBounded hweak htime)
  obtain ⟨further, hfurther, happroximation⟩ :=
    data.exists_sourceApproximation_subsequence hlimitBounded hweak
  exact ⟨data.subsequence ∘ further,
    data.subsequence_strictMono.comp hfurther, by
      simpa only [Function.comp_assoc] using happroximation⟩

/-- Weak-limit sequential-perfection closure holds when every source path and
the limit carry at most unit total mass. -/
theorem unitBoundedPlayerSequentialPerfectionClosedUnderWeakLimits
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    UnitBoundedPlayerSequentialPerfectionClosedUnderWeakLimits reward :=
  unitBoundedPlayerSequentialPerfectionClosedUnderWeakLimits_of_jumpSubsequenceLocalization
    unitBoundedWeakLimitJumpSubsequenceLocalization reward


end GameTheory.QuittingAbsorptionPath

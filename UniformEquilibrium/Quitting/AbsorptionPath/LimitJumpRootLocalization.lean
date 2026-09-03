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

After a fixed limit jump has been localized by literal source jumps, jointly
compactify their pre-jump cumulative coordinates and product rows. The
pre-jump coordinates are forced to the literal left limit: every continuity
probe from below gives a coordinatewise lower bound, while the source and
limit pre-jump totals both equal their jump times. Passing the normalized
jump identity to the limit then identifies the product-row limit with the
selected product root of the limit jump.

The construction may choose a different strict source subsequence for each
limit jump.  It proves weak-limit sequential-perfection closure, but it does
not provide a single common subsequence realizing every limit jump.
-/

noncomputable section

namespace GameTheory.QuittingAbsorptionPath

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private abbrev LimitJumpRootCompactState (ι : Type) [Fintype ι] :=
  ({S : Finset ι // S.Nonempty} → Set.Icc (0 : ℝ) 1) ×
    QuittingRootSimplex ι

private def LimitJumpBoundarySubsequence.rootCompactState
    {sequence : ℕ → AbsorptionPath (ι := ι)}
    {limit : AbsorptionPath (ι := ι)} {time : ℝ}
    (data : LimitJumpBoundarySubsequence sequence limit time)
    (rank : ℕ) : LimitJumpRootCompactState ι :=
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

private theorem LimitJumpBoundarySubsequence.limitLeftValue_le_compactLimit
    {sequence : ℕ → AbsorptionPath (ι := ι)}
    {limit : AbsorptionPath (ι := ι)} {time : ℝ}
    (hweak : WeaklyConvergesAbsorptionPaths sequence limit)
    (data : LimitJumpBoundarySubsequence sequence limit time)
    (compactLimit : LimitJumpRootCompactState ι)
    (further : ℕ → ℕ) (hfurther : StrictMono further)
    (hcompact : Tendsto (data.rootCompactState ∘ further) atTop
      (nhds compactLimit))
    (coalition : {S : Finset ι // S.Nonempty}) :
    limit.1.leftValue time coalition ≤ compactLimit.1 coalition := by
  have hleftTendsto : Tendsto (fun rank ↦
      (sequence (data.subsequence (further rank))).1.leftValue
        (data.sourceTimes (further rank)) coalition) atTop
      (nhds (compactLimit.1 coalition : ℝ)) := by
    have hcontinuous : Continuous
        (fun state : LimitJumpRootCompactState ι ↦
          (state.1 coalition : ℝ)) := by
      fun_prop
    simpa [Function.comp_def,
      LimitJumpBoundarySubsequence.rootCompactState] using
        (hcontinuous.tendsto compactLimit).comp hcompact
  by_cases htimeZero : time = 0
  · subst time
    rw [limit.1.left_zero]
    exact (compactLimit.1 coalition).property.1
  · have htimePos : 0 < time :=
      lt_of_le_of_ne data.limit_jump.1.1 (Ne.symm htimeZero)
    have hdense : Dense ((pathJumps limit.1)ᶜ) :=
      (countable_pathJumps limit.1).dense_compl ℝ
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
        (fun rank ↦ limit.1.value (approach rank) coalition) atTop
        (nhds (limit.1.leftValue time coalition)) :=
      (limit.1.left_limit coalition time data.limit_jump.1).comp
        happroachWithin
    apply le_of_tendsto hlimitApproach
    filter_upwards [] with probeRank
    have hprobeIcc : approach probeRank ∈ Icc (0 : ℝ) 1 :=
      ⟨(happroachMem probeRank).1.1.le,
        (happroachMem probeRank).1.2.le.trans data.limit_jump.1.2⟩
    have hsourceAtProbe : Tendsto (fun rank ↦
        (sequence (data.subsequence (further rank))).1.value
          (approach probeRank) coalition) atTop
        (nhds (limit.1.value (approach probeRank) coalition)) := by
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

private theorem LimitJumpBoundarySubsequence.compactLimit_leftValue_eq
    {sequence : ℕ → AbsorptionPath (ι := ι)}
    {limit : AbsorptionPath (ι := ι)} {time : ℝ}
    (hweak : WeaklyConvergesAbsorptionPaths sequence limit)
    (data : LimitJumpBoundarySubsequence sequence limit time)
    (compactLimit : LimitJumpRootCompactState ι)
    (further : ℕ → ℕ) (hfurther : StrictMono further)
    (hcompact : Tendsto (data.rootCompactState ∘ further) atTop
      (nhds compactLimit)) :
    ∀ coalition,
      (compactLimit.1 coalition : ℝ) =
        limit.1.leftValue time coalition := by
  have hleftTendsto (coalition : {S : Finset ι // S.Nonempty}) :
      Tendsto (fun rank ↦
        (sequence (data.subsequence (further rank))).1.leftValue
          (data.sourceTimes (further rank)) coalition) atTop
        (nhds (compactLimit.1 coalition : ℝ)) := by
    have hcontinuous : Continuous
        (fun state : LimitJumpRootCompactState ι ↦
          (state.1 coalition : ℝ)) := by
      fun_prop
    simpa [Function.comp_def,
      LimitJumpBoundarySubsequence.rootCompactState] using
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
      limit.1.leftValue time coalition) = time :=
    pathLeftTotal_eq_of_mem_pathJumps limit data.limit_jump
  have hcoordinateLe (coalition : {S : Finset ι // S.Nonempty}) :
      limit.1.leftValue time coalition ≤ compactLimit.1 coalition :=
    data.limitLeftValue_le_compactLimit hweak compactLimit further
      hfurther hcompact coalition
  have hnonneg : ∀ coalition ∈
      (Finset.univ : Finset {S : Finset ι // S.Nonempty}),
      0 ≤ (compactLimit.1 coalition : ℝ) -
        limit.1.leftValue time coalition := by
    intro coalition _
    exact sub_nonneg.mpr (hcoordinateLe coalition)
  have hsumZero : (∑ coalition,
      ((compactLimit.1 coalition : ℝ) -
        limit.1.leftValue time coalition)) = 0 := by
    rw [Finset.sum_sub_distrib, hcompactSum, hlimitSum, sub_self]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsumZero
  intro coalition
  have := hzero coalition (Finset.mem_univ coalition)
  linarith

/-- Joint compactness of pre-jump coordinates and product rows upgrades a
literal source-jump boundary subsequence to a full source approximation of
the limit jump along a further strict subsequence. -/
theorem LimitJumpBoundarySubsequence.exists_sourceApproximation_subsequence
    {sequence : ℕ → AbsorptionPath (ι := ι)}
    {limit : AbsorptionPath (ι := ι)} {time : ℝ}
    (hlimitBounded : HasUnitBoundedTotalMass limit)
    (hweak : WeaklyConvergesAbsorptionPaths sequence limit)
    (data : LimitJumpBoundarySubsequence sequence limit time) :
    ∃ further : ℕ → ℕ, StrictMono further ∧
      Nonempty (LimitJumpSourceApproximation
        ((sequence ∘ data.subsequence) ∘ further) limit time) := by
  obtain ⟨compactLimit, further, hfurther, hcompact⟩ :=
    CompactSpace.tendsto_subseq data.rootCompactState
  have hleftEq := data.compactLimit_leftValue_eq hweak compactLimit further
    hfurther hcompact
  have hrootTendsto : Tendsto (fun rank ↦ quittingSimplexOfRoot
      (absorptionPathJumpRoot
        (sequence (data.subsequence (further rank)))
          (data.sourceTimes (further rank)))) atTop
      (nhds compactLimit.2) := by
    have hcontinuous : Continuous
        (fun state : LimitJumpRootCompactState ι ↦ state.2) := by
      fun_prop
    simpa [Function.comp_def,
      LimitJumpBoundarySubsequence.rootCompactState] using
        (hcontinuous.tendsto compactLimit).comp hcompact
  have hsourceLeftTendsto
      (coalition : {S : Finset ι // S.Nonempty}) : Tendsto (fun rank ↦
        (sequence (data.subsequence (further rank))).1.leftValue
          (data.sourceTimes (further rank)) coalition) atTop
      (nhds (limit.1.leftValue time coalition)) := by
    have hcontinuous : Continuous
        (fun state : LimitJumpRootCompactState ι ↦
          (state.1 coalition : ℝ)) := by
      fun_prop
    have hsource := (hcontinuous.tendsto compactLimit).comp hcompact
    rw [← hleftEq coalition]
    simpa [Function.comp_def,
      LimitJumpBoundarySubsequence.rootCompactState] using hsource
  have htimeLtOne : time < 1 :=
    limitJump_lt_one_of_unitBoundedTotalMass limit hlimitBounded
      data.limit_jump
  have hrelation : AbsorptionPathJumpRelation limit time
      (quittingRootOfSimplex compactLimit.2) := by
    intro coalition
    have hleftSide : Tendsto (fun rank ↦
        pathJump (sequence (data.subsequence (further rank))).1
            (data.sourceTimes (further rank)) coalition /
          (1 - data.sourceTimes (further rank))) atTop
        (nhds (pathJump limit.1 time coalition / (1 - time))) := by
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
  have hrootEq : quittingRootOfSimplex compactLimit.2 =
      absorptionPathJumpRoot limit time :=
    AbsorptionPathJumpRelation.eq hrelation
      (absorptionPathJumpRoot_relation limit data.limit_jump)
  have hsimplexEq : compactLimit.2 =
      quittingSimplexOfRoot (absorptionPathJumpRoot limit time) := by
    rw [← hrootEq]
    exact (quittingSimplexOfRoot_rootOfSimplex compactLimit.2).symm
  refine ⟨further, hfurther, ⟨{
    limit_jump := data.limit_jump
    sourceTimes := data.sourceTimes ∘ further
    source_jump := fun rank ↦ ?_
    times_tendsto := data.times_tendsto.comp hfurther.tendsto_atTop
    values_tendsto := fun coalition ↦
      (data.values_tendsto coalition).comp hfurther.tendsto_atTop
    roots_tendsto := hsimplexEq ▸ hrootTendsto
  }⟩⟩
  simpa only [Function.comp_apply] using data.source_jump (further rank)

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

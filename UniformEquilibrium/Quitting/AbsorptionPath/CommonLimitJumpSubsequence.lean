/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.LimitJumpRootLocalization

/-!
# Uniform neighborhoods of weak-limit jumps

A convergent source realization of one limit jump eventually supplies a
literal source jump in every prescribed neighborhood of that limit jump.
Conversely, unit-bounded weak convergence supplies such a source jump in
every sufficiently late source path.  The latter statement upgrades the
existing subsequence localization by a contradiction-and-refinement argument.
-/

noncomputable section

namespace GameTheory.QuittingAbsorptionPath

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A literal jump of one source path whose time, post-jump cumulative
coordinates, and normalized product row lie within one common accuracy of a
specified time and limit row. -/
structure LimitJumpSourceNeighborhood
    (source limit : AbsorptionPath (ι := ι)) (time accuracy : ℝ) where
  sourceTime : ℝ
  source_jump : sourceTime ∈ pathJumps source.1
  time_close : dist sourceTime time < accuracy
  values_close : ∀ coalition,
    dist (source.1.value sourceTime coalition)
      (limit.1.value time coalition) < accuracy
  root_close : dist
    (quittingSimplexOfRoot (absorptionPathJumpRoot source sourceTime))
    (quittingSimplexOfRoot (absorptionPathJumpRoot limit time)) < accuracy

/-- A convergent literal source-jump realization eventually lies in every
positive neighborhood of the target jump. -/
theorem LimitJumpSourceApproximation.eventually_sourceNeighborhood
    {sequence : ℕ → AbsorptionPath (ι := ι)}
    {limit : AbsorptionPath (ι := ι)} {time accuracy : ℝ}
    (approximation : LimitJumpSourceApproximation sequence limit time)
    (haccuracy : 0 < accuracy) :
    ∀ᶠ index in atTop,
      Nonempty (LimitJumpSourceNeighborhood
        (sequence index) limit time accuracy) := by
  have htime := approximation.times_tendsto.eventually
    (Metric.ball_mem_nhds time haccuracy)
  have hvalues : ∀ coalition, ∀ᶠ index in atTop,
      dist ((sequence index).1.value (approximation.sourceTimes index)
        coalition) (limit.1.value time coalition) < accuracy := by
    intro coalition
    exact (approximation.values_tendsto coalition).eventually
      (Metric.ball_mem_nhds _ haccuracy)
  rw [← Filter.eventually_all] at hvalues
  have hroots := approximation.roots_tendsto.eventually
    (Metric.ball_mem_nhds _ haccuracy)
  filter_upwards [htime, hvalues, hroots] with index htime hvalues hroots
  exact ⟨{
    sourceTime := approximation.sourceTimes index
    source_jump := approximation.source_jump index
    time_close := htime
    values_close := hvalues
    root_close := hroots
  }⟩

/-- For a fixed jump of a unit-bounded weak limit and a fixed positive
accuracy, every sufficiently late source path contains a literal jump in the
corresponding time/value/product-row neighborhood. -/
theorem eventually_sourceNeighborhood_of_unitBoundedWeakLimit
    {sequence : ℕ → AbsorptionPath (ι := ι)}
    {limit : AbsorptionPath (ι := ι)}
    (hsourceBounded : ∀ index, HasUnitBoundedTotalMass (sequence index))
    (hlimitBounded : HasUnitBoundedTotalMass limit)
    (hweak : WeaklyConvergesAbsorptionPaths sequence limit)
    {time accuracy : ℝ} (htime : time ∈ pathJumps limit.1)
    (haccuracy : 0 < accuracy) :
    ∀ᶠ index in atTop,
      Nonempty (LimitJumpSourceNeighborhood
        (sequence index) limit time accuracy) := by
  by_contra hnot
  rw [Filter.not_eventually] at hnot
  obtain ⟨bad, hbadStrict, hbad⟩ := extraction_of_frequently_atTop hnot
  have hweakBad : WeaklyConvergesAbsorptionPaths
      (sequence ∘ bad) limit := by
    intro point hpoint hpointNotJump
    exact (hweak point hpoint hpointNotJump).comp hbadStrict.tendsto_atTop
  obtain ⟨further, hfurtherStrict, happroximation⟩ :=
    unitBoundedWeakLimitJumpSubsequenceLocalization
      (sequence ∘ bad) limit (fun index ↦ hsourceBounded (bad index))
        hlimitBounded hweakBad time htime
  let approximation := Classical.choice happroximation
  have hnear := approximation.eventually_sourceNeighborhood haccuracy
  obtain ⟨index, hnearIndex⟩ := hnear.exists
  exact hbad (further index) (by
    simpa only [Function.comp_apply] using hnearIndex)

private def commonLimitJumpAccuracy (rank : ℕ) : ℝ :=
  1 / ((rank : ℝ) + 1)

private theorem commonLimitJumpAccuracy_pos (rank : ℕ) :
    0 < commonLimitJumpAccuracy rank := by
  unfold commonLimitJumpAccuracy
  positivity

private theorem commonLimitJumpAccuracy_tendsto_zero :
    Tendsto commonLimitJumpAccuracy atTop (nhds 0) := by
  unfold commonLimitJumpAccuracy
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- Unit-bounded weak convergence admits one strict source subsequence on
which every limit jump has a convergent literal source-jump realization.
The source witnesses may depend on the limit jump, but the selected source
indices do not. -/
theorem exists_commonLimitJumpSourceApproximation_subsequence
    {sequence : ℕ → AbsorptionPath (ι := ι)}
    {limit : AbsorptionPath (ι := ι)}
    (hsourceBounded : ∀ index, HasUnitBoundedTotalMass (sequence index))
    (hlimitBounded : HasUnitBoundedTotalMass limit)
    (hweak : WeaklyConvergesAbsorptionPaths sequence limit) :
    ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
      WeaklyConvergesAbsorptionPaths (sequence ∘ subsequence) limit ∧
      HasSourceApproximationsForLimitJumps
        (sequence ∘ subsequence) limit := by
  by_cases hnoJumps : (pathJumps limit.1).Nonempty
  · obtain ⟨enumerate, henumerate⟩ :=
      Set.Countable.exists_surjective
        (s := pathJumps limit.1) hnoJumps (countable_pathJumps limit.1)
    have hneighborhoods (rank : ℕ) : ∀ᶠ index in atTop,
        ∀ jumpRank : Fin (rank + 1),
          Nonempty (LimitJumpSourceNeighborhood (sequence index) limit
            (enumerate jumpRank).1 (commonLimitJumpAccuracy rank)) := by
      apply Filter.eventually_all.mpr
      intro jumpRank
      exact eventually_sourceNeighborhood_of_unitBoundedWeakLimit
        hsourceBounded hlimitBounded hweak (enumerate jumpRank).2
          (commonLimitJumpAccuracy_pos rank)
    obtain ⟨subsequence, hsubsequenceStrict, hselected⟩ :=
      Filter.extraction_forall_of_eventually hneighborhoods
    have hweakSubsequence : WeaklyConvergesAbsorptionPaths
        (sequence ∘ subsequence) limit := by
      intro point hpoint hpointNotJump
      exact (hweak point hpoint hpointNotJump).comp
        hsubsequenceStrict.tendsto_atTop
    refine ⟨subsequence, hsubsequenceStrict, hweakSubsequence, ?_⟩
    intro time htime
    obtain ⟨jumpRank, hjumpRank⟩ := henumerate ⟨time, htime⟩
    let selectedRank : ∀ rank, Fin (rank + 1) := fun rank ↦
      if h : jumpRank < rank + 1 then ⟨jumpRank, h⟩ else ⟨0, by omega⟩
    let selected : ∀ rank, LimitJumpSourceNeighborhood
        (sequence (subsequence rank)) limit (enumerate (selectedRank rank)).1
          (commonLimitJumpAccuracy rank) := fun rank ↦
      Classical.choice (hselected rank (selectedRank rank))
    have hselectedRank (rank : ℕ) (hrank : jumpRank ≤ rank) :
        (selectedRank rank : ℕ) = jumpRank := by
      simp only [selectedRank, dif_pos (Nat.lt_succ_iff.mpr hrank)]
    have htarget (rank : ℕ) (hrank : jumpRank ≤ rank) :
        (enumerate (selectedRank rank)).1 = time := by
      rw [hselectedRank rank hrank]
      exact congrArg Subtype.val hjumpRank
    refine ⟨{
      limit_jump := htime
      sourceTimes := fun rank ↦ (selected rank).sourceTime
      source_jump := fun rank ↦ (selected rank).source_jump
      times_tendsto := ?_
      values_tendsto := ?_
      roots_tendsto := ?_
    }⟩
    · rw [Metric.tendsto_atTop]
      intro accuracy haccuracy
      have heventualAccuracy :=
        commonLimitJumpAccuracy_tendsto_zero.eventually
          (Iio_mem_nhds haccuracy)
      obtain ⟨threshold, hthreshold⟩ := Filter.eventually_atTop.mp
        ((eventually_ge_atTop jumpRank).and heventualAccuracy)
      refine ⟨threshold, fun rank hrank ↦ ?_⟩
      have hconditions := hthreshold rank hrank
      rw [← htarget rank hconditions.1]
      exact (selected rank).time_close.trans hconditions.2
    · intro coalition
      rw [Metric.tendsto_atTop]
      intro accuracy haccuracy
      have heventualAccuracy :=
        commonLimitJumpAccuracy_tendsto_zero.eventually
          (Iio_mem_nhds haccuracy)
      obtain ⟨threshold, hthreshold⟩ := Filter.eventually_atTop.mp
        ((eventually_ge_atTop jumpRank).and heventualAccuracy)
      refine ⟨threshold, fun rank hrank ↦ ?_⟩
      have hconditions := hthreshold rank hrank
      rw [← htarget rank hconditions.1]
      exact ((selected rank).values_close coalition).trans hconditions.2
    · rw [Metric.tendsto_atTop]
      intro accuracy haccuracy
      have heventualAccuracy :=
        commonLimitJumpAccuracy_tendsto_zero.eventually
          (Iio_mem_nhds haccuracy)
      obtain ⟨threshold, hthreshold⟩ := Filter.eventually_atTop.mp
        ((eventually_ge_atTop jumpRank).and heventualAccuracy)
      refine ⟨threshold, fun rank hrank ↦ ?_⟩
      have hconditions := hthreshold rank hrank
      rw [← htarget rank hconditions.1]
      exact (selected rank).root_close.trans hconditions.2
  ·
    refine ⟨id, strictMono_id, ?_, ?_⟩
    · simpa only [Function.comp_id] using hweak
    · intro time htime
      exact (hnoJumps ⟨time, htime⟩).elim

/-- Weak sequential compactness of unit-bounded absorption paths, before
retaining convergent literal source realizations of all limit jumps. -/
def UnitBoundedAbsorptionPathWeakSequentialCompactness : Prop :=
  ∀ sequence : ℕ → AbsorptionPath (ι := ι),
    (∀ index, HasUnitBoundedTotalMass (sequence index)) →
      ∃ (limit : AbsorptionPath (ι := ι)) (subsequence : ℕ → ℕ),
        StrictMono subsequence ∧
          HasUnitBoundedTotalMass limit ∧
          WeaklyConvergesAbsorptionPaths (sequence ∘ subsequence) limit

/-- Weak sequential compactness of unit-bounded absorption paths upgrades to
sequential compactness retaining one common source subsequence that realizes
every limit jump. -/
theorem unitBoundedAbsorptionPathSequentialCompactness_of_weakSequentialCompactness
    (hcompact : UnitBoundedAbsorptionPathWeakSequentialCompactness (ι := ι)) :
    UnitBoundedAbsorptionPathSequentialCompactness (ι := ι) := by
  intro sequence hsourceBounded
  obtain ⟨limit, firstSubsequence, hfirstStrict, hlimitBounded, hweak⟩ :=
    hcompact sequence hsourceBounded
  obtain ⟨secondSubsequence, hsecondStrict, hweakSecond, hjumps⟩ :=
    exists_commonLimitJumpSourceApproximation_subsequence
      (fun rank ↦ hsourceBounded (firstSubsequence rank))
        hlimitBounded hweak
  refine ⟨limit, firstSubsequence ∘ secondSubsequence,
    hfirstStrict.comp hsecondStrict, hlimitBounded, ?_, ?_⟩
  · simpa only [Function.comp_def] using hweakSecond
  · simpa only [Function.comp_def] using hjumps

end GameTheory.QuittingAbsorptionPath

/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.AKRSPartition

/-!
# Weak convergence of bounded absorption paths

This module records the cumulative-coordinate weak topology used for
absorption paths and the unit total-mass invariant needed to interpret the
coordinates as one subprobability law.  The invariant is deliberately
separate from `IsAbsorptionPath`: the latter currently contains the clock
lower bound but not this total-mass upper bound.
-/

noncomputable section

namespace GameTheory.QuittingAbsorptionPath

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every path-time total is at most one.  Together with the clock lower
bound in `IsAbsorptionPath`, this is the missing probability-mass part of the
unit-mass path invariant. -/
def HasUnitBoundedTotalMass (path : AbsorptionPath (ι := ι)) : Prop :=
  ∀ time ∈ Icc (0 : ℝ) 1, pathTotal path.1 time ≤ 1

/-- Coordinatewise weak convergence at every continuity point of an
unbundled càdlàg limit. -/
def WeaklyConvergesAbsorptionPathsToCadlag
    (sequence : ℕ → AbsorptionPath (ι := ι))
    (limit : CadlagPath (ι := ι)) : Prop :=
  ∀ time : ℝ, time ∈ Icc (0 : ℝ) 1 → time ∉ pathJumps limit →
    Tendsto (fun index coalition ↦ (sequence index).1.value time coalition)
      atTop (nhds fun coalition ↦ limit.value time coalition)

/-- Coordinatewise weak convergence at every continuity point of a bundled
absorption-path limit. -/
def WeaklyConvergesAbsorptionPaths
    (sequence : ℕ → AbsorptionPath (ι := ι))
    (limit : AbsorptionPath (ι := ι)) : Prop :=
  WeaklyConvergesAbsorptionPathsToCadlag sequence limit.1

/-- The existing bundled weak convergence predicate is definitionally the
specialization of unbundled weak convergence to the underlying càdlàg path. -/
theorem weaklyConvergesAbsorptionPathsToCadlag_iff
    (sequence : ℕ → AbsorptionPath (ι := ι))
    (limit : AbsorptionPath (ι := ι)) :
    WeaklyConvergesAbsorptionPathsToCadlag sequence limit.1 ↔
      WeaklyConvergesAbsorptionPaths sequence limit := by
  rfl


/-- A jump of a limit path is realized by jumps of its source paths.  The
source times, post-jump cumulative coordinates, and normalized product rows
all converge to their literal counterparts at the limit jump. -/
structure LimitJumpSourceApproximation
    (sequence : ℕ → AbsorptionPath (ι := ι))
    (limit : AbsorptionPath (ι := ι)) (time : ℝ) where
  limit_jump : time ∈ pathJumps limit.1
  sourceTimes : ℕ → ℝ
  source_jump : ∀ index,
    sourceTimes index ∈ pathJumps (sequence index).1
  times_tendsto : Tendsto sourceTimes atTop (nhds time)
  values_tendsto : ∀ coalition,
    Tendsto (fun index ↦
      (sequence index).1.value (sourceTimes index) coalition) atTop
      (nhds (limit.1.value time coalition))
  roots_tendsto : Tendsto (fun index ↦ quittingSimplexOfRoot
      (absorptionPathJumpRoot (sequence index) (sourceTimes index))) atTop
    (nhds (quittingSimplexOfRoot (absorptionPathJumpRoot limit time)))

/-- Every jump row of the limit has a convergent realization by literal jump
rows of the corresponding source paths.  This is the strengthened jump
conclusion needed in addition to coordinatewise weak convergence. -/
def HasSourceApproximationsForLimitJumps
    (sequence : ℕ → AbsorptionPath (ι := ι))
    (limit : AbsorptionPath (ι := ι)) : Prop :=
  ∀ time ∈ pathJumps limit.1,
    Nonempty (LimitJumpSourceApproximation sequence limit time)

/-- Corrected sequential-compactness surface for absorption paths carrying
unit-bounded total mass.  Besides a weakly convergent subsequence, it retains
the convergent source jump rows required by downstream sequential-perfection
closure. -/
def UnitBoundedAbsorptionPathSequentialCompactness : Prop :=
  ∀ sequence : ℕ → AbsorptionPath (ι := ι),
    (∀ index, HasUnitBoundedTotalMass (sequence index)) →
      ∃ (limit : AbsorptionPath (ι := ι)) (subsequence : ℕ → ℕ),
        StrictMono subsequence ∧
          HasUnitBoundedTotalMass limit ∧
          WeaklyConvergesAbsorptionPaths (sequence ∘ subsequence) limit ∧
          HasSourceApproximationsForLimitJumps
            (sequence ∘ subsequence) limit

/-- Playerwise sequential perfection is closed when both the path error and
the path itself converge.  This unrestricted property is false for the
current `AbsorptionPath` type because total endpoint mass is not bounded. -/
def PlayerSequentialPerfectionClosedUnderWeakLimits
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ (errors : ℕ → ℝ) (paths : ℕ → AbsorptionPath (ι := ι))
      (limit : AbsorptionPath (ι := ι)) (player : ι),
    (∀ index, 0 ≤ errors index) →
      Tendsto errors atTop (nhds 0) →
      WeaklyConvergesAbsorptionPaths paths limit →
      (∀ index,
        IsPlayerSequentiallyPerfectAbsorptionPath reward (paths index)
          player (errors index)) →
      IsPlayerSequentiallyPerfectAbsorptionPath reward limit player 0

/-- Closure property on paths whose cumulative total mass is literally
bounded by one, for every source path and for the limit. Source jump and
continuous-clock localization data are consequences rather than hypotheses
of this property. -/
def UnitBoundedPlayerSequentialPerfectionClosedUnderWeakLimits
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ (errors : ℕ → ℝ) (paths : ℕ → AbsorptionPath (ι := ι))
      (limit : AbsorptionPath (ι := ι)) (player : ι),
    (∀ index, HasUnitBoundedTotalMass (paths index)) →
      HasUnitBoundedTotalMass limit →
      (∀ index, 0 ≤ errors index) →
      Tendsto errors atTop (nhds 0) →
      WeaklyConvergesAbsorptionPaths paths limit →
      (∀ index,
        IsPlayerSequentiallyPerfectAbsorptionPath reward (paths index)
          player (errors index)) →
      IsPlayerSequentiallyPerfectAbsorptionPath reward limit player 0

/-- A unit-bounded absorption path has total mass exactly one at clock one. -/
theorem pathTotal_one_eq_one_of_unitBoundedTotalMass
    (path : AbsorptionPath (ι := ι))
    (hbounded : HasUnitBoundedTotalMass path) :
    pathTotal path.1 1 = 1 := by
  have hone : (1 : ℝ) ∈ Icc 0 1 := by norm_num
  exact le_antisymm (hbounded 1 hone) (path.property.1 1 hone)

/-- The left total of a unit-bounded absorption path is also one at clock
one. -/
theorem pathLeftTotal_one_eq_one_of_unitBoundedTotalMass
    (path : AbsorptionPath (ι := ι))
    (hbounded : HasUnitBoundedTotalMass path) :
    pathLeftTotal path.1 1 = 1 := by
  have hone : (1 : ℝ) ∈ Icc 0 1 := by norm_num
  apply le_antisymm
  · exact (pathLeftTotal_le_pathTotal path.1 hone).trans (hbounded 1 hone)
  · exact le_pathLeftTotal path hone

/-- Every coordinate of a unit-bounded absorption path is continuous from
the left at clock one. -/
theorem value_one_eq_leftValue_one_of_unitBoundedTotalMass
    (path : AbsorptionPath (ι := ι))
    (hbounded : HasUnitBoundedTotalMass path)
    (coalition : {S : Finset ι // S.Nonempty}) :
    path.1.value 1 coalition = path.1.leftValue 1 coalition := by
  have hone : (1 : ℝ) ∈ Icc 0 1 := by norm_num
  have hle := path.1.leftValue_le_value coalition hone
  apply le_antisymm
  · by_contra hnot
    have hstrict : path.1.leftValue 1 coalition <
        path.1.value 1 coalition := lt_of_not_ge hnot
    have hsumStrict : pathLeftTotal path.1 1 < pathTotal path.1 1 := by
      unfold pathLeftTotal pathTotal
      exact Finset.sum_lt_sum
        (fun other _ => path.1.leftValue_le_value other hone)
        ⟨coalition, Finset.mem_univ coalition, hstrict⟩
    rw [pathLeftTotal_one_eq_one_of_unitBoundedTotalMass path hbounded,
      pathTotal_one_eq_one_of_unitBoundedTotalMass path hbounded] at hsumStrict
    exact (lt_irrefl 1 hsumStrict).elim
  · exact hle

/-- Clock one is not a jump time of a unit-bounded absorption path. -/
theorem one_not_mem_pathJumps_of_unitBoundedTotalMass
    (path : AbsorptionPath (ι := ι))
    (hbounded : HasUnitBoundedTotalMass path) :
    1 ∉ pathJumps path.1 := by
  rintro ⟨_, coalition, hjump⟩
  apply hjump
  unfold pathJump
  rw [value_one_eq_leftValue_one_of_unitBoundedTotalMass path hbounded]
  exact sub_self _

/-- Weak convergence of unit-bounded paths includes literal convergence of
all endpoint cumulative coordinates. -/
theorem WeaklyConvergesAbsorptionPaths.tendsto_value_one
    {sequence : ℕ → AbsorptionPath (ι := ι)}
    {limit : AbsorptionPath (ι := ι)}
    (hbounded : HasUnitBoundedTotalMass limit)
    (hweak : WeaklyConvergesAbsorptionPaths sequence limit) :
    Tendsto (fun index coalition => (sequence index).1.value 1 coalition)
      atTop (𝓝 fun coalition => limit.1.value 1 coalition) :=
  hweak 1 (by norm_num) (one_not_mem_pathJumps_of_unitBoundedTotalMass
    limit hbounded)

/-- The path payoff is continuous when the terminal coordinates and the
coordinates at the evaluated source times converge to a nonterminal limit.
The source times may move; their membership in the clock interval is stated
literally. -/
theorem absorptionPathPayoff_tendsto_of_value_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {paths : ℕ → AbsorptionPath (ι := ι)}
    {limit : AbsorptionPath (ι := ι)}
    {times : ℕ → ℝ} {time : ℝ}
    (htimes : ∀ index, times index ∈ Icc (0 : ℝ) 1)
    (htime : time ∈ Icc (0 : ℝ) 1)
    (htotal : pathTotal limit.1 time < 1)
    (hendpoint : ∀ coalition,
      Tendsto (fun index ↦ (paths index).1.value 1 coalition) atTop
        (nhds (limit.1.value 1 coalition)))
    (hcurrent : ∀ coalition,
      Tendsto (fun index ↦ (paths index).1.value (times index) coalition)
        atTop (nhds (limit.1.value time coalition))) :
    Tendsto (fun index ↦
        absorptionPathPayoff reward (paths index) (times index))
      atTop (nhds (absorptionPathPayoff reward limit time)) := by
  rw [tendsto_pi_nhds]
  intro player
  have hcurrentTotal : Tendsto
      (fun index ↦ pathTotal (paths index).1 (times index)) atTop
      (nhds (pathTotal limit.1 time)) := by
    unfold pathTotal
    exact tendsto_finsetSum Finset.univ fun coalition _ ↦ hcurrent coalition
  have hnumerator : Tendsto (fun index ↦
      ∑ coalition,
        ((paths index).1.value 1 coalition -
          (paths index).1.value (times index) coalition) *
            reward coalition player) atTop
      (nhds (∑ coalition,
        (limit.1.value 1 coalition - limit.1.value time coalition) *
          reward coalition player)) := by
    apply tendsto_finsetSum
    intro coalition _
    exact ((hendpoint coalition).sub (hcurrent coalition)).mul_const _
  have hdenominator : Tendsto
      (fun index ↦ 1 - pathTotal (paths index).1 (times index)) atTop
      (nhds (1 - pathTotal limit.1 time)) :=
    tendsto_const_nhds.sub hcurrentTotal
  have hquotient := hnumerator.div hdenominator (by linarith)
  rw [absorptionPathPayoff, if_pos htime, if_pos htotal]
  apply hquotient.congr'
  have heventualTotal : ∀ᶠ index in atTop,
      pathTotal (paths index).1 (times index) < 1 :=
    hcurrentTotal.eventually (Iio_mem_nhds htotal)
  filter_upwards [heventualTotal] with index hsourceTotal
  simp only [absorptionPathPayoff, if_pos (htimes index),
    if_pos hsourceTotal]
  rfl

/-- At every nonjump, nonterminal clock time, weak convergence of paths to a
unit-bounded limit implies convergence of their continuation-payoff vectors. -/
theorem WeaklyConvergesAbsorptionPaths.absorptionPathPayoff_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {paths : ℕ → AbsorptionPath (ι := ι)}
    {limit : AbsorptionPath (ι := ι)}
    (hbounded : HasUnitBoundedTotalMass limit)
    (hweak : WeaklyConvergesAbsorptionPaths paths limit)
    {time : ℝ} (htime : time ∈ Icc (0 : ℝ) 1)
    (hnotJump : time ∉ pathJumps limit.1)
    (htotal : pathTotal limit.1 time < 1) :
    Tendsto (fun index ↦ absorptionPathPayoff reward (paths index) time)
      atTop (nhds (absorptionPathPayoff reward limit time)) := by
  apply absorptionPathPayoff_tendsto_of_value_tendsto reward
    (times := fun _ ↦ time) (time := time)
  · exact fun _ ↦ htime
  · exact htime
  · exact htotal
  · intro coalition
    exact (tendsto_pi_nhds.mp (hweak.tendsto_value_one hbounded)) coalition
  · intro coalition
    exact (tendsto_pi_nhds.mp (hweak time htime hnotJump)) coalition

/-- A moving source-time evaluation converges at a continuity time of the
unbundled limit when the source times approach that time from the right. -/
theorem WeaklyConvergesAbsorptionPathsToCadlag.value_tendsto_of_tendsto_fromAbove
    {paths : ℕ → AbsorptionPath (ι := ι)}
    {limit : CadlagPath (ι := ι)}
    (hweak : WeaklyConvergesAbsorptionPathsToCadlag paths limit)
    {times : ℕ → ℝ} {time : ℝ}
    (htime : time ∈ Icc (0 : ℝ) 1)
    (htimeOne : time ≠ 1)
    (hnotJump : time ∉ pathJumps limit)
    (htimes : ∀ index, times index ∈ Icc (0 : ℝ) 1)
    (hfromAbove : ∀ index, time ≤ times index)
    (htimesTendsto : Tendsto times atTop (nhds time))
    (coalition : {S : Finset ι // S.Nonempty}) :
    Tendsto (fun index ↦ (paths index).1.value (times index) coalition)
      atTop (nhds (limit.value time coalition)) := by
  apply tendsto_order.2
  constructor
  · intro lower hlower
    have hfixed := tendsto_pi_nhds.mp (hweak time htime hnotJump) coalition
    filter_upwards [hfixed.eventually (Ioi_mem_nhds hlower)] with index hindex
    exact hindex.trans_le <|
      (paths index).1.monotone coalition htime (htimes index)
        (hfromAbove index)
  · intro upper hupper
    have htimeLtOne : time < 1 := lt_of_le_of_ne htime.2 htimeOne
    have hdense : Dense ((pathJumps limit)ᶜ) :=
      (countable_pathJumps limit).dense_compl ℝ
    obtain ⟨probe, _hprobeStrictAnti, hprobeMem, hprobeTendsto⟩ :=
      hdense.exists_seq_strictAnti_tendsto_of_lt htimeLtOne
    have hprobeWithin : Tendsto probe atTop
        (nhdsWithin time (Icc time 1)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hprobeTendsto,
        Filter.Eventually.of_forall fun rank ↦
          ⟨(hprobeMem rank).1.1.le, (hprobeMem rank).1.2.le⟩⟩
    have hlimitProbe : Tendsto
        (fun rank ↦ limit.value (probe rank) coalition) atTop
        (nhds (limit.value time coalition)) :=
      (limit.right_continuous coalition time htime).comp hprobeWithin
    obtain ⟨rank, hrankUpper⟩ :=
      (hlimitProbe.eventually (Iio_mem_nhds hupper)).exists
    have htimesBefore : ∀ᶠ index in atTop, times index < probe rank :=
      htimesTendsto.eventually_lt_const (hprobeMem rank).1.1
    have hsourceProbe := tendsto_pi_nhds.mp
      (hweak (probe rank)
        ⟨htime.1.trans (hprobeMem rank).1.1.le,
          (hprobeMem rank).1.2.le⟩
        (hprobeMem rank).2) coalition
    have hsourceUpper : ∀ᶠ index in atTop,
        (paths index).1.value (probe rank) coalition < upper :=
      hsourceProbe.eventually_lt_const hrankUpper
    filter_upwards [htimesBefore, hsourceUpper] with index hbefore hsource
    exact ((paths index).1.monotone coalition (htimes index)
      ⟨htime.1.trans (hprobeMem rank).1.1.le,
        (hprobeMem rank).1.2.le⟩ hbefore.le).trans_lt hsource

/-- Bundled moving evaluation is the direct specialization of the unbundled theorem. -/
theorem WeaklyConvergesAbsorptionPaths.value_tendsto_of_tendsto_fromAbove
    {paths : ℕ → AbsorptionPath (ι := ι)}
    {limit : AbsorptionPath (ι := ι)}
    (hweak : WeaklyConvergesAbsorptionPaths paths limit)
    {times : ℕ → ℝ} {time : ℝ}
    (htime : time ∈ Icc (0 : ℝ) 1)
    (htimeOne : time ≠ 1)
    (hnotJump : time ∉ pathJumps limit.1)
    (htimes : ∀ index, times index ∈ Icc (0 : ℝ) 1)
    (hfromAbove : ∀ index, time ≤ times index)
    (htimesTendsto : Tendsto times atTop (nhds time))
    (coalition : {S : Finset ι // S.Nonempty}) :
    Tendsto (fun index ↦ (paths index).1.value (times index) coalition)
      atTop (nhds (limit.1.value time coalition)) := by
  exact WeaklyConvergesAbsorptionPathsToCadlag.value_tendsto_of_tendsto_fromAbove
    hweak htime htimeOne hnotJump htimes hfromAbove htimesTendsto coalition


end GameTheory.QuittingAbsorptionPath

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

/-- Coordinatewise weak convergence at every continuity point of the limit
path.  For unit-bounded absorption paths, clock one is automatically a
continuity point, so this predicate also sees terminal mass. -/
def WeaklyConvergesAbsorptionPaths
    (sequence : ℕ → AbsorptionPath (ι := ι))
    (limit : AbsorptionPath (ι := ι)) : Prop :=
  ∀ time : ℝ, time ∈ Icc (0 : ℝ) 1 → time ∉ pathJumps limit.1 →
    Tendsto (fun index coalition => (sequence index).1.value time coalition)
      atTop (𝓝 fun coalition => limit.1.value time coalition)

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

/-- Open target closure property on paths whose cumulative total mass is
literally bounded by one, for every source path and for the limit.  The source
jump and continuous-clock localization data used by checked intermediate
consumers are intended consequences of weak convergence and path geometry;
they are therefore proof obligations rather than hypotheses of this target. -/
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

end GameTheory.QuittingAbsorptionPath

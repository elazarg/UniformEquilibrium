/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.ContinuousClockActiveWeakLimit

/-!
# Jump localization through source subsequences

For closure at one fixed limit jump, a convergent realization is needed only
along one source subsequence.  This module states that weaker localization
surface and shows how it supplies the jump-row part of unit-bounded
weak-limit sequential-perfection closure.  The subsequence may depend on the
limit jump; this module does not assert one common subsequence realizing all
limit jumps simultaneously.
-/

noncomputable section

namespace GameTheory.QuittingAbsorptionPath

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every limit jump has a convergent literal realization along some strict
subsequence of the original source sequence.  The subsequence may depend on
the limit jump. -/
def HasSubsequenceSourceApproximationsForLimitJumps
    (sequence : ℕ → AbsorptionPath (ι := ι))
    (limit : AbsorptionPath (ι := ι)) : Prop :=
  ∀ time ∈ pathJumps limit.1,
    ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
      Nonempty (LimitJumpSourceApproximation
        (sequence ∘ subsequence) limit time)

/-- Unit-bounded weak convergence localizes each limit jump along a strict
source subsequence, which may depend on that jump. -/
def UnitBoundedWeakLimitJumpSubsequenceLocalization : Prop :=
  ∀ (sequence : ℕ → AbsorptionPath (ι := ι))
      (limit : AbsorptionPath (ι := ι)),
    (∀ index, HasUnitBoundedTotalMass (sequence index)) →
      HasUnitBoundedTotalMass limit →
        WeaklyConvergesAbsorptionPaths sequence limit →
          HasSubsequenceSourceApproximationsForLimitJumps sequence limit

/-- One limit jump is exactly player-perfect when it has a convergent literal
source realization and the source errors vanish. -/
theorem playerJumpRowPerfect_of_sourceApproximation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (errors : ℕ → ℝ) (paths : ℕ → AbsorptionPath (ι := ι))
    (limit : AbsorptionPath (ι := ι)) (player : ι)
    (hlimitBounded : HasUnitBoundedTotalMass limit)
    (herrors : Tendsto errors atTop (nhds 0))
    (hweak : WeaklyConvergesAbsorptionPaths paths limit)
    {time : ℝ} (htime : time ∈ pathJumps limit.1)
    (htotal : pathTotal limit.1 time < 1)
    (approximation : LimitJumpSourceApproximation paths limit time)
    (hperfect : ∀ index,
      IsPlayerSequentiallyPerfectAbsorptionPath reward (paths index)
        player (errors index)) :
    QuittingPlayerRowεPerfect reward
      (absorptionPathPayoff reward limit time)
      (absorptionPathJumpRoot limit time) player 0 := by
  have hsourceTotal : Tendsto (fun index ↦
      pathTotal (paths index).1 (approximation.sourceTimes index)) atTop
      (nhds (pathTotal limit.1 time)) := by
    unfold pathTotal
    exact tendsto_finsetSum Finset.univ fun coalition _ ↦
      approximation.values_tendsto coalition
  have hsourceNonterminal : ∀ᶠ index in atTop,
      pathTotal (paths index).1 (approximation.sourceTimes index) < 1 :=
    hsourceTotal.eventually (Iio_mem_nhds htotal)
  have hpayoff : Tendsto (fun index ↦
      absorptionPathPayoff reward (paths index)
        (approximation.sourceTimes index)) atTop
      (nhds (absorptionPathPayoff reward limit time)) := by
    apply absorptionPathPayoff_tendsto_of_value_tendsto reward
      (times := approximation.sourceTimes) (time := time)
    · exact fun index ↦ (approximation.source_jump index).1
    · exact htime.1
    · exact htotal
    · intro coalition
      exact (tendsto_pi_nhds.mp
        (hweak.tendsto_value_one hlimitBounded)) coalition
    · exact approximation.values_tendsto
  rw [← quittingRootOfSimplex_simplexOfRoot
    (absorptionPathJumpRoot limit time)]
  apply quittingPlayerRowεPerfect_of_tendsto reward player errors
    (fun index ↦ absorptionPathPayoff reward (paths index)
      (approximation.sourceTimes index))
    (fun index ↦ quittingSimplexOfRoot
      (absorptionPathJumpRoot (paths index) (approximation.sourceTimes index)))
    herrors hpayoff approximation.roots_tendsto
  filter_upwards [hsourceNonterminal] with index hnonterminal
  rw [quittingRootOfSimplex_simplexOfRoot]
  exact (hperfect index).1 (approximation.sourceTimes index)
    (approximation.source_jump index) hnonterminal

/-- Jump-row perfection survives when each limit jump is realized along its
own strict source subsequence. -/
theorem playerJumpRowsPerfect_of_subsequenceSourceApproximatedWeakLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (errors : ℕ → ℝ) (paths : ℕ → AbsorptionPath (ι := ι))
    (limit : AbsorptionPath (ι := ι)) (player : ι)
    (hlimitBounded : HasUnitBoundedTotalMass limit)
    (herrors : Tendsto errors atTop (nhds 0))
    (hweak : WeaklyConvergesAbsorptionPaths paths limit)
    (hjumps : HasSubsequenceSourceApproximationsForLimitJumps paths limit)
    (hperfect : ∀ index,
      IsPlayerSequentiallyPerfectAbsorptionPath reward (paths index)
        player (errors index)) :
    ∀ time ∈ pathJumps limit.1, pathTotal limit.1 time < 1 →
      QuittingPlayerRowεPerfect reward
        (absorptionPathPayoff reward limit time)
        (absorptionPathJumpRoot limit time) player 0 := by
  intro time htime htotal
  obtain ⟨subsequence, hsubsequence, happroximation⟩ :=
    hjumps time htime
  let approximation := Classical.choice happroximation
  have hsubsequenceAtTop : Tendsto subsequence atTop atTop :=
    hsubsequence.tendsto_atTop
  have hweakSubsequence : WeaklyConvergesAbsorptionPaths
      (paths ∘ subsequence) limit := by
    intro point hpoint hpointNotJump
    exact (hweak point hpoint hpointNotJump).comp hsubsequenceAtTop
  exact playerJumpRowPerfect_of_sourceApproximation reward
    (errors ∘ subsequence) (paths ∘ subsequence) limit player
    hlimitBounded (herrors.comp hsubsequenceAtTop) hweakSubsequence htime
    htotal approximation (fun index ↦ hperfect (subsequence index))

/-- Subsequence-localized jump rows and plain weak convergence together close
the complete playerwise sequential-perfection predicate. -/
theorem playerSequentiallyPerfect_of_subsequenceSourceApproximatedUnitBoundedWeakLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (errors : ℕ → ℝ) (paths : ℕ → AbsorptionPath (ι := ι))
    (limit : AbsorptionPath (ι := ι)) (player : ι)
    (hsourceBounded : ∀ index, HasUnitBoundedTotalMass (paths index))
    (hlimitBounded : HasUnitBoundedTotalMass limit)
    (herrors : Tendsto errors atTop (nhds 0))
    (hweak : WeaklyConvergesAbsorptionPaths paths limit)
    (hjumps : HasSubsequenceSourceApproximationsForLimitJumps paths limit)
    (hperfect : ∀ index,
      IsPlayerSequentiallyPerfectAbsorptionPath reward (paths index)
        player (errors index)) :
    IsPlayerSequentiallyPerfectAbsorptionPath reward limit player 0 := by
  refine ⟨playerJumpRowsPerfect_of_subsequenceSourceApproximatedWeakLimit
    reward errors paths limit player hlimitBounded herrors hweak hjumps
    hperfect, ?_⟩
  intro time htime htimeOne
  constructor
  · simpa using
      playerContinuousClockLowerBound_of_unitBoundedWeakLimit reward errors
        paths limit player hsourceBounded hlimitBounded herrors hweak hperfect
        time htime htimeOne
  · intro hderivative
    simpa using
      playerContinuousClockUpperBound_of_unitBoundedWeakLimit reward errors
        paths limit player hsourceBounded hlimitBounded herrors hweak hperfect
        time htime htimeOne hderivative

/-- Jump-subsequence localization implies unit-bounded weak-limit
sequential-perfection closure for every reward table. -/
theorem unitBoundedPlayerSequentialPerfectionClosedUnderWeakLimits_of_jumpSubsequenceLocalization
    (hlocalization : UnitBoundedWeakLimitJumpSubsequenceLocalization (ι := ι))
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    UnitBoundedPlayerSequentialPerfectionClosedUnderWeakLimits reward := by
  intro errors paths limit player hsourceBounded hlimitBounded _herrorsNonneg
    herrors hweak hperfect
  exact
    playerSequentiallyPerfect_of_subsequenceSourceApproximatedUnitBoundedWeakLimit
      reward errors paths limit player hsourceBounded hlimitBounded herrors
      hweak (hlocalization paths limit hsourceBounded hlimitBounded hweak)
      hperfect

end GameTheory.QuittingAbsorptionPath

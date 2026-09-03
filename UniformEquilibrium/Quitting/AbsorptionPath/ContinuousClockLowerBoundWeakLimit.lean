/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.ClockBoundarySourceApproximation
import UniformEquilibrium.Quitting.Classification.Existence.RowPerfectionClosed

/-!
# Lower continuous-clock perfection under bounded weak limits

At a nonterminal clock time of a unit-bounded weak limit, source path totals
give literal partition boundaries.  Clock boundaries use the source path's
continuous lower inequality.  Jump boundaries use its row inequality, and
their normalized product rows vanish to all-Continue.  These two cases combine
without selecting one case uniformly across source indices.
-/

noncomputable section

namespace GameTheory.QuittingAbsorptionPath

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem limitClockTime_total_lt_one
    {limit : AbsorptionPath (ι := ι)} {time : ℝ}
    (htime : time ∈ pathTimes limit.1) (htimeOne : time ≠ 1) :
    pathTotal limit.1 time < 1 := by
  rw [htime.2]
  exact lt_of_le_of_ne htime.1.2 htimeOne

theorem LimitClockBoundarySourceApproximation.payoff_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {paths : ℕ → AbsorptionPath (ι := ι)}
    {limit : AbsorptionPath (ι := ι)} {time : ℝ}
    (approximation : LimitClockBoundarySourceApproximation paths limit time)
    (hlimitBounded : HasUnitBoundedTotalMass limit)
    (hweak : WeaklyConvergesAbsorptionPaths paths limit)
    (htime : time ∈ pathTimes limit.1) (htimeOne : time ≠ 1) :
    Tendsto (fun index ↦ absorptionPathPayoff reward (paths index)
      (approximation.sourceTimes index)) atTop
      (nhds (absorptionPathPayoff reward limit time)) := by
  apply absorptionPathPayoff_tendsto_of_value_tendsto reward
    (times := approximation.sourceTimes) (time := time)
  · intro index
    exact (approximation.source_boundary index).elim And.left And.left
  · exact htime.1
  · exact limitClockTime_total_lt_one htime htimeOne
  · intro coalition
    exact tendsto_pi_nhds.mp (hweak.tendsto_value_one hlimitBounded)
      coalition
  · exact approximation.values_tendsto

private theorem LimitClockBoundarySourceApproximation.quitPayoff_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (player : ι)
    {paths : ℕ → AbsorptionPath (ι := ι)}
    {limit : AbsorptionPath (ι := ι)} {time : ℝ}
    (approximation : LimitClockBoundarySourceApproximation paths limit time)
    (htails : Tendsto (fun index ↦ absorptionPathPayoff reward (paths index)
      (approximation.sourceTimes index)) atTop
      (nhds (absorptionPathPayoff reward limit time))) :
    Tendsto (fun index ↦ quittingRootQuitPayoff reward
      (absorptionPathPayoff reward (paths index)
        (approximation.sourceTimes index))
      (absorptionPathBoundaryRoot (paths index)
        (approximation.sourceTimes index)) player) atTop
      (nhds (reward ⟨{player}, Finset.singleton_nonempty player⟩ player)) := by
  have hraw :=
    (continuous_quittingRootQuitPayoff_simplex reward player).continuousAt.tendsto.comp
      (htails.prodMk_nhds approximation.roots_tendsto)
  change Tendsto (fun index ↦ quittingRootQuitPayoff reward
      (absorptionPathPayoff reward (paths index)
        (approximation.sourceTimes index))
      (quittingRootOfSimplex (quittingSimplexOfRoot
        (absorptionPathBoundaryRoot (paths index)
          (approximation.sourceTimes index)))) player) atTop
    (nhds (quittingRootQuitPayoff reward
      (absorptionPathPayoff reward limit time)
      (quittingRootOfSimplex (quittingSimplexOfRoot
        (quittingAllContinueRoot : ι → PMF Bool))) player)) at hraw
  simpa only [quittingRootOfSimplex_simplexOfRoot,
    quittingRootQuitPayoff_allContinueRoot, quittingSingletonTerminal] using hraw

private theorem LimitClockBoundarySourceApproximation.successorPayoff_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (player : ι)
    {paths : ℕ → AbsorptionPath (ι := ι)}
    {limit : AbsorptionPath (ι := ι)} {time : ℝ}
    (approximation : LimitClockBoundarySourceApproximation paths limit time)
    (htails : Tendsto (fun index ↦ absorptionPathPayoff reward (paths index)
      (approximation.sourceTimes index)) atTop
      (nhds (absorptionPathPayoff reward limit time))) :
    Tendsto (fun index ↦ quittingRootSuccessorPayoff reward
      (absorptionPathPayoff reward (paths index)
        (approximation.sourceTimes index))
      (absorptionPathBoundaryRoot (paths index)
        (approximation.sourceTimes index)) player) atTop
      (nhds (absorptionPathPayoff reward limit time player)) := by
  have hraw :=
    (((continuous_apply player).comp
      (continuous_quittingRootSuccessorPayoff_simplex reward)).continuousAt.tendsto).comp
        (htails.prodMk_nhds approximation.roots_tendsto)
  change Tendsto (fun index ↦ quittingRootSuccessorPayoff reward
      (absorptionPathPayoff reward (paths index)
        (approximation.sourceTimes index))
      (quittingRootOfSimplex (quittingSimplexOfRoot
        (absorptionPathBoundaryRoot (paths index)
          (approximation.sourceTimes index)))) player) atTop
    (nhds (quittingRootSuccessorPayoff reward
      (absorptionPathPayoff reward limit time)
      (quittingRootOfSimplex (quittingSimplexOfRoot
        (quittingAllContinueRoot : ι → PMF Bool))) player)) at hraw
  have hlimit : quittingRootSuccessorPayoff reward
      (absorptionPathPayoff reward limit time)
      (quittingAllContinueRoot : ι → PMF Bool) player =
      absorptionPathPayoff reward limit time player := by
    rw [quittingRootSuccessorPayoff_eq_endpointMix]
    simp [quittingAllContinueRoot]
  simpa only [quittingRootOfSimplex_simplexOfRoot, hlimit] using hraw

/-- The lower continuous-clock sequential-perfection inequality is closed
under unit-bounded weak convergence. -/
theorem playerContinuousClockLowerBound_of_unitBoundedWeakLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (errors : ℕ → ℝ) (paths : ℕ → AbsorptionPath (ι := ι))
    (limit : AbsorptionPath (ι := ι)) (player : ι)
    (hsourceBounded : ∀ index, HasUnitBoundedTotalMass (paths index))
    (hlimitBounded : HasUnitBoundedTotalMass limit)
    (herrors : Tendsto errors atTop (nhds 0))
    (hweak : WeaklyConvergesAbsorptionPaths paths limit)
    (hperfect : ∀ index,
      IsPlayerSequentiallyPerfectAbsorptionPath reward (paths index)
        player (errors index)) :
    ∀ time ∈ pathTimes limit.1, time ≠ 1 →
      reward ⟨{player}, Finset.singleton_nonempty player⟩ player ≤
        absorptionPathPayoff reward limit time player := by
  intro time htime htimeOne
  let approximation := Classical.choice
    (nonempty_limitClockBoundarySourceApproximation hsourceBounded hweak
      htime htimeOne)
  have htail := approximation.payoff_tendsto reward hlimitBounded hweak
    htime htimeOne
  have hbound : ∀ᶠ index in atTop,
      quittingRootQuitPayoff reward
          (absorptionPathPayoff reward (paths index)
            (approximation.sourceTimes index))
          (absorptionPathBoundaryRoot (paths index)
            (approximation.sourceTimes index)) player ≤
        quittingRootSuccessorPayoff reward
            (absorptionPathPayoff reward (paths index)
              (approximation.sourceTimes index))
            (absorptionPathBoundaryRoot (paths index)
              (approximation.sourceTimes index)) player + errors index := by
    filter_upwards [approximation.eventually_source_total_lt_one]
      with index hnonterminalTotal
    rcases approximation.source_boundary index with hjump | hclock
    · rw [absorptionPathBoundaryRoot_of_mem_pathJumps (paths index) hjump]
      exact ((hperfect index).1 (approximation.sourceTimes index) hjump
        hnonterminalTotal).1
    · have hnotJump : approximation.sourceTimes index ∉
          pathJumps (paths index).1 := by
        intro hjump
        have hstrict := lt_pathTotal_of_mem_pathJumps (paths index) hjump
        rw [hclock.2] at hstrict
        exact (lt_irrefl (approximation.sourceTimes index) hstrict).elim
      rw [absorptionPathBoundaryRoot_of_not_mem_pathJumps (paths index)
        hnotJump, quittingRootQuitPayoff_allContinueRoot,
        quittingSingletonTerminal]
      have hsuccessor : quittingRootSuccessorPayoff reward
          (absorptionPathPayoff reward (paths index)
            (approximation.sourceTimes index))
          (quittingAllContinueRoot : ι → PMF Bool) player =
          absorptionPathPayoff reward (paths index)
            (approximation.sourceTimes index) player := by
        rw [quittingRootSuccessorPayoff_eq_endpointMix]
        simp [quittingAllContinueRoot]
      rw [hsuccessor]
      have hnonterminal : approximation.sourceTimes index < 1 := by
        rwa [hclock.2] at hnonterminalTotal
      linarith [((hperfect index).2 (approximation.sourceTimes index)
        hclock (ne_of_lt hnonterminal)).1]
  have hlimit := le_of_tendsto_of_tendsto
    (approximation.quitPayoff_tendsto reward player htail)
    ((approximation.successorPayoff_tendsto reward player htail).add herrors)
    hbound
  simpa using hlimit

end GameTheory.QuittingAbsorptionPath

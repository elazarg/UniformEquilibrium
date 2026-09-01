/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.UnboundedExactBlockHazardCapacity
import UniformEquilibrium.Quitting.Cycles.PeriodicClosing
import UniformEquilibrium.Quitting.Debt.Dynamic.ChronologicalSeamReduction

/-!
# Summable-residual Nash--Bellman spines

This module records an approximate infinite Nash--Bellman spine whose Bellman
and one-stage Nash residuals are nonnegative and summable.  Such a spine is
not an exact canonical Nash--Bellman spine: its residual streams are part of
the data and all consumers retain them explicitly.

The first ledger below turns a supplied residual spine into the artificial
semantic chain used by the summable-seam compiler.  A later section constructs
arbitrarily small residual spines by concatenating compact near-return blocks
from unbounded finite exact-block hazard capacity.

The capacity ranges over all exact blocks in the supplied carrier.  No theorem
here produces that capacity from an AKRS source trace or the Fin4 hard
residual.  The all-behavior uniform-payoff consumer additionally requires two
persistent marginal labels on every supplied accuracy-indexed spine.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction
open scoped BigOperators Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- An infinite Nash--Bellman spine with summable nonnegative Bellman and
one-stage Nash residuals. -/
structure QuittingSummableResidualNashBellmanSpine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  roots : ℕ → ι → PMF Bool
  value : ℕ → Payoff ι
  bellmanError : ℕ → ℝ
  nashError : ℕ → ℝ
  value_bounded : ∃ bound, ∀ time who, |value time who| ≤ bound
  bellmanError_nonneg : ∀ time, 0 ≤ bellmanError time
  nashError_nonneg : ∀ time, 0 ≤ nashError time
  bellmanError_summable : Summable bellmanError
  nashError_summable : Summable nashError
  bellman : ∀ time who,
    |value time who -
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time) who| ≤
        bellmanError time
  nash : ∀ time,
    IsεQuittingRootNash reward (value (time + 1)) (nashError time)
      (roots time)

namespace QuittingSummableResidualNashBellmanSpine

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  (spine : QuittingSummableResidualNashBellmanSpine reward)

/-- Diagonal artificial successor used by the chronological seam consumer. -/
def successor (time : ℕ) : QuittingTerminalSemanticPair ι :=
  (spine.value (time + 1), spine.value (time + 1))

/-- Exact semantic prefix of the diagonal artificial successor. -/
def candidate (time : ℕ) : QuittingTerminalSemanticPair ι :=
  quittingTerminalSemanticPrefix reward (spine.roots time)
    (spine.successor time)

theorem candidate_prescribed (time : ℕ) :
    (spine.candidate time).1 =
      quittingRootSuccessorPayoff reward (spine.value (time + 1))
        (spine.roots time) :=
  rfl

/-- Diagonal-prefix debt is nonnegative because its mixed payoff lies below
the maximum of the two pure endpoints. -/
theorem candidate_debt_nonneg (time : ℕ) (who : ι) :
    0 ≤ quittingTerminalSemanticDebt (spine.candidate time) who := by
  let prescribed := quittingRootSuccessorPayoff reward
    (spine.value (time + 1)) (spine.roots time) who
  let quit := quittingRootQuitPayoff reward
    (spine.value (time + 1)) (spine.roots time) who
  let cont := quittingRootContinuePayoff reward
    (spine.value (time + 1)) (spine.roots time) who
  let localRoots : ℕ → ι → PMF Bool := fun _ => spine.roots time
  let localValue : ℕ → ℝ := fun _ => spine.value (time + 1) who
  have hmix := quittingRootSuccessorPayoff_le_liveBellmanValue reward
    localRoots who localValue 0
  have hquitEq := quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
    reward localRoots who (spine.value (time + 1)) 0
  have hcontinueEq := quittingRootContinuePayoff_eq_fixedOpponents
    reward localRoots who (spine.value (time + 1)) 0
  change quittingRootSuccessorPayoff reward (spine.value (time + 1))
      (spine.roots time) who ≤
    max (quittingFixedOpponentsQuitValue reward localRoots who 0)
      (quittingFixedOpponentsContinueReward reward localRoots who 0 +
        quittingFixedOpponentsContinueMass localRoots who 0 *
          spine.value (time + 1) who) at hmix
  rw [← hquitEq, ← hcontinueEq] at hmix
  unfold quittingTerminalSemanticDebt candidate successor
    quittingTerminalSemanticPrefix
  dsimp only [Prod.fst, Prod.snd]
  rw [Function.update_eq_self]
  change 0 ≤ max quit cont - prescribed
  apply sub_nonneg.mpr
  simpa [prescribed, quit, cont] using hmix

/-- Approximate root Nash bounds every diagonal-prefix debt coordinate by
the row's Nash residual. -/
theorem candidate_debt_le (time : ℕ) (who : ι) :
    quittingTerminalSemanticDebt (spine.candidate time) who ≤
      spine.nashError time := by
  have hnash := spine.nash time
  have hquit := quittingRootQuitPayoff_le_successor_add_of_isεNash
    reward (spine.value (time + 1)) (spine.nashError time)
      (spine.roots time) who hnash
  have hcontinue := quittingRootContinuePayoff_le_successor_add_of_isεNash
    reward (spine.value (time + 1)) (spine.nashError time)
      (spine.roots time) who hnash
  unfold quittingTerminalSemanticDebt candidate successor
    quittingTerminalSemanticPrefix
  dsimp only [Prod.fst, Prod.snd]
  rw [Function.update_eq_self]
  change max
      (quittingRootQuitPayoff reward (spine.value (time + 1))
        (spine.roots time) who)
      (quittingRootContinuePayoff reward (spine.value (time + 1))
        (spine.roots time) who) -
      quittingRootSuccessorPayoff reward (spine.value (time + 1))
        (spine.roots time) who ≤ spine.nashError time
  rw [sub_le_iff_le_add]
  exact max_le (by simpa [add_comm] using hquit)
    (by simpa [add_comm] using hcontinue)

/-- The prescribed seam has the packet's exact `beta_(t+1)` orientation. -/
theorem abs_successor_prescribed_sub_candidate_next_le
    (time : ℕ) (who : ι) :
    |(spine.successor time).1 who - (spine.candidate (time + 1)).1 who| ≤
      spine.bellmanError (time + 1) := by
  change |spine.value (time + 1) who -
    quittingRootSuccessorPayoff reward (spine.value (time + 1 + 1))
      (spine.roots (time + 1)) who| ≤ spine.bellmanError (time + 1)
  exact spine.bellman (time + 1) who

/-- The cap seam is at most `beta_(t+1) + nu_(t+1)`. -/
theorem abs_successor_cap_sub_candidate_next_le
    (time : ℕ) (who : ι) :
    |(spine.successor time).2 who - (spine.candidate (time + 1)).2 who| ≤
      spine.bellmanError (time + 1) + spine.nashError (time + 1) := by
  have hdebt0 := spine.candidate_debt_nonneg (time + 1) who
  have hdebt := spine.candidate_debt_le (time + 1) who
  have hprescribed :=
    spine.abs_successor_prescribed_sub_candidate_next_le time who
  calc
    |(spine.successor time).2 who - (spine.candidate (time + 1)).2 who| ≤
        |(spine.successor time).2 who -
          (spine.candidate (time + 1)).1 who| +
        |(spine.candidate (time + 1)).1 who -
          (spine.candidate (time + 1)).2 who| := by
      exact abs_sub_le _ _ _
    _ ≤ spine.bellmanError (time + 1) + spine.nashError (time + 1) := by
      have hdiag : (spine.successor time).2 who =
          (spine.successor time).1 who := rfl
      rw [hdiag]
      apply add_le_add hprescribed
      rw [abs_sub_comm]
      change |quittingTerminalSemanticDebt
        (spine.candidate (time + 1)) who| ≤ spine.nashError (time + 1)
      rw [abs_of_nonneg hdebt0]
      exact hdebt

/-- Outsider pure Quit is safe up to the Bellman plus Nash residual at the
same selected row. -/
theorem fixedOpponentsQuitValue_le_value_add_residual
    (time : ℕ) (who : ι) :
    quittingStationaryFixedOpponentsQuitValue reward (spine.roots time) who ≤
      spine.value time who + spine.bellmanError time + spine.nashError time := by
  unfold quittingStationaryFixedOpponentsQuitValue
  rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward
    (fun _ => spine.roots time) who (spine.value (time + 1)) 0]
  have hquit := quittingRootQuitPayoff_le_successor_add_of_isεNash
    reward (spine.value (time + 1)) (spine.nashError time)
      (spine.roots time) who (spine.nash time)
  have hbellman := spine.bellman time who
  have hupper : quittingRootSuccessorPayoff reward (spine.value (time + 1))
      (spine.roots time) who ≤ spine.value time who + spine.bellmanError time :=
    by linarith [abs_le.mp hbellman |>.1]
  linarith

/-- The shifted artificial chronological chain used by the seam consumer. -/
def shiftedChain (start : ℕ) : QuittingBoundedSeamChain reward where
  roots time := spine.roots (start + time)
  candidate time := spine.candidate (start + time)
  successor time := spine.successor (start + time)
  exact_step time := rfl
  debt_nonneg time who := spine.candidate_debt_nonneg (start + time) who
  prescribed_bounded := by
    obtain ⟨bound, hbound⟩ := spine.value_bounded
    let common := max |bound| (quittingRewardBound reward)
    refine ⟨common, ?_⟩
    intro time who
    change |quittingRootSuccessorPayoff reward
      (spine.value (start + time + 1)) (spine.roots (start + time)) who| ≤
        common
    apply abs_quittingRootExpectedPayoff_le_bound
    · intro terminal player
      exact (abs_reward_le_quittingRewardBound reward terminal player).trans
        (le_max_right _ _)
    · intro player
      exact (hbound (start + time + 1) player).trans
        ((le_abs_self bound).trans (le_max_left _ _))
  debt_bounded := by
    refine ⟨∑' time, spine.nashError time, ?_⟩
    intro time who
    rw [abs_of_nonneg (spine.candidate_debt_nonneg (start + time) who)]
    apply (spine.candidate_debt_le (start + time) who).trans
    have hsingle := spine.nashError_summable.sum_le_tsum
      {start + time} (fun index _ => spine.nashError_nonneg index)
    simpa using hsingle

theorem shiftedChain_prescribedSeam_le
    (start time : ℕ) (who : ι) :
    (spine.shiftedChain start).prescribedSeam who time ≤
      spine.bellmanError (start + time + 1) := by
  simpa [shiftedChain, QuittingBoundedSeamChain.prescribedSeam,
    Nat.add_assoc] using
      spine.abs_successor_prescribed_sub_candidate_next_le (start + time) who

theorem shiftedChain_capSeam_le
    (start time : ℕ) (who : ι) :
    (spine.shiftedChain start).capSeam who time ≤
      spine.bellmanError (start + time + 1) +
        spine.nashError (start + time + 1) := by
  simpa [shiftedChain, QuittingBoundedSeamChain.capSeam,
    Nat.add_assoc] using
      spine.abs_successor_cap_sub_candidate_next_le (start + time) who

theorem shiftedChain_totalSeam_le
    (start time : ℕ) (who : ι) :
    (spine.shiftedChain start).totalSeam who time ≤
      2 * spine.bellmanError (start + time + 1) +
        spine.nashError (start + time + 1) := by
  unfold QuittingBoundedSeamChain.totalSeam
  have hfirst := spine.shiftedChain_prescribedSeam_le start time who
  have hsecond := spine.shiftedChain_capSeam_le start time who
  linarith

/-- Stored value differs from the literal suffix payoff by at most the tail
sum of Bellman residuals. -/
theorem abs_value_sub_shiftedActualPair_prescribed_le_tsum
    (start : ℕ) (who : ι)
    (hjoint : Tendsto
      (Math.survivalProduct (fun time =>
        quittingStationaryContinueMass
          ((spine.shiftedChain start).roots time)) 0) atTop (nhds 0)) :
    |spine.value start who -
        ((spine.shiftedChain start).actualPair 0).1 who| ≤
      ∑' offset, spine.bellmanError (start + offset) := by
  let chain := spine.shiftedChain start
  have hseamSummable : Summable (chain.prescribedSeam who) := by
    apply Summable.of_nonneg_of_le
      (fun time => chain.prescribedSeam_nonneg who time)
      (fun time => spine.shiftedChain_prescribedSeam_le start time who)
    have hsuffix : Summable (fun offset =>
        spine.bellmanError (offset + (start + 1))) :=
      (summable_nat_add_iff (start + 1)).2 spine.bellmanError_summable
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsuffix
  have hactual := chain.abs_actualPair_prescribed_sub_le_tsum who
    hseamSummable hjoint
  have hseamTsum : (∑' time, chain.prescribedSeam who time) ≤
      ∑' offset, spine.bellmanError (start + offset + 1) := by
    have hsuffix : Summable (fun offset =>
        spine.bellmanError (start + offset + 1)) := by
      have h := (summable_nat_add_iff (start + 1)).2
        spine.bellmanError_summable
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
    exact hseamSummable.tsum_le_tsum
      (fun time => spine.shiftedChain_prescribedSeam_le start time who)
      hsuffix
  have hbellman := spine.bellman start who
  have htriangle : |spine.value start who -
        (chain.actualPair 0).1 who| ≤
      spine.bellmanError start + ∑' time, chain.prescribedSeam who time := by
    calc
      |spine.value start who - (chain.actualPair 0).1 who| ≤
          |spine.value start who - (chain.candidate 0).1 who| +
            |(chain.candidate 0).1 who - (chain.actualPair 0).1 who| :=
        abs_sub_le _ _ _
      _ ≤ spine.bellmanError start +
          ∑' time, chain.prescribedSeam who time := by
        apply add_le_add
        · change |spine.value start who -
            quittingRootSuccessorPayoff reward (spine.value (start + 1))
              (spine.roots start) who| ≤ spine.bellmanError start
          exact hbellman
        · simpa [abs_sub_comm] using hactual
  have htailSplit :=
    ((summable_nat_add_iff start).2
      spine.bellmanError_summable).sum_add_tsum_nat_add 1
  have htailEq : spine.bellmanError start +
        (∑' offset, spine.bellmanError (start + offset + 1)) =
      ∑' offset, spine.bellmanError (start + offset) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htailSplit
  calc
    |spine.value start who - (chain.actualPair 0).1 who| ≤
        spine.bellmanError start + ∑' time, chain.prescribedSeam who time :=
      htriangle
    _ ≤ spine.bellmanError start +
        ∑' offset, spine.bellmanError (start + offset + 1) :=
      by simpa [add_comm] using
        (add_le_add_right hseamTsum (spine.bellmanError start))
    _ = ∑' offset, spine.bellmanError (start + offset) := htailEq

end QuittingSummableResidualNashBellmanSpine

/-! ## Summably joined compact near-return blocks -/

/-- A sequence of finite exact-block hazard returns whose endpoint-to-next-
start distances are summable.  Each return retains its own positive radius;
only the bridge distances are summed. -/
structure QuittingSummableExactNashBellmanHazardReturns
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : Set (QuittingNashBellmanPoint ι)) where
  radius : ℕ → ℝ
  returnedBlock : ∀ block,
    QuittingFiniteExactNashBellmanHazardReturn reward carrier (radius block)
  bridgeDistance_summable : Summable (fun block =>
    dist
      ((returnedBlock block).block.state (returnedBlock block).second)
      ((returnedBlock (block + 1)).block.state
        (returnedBlock (block + 1)).first))

namespace QuittingSummableExactNashBellmanHazardReturns

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {carrier : Set (QuittingNashBellmanPoint ι)}
  (returns : QuittingSummableExactNashBellmanHazardReturns reward carrier)

/-- Distance from one returned block's terminal annotation to the next
returned block's initial annotation. -/
def bridgeDistance (block : ℕ) : ℝ :=
  dist
    ((returns.returnedBlock block).block.state
      (returns.returnedBlock block).second)
    ((returns.returnedBlock (block + 1)).block.state
      (returns.returnedBlock (block + 1)).first)

theorem bridgeDistance_nonneg (block : ℕ) :
    0 ≤ returns.bridgeDistance block :=
  dist_nonneg

theorem summable_bridgeDistance : Summable returns.bridgeDistance := by
  change Summable (fun block =>
    dist
      ((returns.returnedBlock block).block.state
        (returns.returnedBlock block).second)
      ((returns.returnedBlock (block + 1)).block.state
        (returns.returnedBlock (block + 1)).first))
  exact returns.bridgeDistance_summable

end QuittingSummableExactNashBellmanHazardReturns

/-- Compactness refines positive-charge returns at shrinking radii into a
sequence with arbitrarily small total bridge distance. -/
theorem nonempty_summableExactNashBellmanHazardReturns_of_unboundedCapacity
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : Set (QuittingNashBellmanPoint ι))
    (hcarrier : IsCompact carrier)
    (hcapacity :
      HasUnboundedFiniteExactNashBellmanHazardCapacity reward carrier)
    (bridgeBudget : ℝ) (hbridgeBudget : 0 < bridgeBudget) :
    ∃ returns : QuittingSummableExactNashBellmanHazardReturns reward carrier,
      ∑' block, returns.bridgeDistance block ≤ bridgeBudget := by
  classical
  let scale : ℕ → ℝ := fun rank =>
    (bridgeBudget / 3) / 2 * (1 / 2 : ℝ) ^ rank
  have hscalePos : ∀ rank, 0 < scale rank := by
    intro rank
    dsimp [scale]
    positivity
  have hscaleAnti : Antitone scale := by
    intro first second hle
    dsimp [scale]
    apply mul_le_mul_of_nonneg_left
    · exact (pow_right_anti₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) ≤ 1)) hle
    · positivity
  have hscaleSummable : Summable scale := by
    have hgeometric : Summable (fun rank : ℕ => (1 / 2 : ℝ) ^ rank) :=
      summable_geometric_of_norm_lt_one (by norm_num)
    exact hgeometric.mul_left ((bridgeBudget / 3) / 2)
  have hscaleTsum : (∑' rank, scale rank) = bridgeBudget / 3 := by
    change (∑' rank : ℕ,
      (bridgeBudget / 3) / 2 * (1 / 2 : ℝ) ^ rank) = bridgeBudget / 3
    rw [tsum_mul_left,
      tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    ring
  let raw : ∀ rank,
      QuittingFiniteExactNashBellmanHazardReturn reward carrier (scale rank) :=
    fun rank => Classical.choice
      (nonempty_finiteExactNashBellmanHazardReturn_of_unboundedCapacity
        reward carrier hcarrier hcapacity (scale rank) (hscalePos rank))
  let startState : ℕ → QuittingNashBellmanPoint ι := fun rank =>
    (raw rank).block.state (raw rank).first
  have hstartMem : ∀ rank, startState rank ∈ carrier := by
    intro rank
    exact (raw rank).block.state_mem _
      ((raw rank).first_lt_second.le.trans
        (raw rank).second_le_horizon)
  obtain ⟨limit, _hlimitMem, subsequence, hsubsequence, hconverges⟩ :=
    hcarrier.tendsto_subseq hstartMem
  have hcloseEventually : ∀ rank,
      ∀ᶠ index : ℕ in atTop,
        dist (startState (subsequence index)) limit < scale rank := by
    intro rank
    have hball : ∀ᶠ index : ℕ in atTop,
        (startState ∘ subsequence) index ∈
          Metric.ball limit (scale rank) :=
      hconverges (Metric.ball_mem_nhds limit (hscalePos rank))
    simpa only [Function.comp_apply, Metric.mem_ball] using hball
  obtain ⟨refinement, hrefinement, hrefinementClose⟩ :=
    Filter.extraction_forall_of_eventually hcloseEventually
  let selectedIndex : ℕ → ℕ := fun rank => subsequence (refinement rank)
  have hselectedIndex : StrictMono selectedIndex :=
    hsubsequence.comp hrefinement
  let selectedRadius : ℕ → ℝ := fun rank => scale (selectedIndex rank)
  let selectedReturn : ∀ rank,
      QuittingFiniteExactNashBellmanHazardReturn
        reward carrier (selectedRadius rank) :=
    fun rank => raw (selectedIndex rank)
  let bridge : ℕ → ℝ := fun rank =>
    dist
      ((selectedReturn rank).block.state (selectedReturn rank).second)
      ((selectedReturn (rank + 1)).block.state
        (selectedReturn (rank + 1)).first)
  have hbridgeBound : ∀ rank, bridge rank ≤ 3 * scale rank := by
    intro rank
    have hindex : rank ≤ selectedIndex rank := hselectedIndex.id_le rank
    have hwithin : dist
        ((selectedReturn rank).block.state (selectedReturn rank).second)
        ((selectedReturn rank).block.state (selectedReturn rank).first) <
        scale rank := by
      calc
        dist
            ((selectedReturn rank).block.state (selectedReturn rank).second)
            ((selectedReturn rank).block.state (selectedReturn rank).first) =
            dist
              ((selectedReturn rank).block.state (selectedReturn rank).first)
              ((selectedReturn rank).block.state
                (selectedReturn rank).second) := dist_comm _ _
        _ < scale (selectedIndex rank) := (selectedReturn rank).dist_lt
        _ ≤ scale rank := hscaleAnti hindex
    have hfirstClose :
        dist
          ((selectedReturn rank).block.state (selectedReturn rank).first)
          limit < scale rank := by
      simpa [selectedReturn, selectedIndex, startState] using
        hrefinementClose rank
    have hnextClose :
        dist limit
          ((selectedReturn (rank + 1)).block.state
            (selectedReturn (rank + 1)).first) < scale (rank + 1) := by
      rw [dist_comm]
      simpa [selectedReturn, selectedIndex, startState] using
        hrefinementClose (rank + 1)
    have hnextScale : scale (rank + 1) ≤ scale rank :=
      hscaleAnti (Nat.le_succ rank)
    have htriangle : bridge rank ≤
        dist
            ((selectedReturn rank).block.state (selectedReturn rank).second)
            ((selectedReturn rank).block.state (selectedReturn rank).first) +
          dist
            ((selectedReturn rank).block.state (selectedReturn rank).first)
            limit +
          dist limit
            ((selectedReturn (rank + 1)).block.state
              (selectedReturn (rank + 1)).first) := by
      calc
        bridge rank ≤
            dist
                ((selectedReturn rank).block.state
                  (selectedReturn rank).second)
                ((selectedReturn rank).block.state
                  (selectedReturn rank).first) +
              dist
                ((selectedReturn rank).block.state
                  (selectedReturn rank).first)
                ((selectedReturn (rank + 1)).block.state
                  (selectedReturn (rank + 1)).first) :=
          dist_triangle _ _ _
        _ ≤ _ := by
          have h := dist_triangle
            ((selectedReturn rank).block.state (selectedReturn rank).first)
            limit
            ((selectedReturn (rank + 1)).block.state
              (selectedReturn (rank + 1)).first)
          linarith
    linarith
  have hmajorSummable : Summable (fun rank => 3 * scale rank) :=
    hscaleSummable.mul_left 3
  have hbridgeSummable : Summable bridge :=
    Summable.of_nonneg_of_le (fun _ => dist_nonneg) hbridgeBound
      hmajorSummable
  let returns : QuittingSummableExactNashBellmanHazardReturns
      reward carrier := {
    radius := selectedRadius
    returnedBlock := selectedReturn
    bridgeDistance_summable := by
      simpa only [QuittingSummableExactNashBellmanHazardReturns.bridgeDistance,
        bridge] using hbridgeSummable }
  refine ⟨returns, ?_⟩
  have htsum := hbridgeSummable.tsum_le_tsum hbridgeBound hmajorSummable
  calc
    (∑' block, returns.bridgeDistance block) = ∑' block, bridge block := by
      rfl
    _ ≤ ∑' rank, 3 * scale rank := htsum
    _ = bridgeBudget := by rw [tsum_mul_left, hscaleTsum]; ring

namespace QuittingSummableExactNashBellmanHazardReturns

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {carrier : Set (QuittingNashBellmanPoint ι)}
  (returns : QuittingSummableExactNashBellmanHazardReturns reward carrier)

/-- Number of exact Bellman rows retained from one returned subblock. -/
def length (block : ℕ) : ℕ :=
  (returns.returnedBlock block).second - (returns.returnedBlock block).first

theorem length_pos (block : ℕ) : 0 < returns.length block := by
  unfold length
  exact Nat.sub_pos_of_lt (returns.returnedBlock block).first_lt_second

/-- The returned exact blocks as diagonal semantic blocks, before calendar
flattening. -/
def toSeamBlocks
    (valueBound : ℝ)
    (hvalueBound : ∀ point ∈ carrier, ∀ who,
      |point.1 who| ≤ valueBound) :
    QuittingVariableLengthSeamBlocksNat reward where
  length := returns.length
  length_pos := returns.length_pos
  roots block offset :=
    (returns.returnedBlock block).block.root
      ((returns.returnedBlock block).first + offset)
  candidate block offset :=
    let value := (returns.returnedBlock block).block.state
      ((returns.returnedBlock block).first + offset) |>.1
    (value, value)
  exact_step := by
    intro block offset hoffset
    let returned := returns.returnedBlock block
    have htime : returned.first + offset < returned.second := by
      dsimp [returned]
      unfold length at hoffset
      omega
    have hhorizon : returned.first + offset < returned.block.horizon :=
      htime.trans_le returned.second_le_horizon
    have hnash := returned.block.root_isZeroNash hhorizon
    have hprefix := quittingTerminalSemanticPrefix_diagonal_eq_of_isZeroNash
      reward (returned.block.state (returned.first + offset + 1)).1
        (returned.block.root (returned.first + offset)) hnash
    have hvalue := returned.block.value_eq_successor hhorizon
    change
      ((returned.block.state (returned.first + offset)).1,
          (returned.block.state (returned.first + offset)).1) =
        quittingTerminalSemanticPrefix reward
          (returned.block.root (returned.first + offset))
          ((returned.block.state (returned.first + offset + 1)).1,
            (returned.block.state (returned.first + offset + 1)).1)
    simpa [returned, add_assoc, hvalue] using hprefix.symm
  debt_nonneg := by
    intro block offset _hoffset who
    change 0 ≤
      ((returns.returnedBlock block).block.state
          ((returns.returnedBlock block).first + offset)).1 who -
        ((returns.returnedBlock block).block.state
          ((returns.returnedBlock block).first + offset)).1 who
    linarith
  prescribed_bounded := by
    refine ⟨valueBound, ?_⟩
    intro block offset hoffset who
    let returned := returns.returnedBlock block
    have hindex : returned.first + offset ≤ returned.second := by
      change offset ≤ returned.second - returned.first at hoffset
      have hfirstSecond := returned.first_lt_second
      omega
    have hmem : returned.block.state (returned.first + offset) ∈ carrier :=
      returned.block.state_mem _ (hindex.trans returned.second_le_horizon)
    change |(returned.block.state (returned.first + offset)).1 who| ≤ valueBound
    exact hvalueBound (returned.block.state (returned.first + offset)) hmem who
  debt_bounded := by
    refine ⟨0, ?_⟩
    intro block offset _hoffset who
    change |((returns.returnedBlock block).block.state
          ((returns.returnedBlock block).first + offset)).1 who -
        ((returns.returnedBlock block).block.state
          ((returns.returnedBlock block).first + offset)).1 who| ≤ 0
    simp

omit [DecidableEq ι] in
private theorem abs_payoff_apply_sub_le_point_dist
    (first second : QuittingNashBellmanPoint ι) (who : ι) :
    |first.1 who - second.1 who| ≤ dist first second := by
  rw [← Real.dist_eq]
  calc
    dist (first.1 who) (second.1 who) ≤ dist first.1 second.1 :=
      (dist_pi_le_iff dist_nonneg).mp le_rfl who
    _ ≤ max (dist first.1 second.1) (dist first.2 second.2) := le_max_left _ _
    _ = dist first second := Prod.dist_eq.symm

theorem prescribedBlockSeamNat_le_bridgeDistance
    (valueBound : ℝ)
    (hvalueBound : ∀ point ∈ carrier, ∀ who,
      |point.1 who| ≤ valueBound)
    (who : ι) (block : ℕ) :
    (returns.toSeamBlocks valueBound hvalueBound).prescribedBlockSeamNat
        who block ≤ returns.bridgeDistance block := by
  unfold QuittingVariableLengthSeamBlocksNat.prescribedBlockSeamNat
  simp only [toSeamBlocks, length, Nat.add_sub_of_le
    (returns.returnedBlock block).first_lt_second.le]
  exact abs_payoff_apply_sub_le_point_dist _ _ who

theorem summable_prescribedBlockSeamNat
    (valueBound : ℝ)
    (hvalueBound : ∀ point ∈ carrier, ∀ who,
      |point.1 who| ≤ valueBound)
    (who : ι) :
    Summable (fun block =>
      (returns.toSeamBlocks valueBound hvalueBound).prescribedBlockSeamNat
        who block) :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (returns.prescribedBlockSeamNat_le_bridgeDistance
      valueBound hvalueBound who)
    returns.summable_bridgeDistance

theorem tsum_prescribedBlockSeamNat_le_bridgeDistance
    (valueBound : ℝ)
    (hvalueBound : ∀ point ∈ carrier, ∀ who,
      |point.1 who| ≤ valueBound)
    (who : ι) :
    (∑' block,
      (returns.toSeamBlocks valueBound hvalueBound).prescribedBlockSeamNat
        who block) ≤ ∑' block, returns.bridgeDistance block := by
  exact (returns.summable_prescribedBlockSeamNat
    valueBound hvalueBound who).tsum_le_tsum
      (returns.prescribedBlockSeamNat_le_bridgeDistance
        valueBound hvalueBound who)
      returns.summable_bridgeDistance

/-- Every flattened row remains an exact one-stage Nash root against its
within-block successor annotation. -/
theorem flatRootNat_isZeroNash
    (valueBound : ℝ)
    (hvalueBound : ∀ point ∈ carrier, ∀ who,
      |point.1 who| ≤ valueBound)
    (time : ℕ) :
    IsεQuittingRootNash reward
      ((returns.toSeamBlocks valueBound hvalueBound).flatSuccessorNat time).1
      0
      ((returns.toSeamBlocks valueBound hvalueBound).flatRootNat time) := by
  let blocks := returns.toSeamBlocks valueBound hvalueBound
  let block := consecutiveBlockIndex blocks.length blocks.length_pos time
  let offset := consecutiveBlockOffset blocks.length blocks.length_pos time
  have hoffset : offset < blocks.length block :=
    consecutiveBlockOffset_lt blocks.length blocks.length_pos time
  have htime :
      (returns.returnedBlock block).first + offset <
        (returns.returnedBlock block).second := by
    change offset <
      (returns.returnedBlock block).second -
        (returns.returnedBlock block).first at hoffset
    omega
  have hhorizon :
      (returns.returnedBlock block).first + offset <
        (returns.returnedBlock block).block.horizon :=
    htime.trans_le (returns.returnedBlock block).second_le_horizon
  simpa [blocks, block, offset,
    QuittingVariableLengthSeamBlocksNat.flatSuccessorNat,
    QuittingVariableLengthSeamBlocksNat.flatRootNat, toSeamBlocks,
    Nat.add_assoc] using
      (returns.returnedBlock block).block.root_isZeroNash hhorizon

/-- Calendar Bellman error obtained by summing the prescribed seam over all
players. -/
def flattenedBellmanError
    (valueBound : ℝ)
    (hvalueBound : ∀ point ∈ carrier, ∀ who,
      |point.1 who| ≤ valueBound)
    (time : ℕ) : ℝ :=
  ∑ who, ((returns.toSeamBlocks valueBound hvalueBound).flatChainNat
    |>.prescribedSeam who time)

/-- Calendar Nash error obtained by the continuation-transfer factor two. -/
def flattenedNashError
    (valueBound : ℝ)
    (hvalueBound : ∀ point ∈ carrier, ∀ who,
      |point.1 who| ≤ valueBound)
    (time : ℕ) : ℝ :=
  2 * flattenedBellmanError returns valueBound hvalueBound time

/-- Summably joined exact blocks form a summable-residual Nash--Bellman
spine.  Its residuals arise only at calendar seams between returned blocks. -/
def toSummableResidualNashBellmanSpine
    (valueBound : ℝ)
    (hvalueBound : ∀ point ∈ carrier, ∀ who,
      |point.1 who| ≤ valueBound) :
    QuittingSummableResidualNashBellmanSpine reward := by
  let blocks := returns.toSeamBlocks valueBound hvalueBound
  let beta : ℕ → ℝ :=
    flattenedBellmanError returns valueBound hvalueBound
  have hcoordinate : ∀ who,
      Summable (blocks.flatChainNat.prescribedSeam who) := by
    intro who
    exact (blocks.summable_flatPrescribedSeamNat_and_tsum_le who
      (returns.summable_prescribedBlockSeamNat
        valueBound hvalueBound who)
      (returns.tsum_prescribedBlockSeamNat_le_bridgeDistance
        valueBound hvalueBound who)).1
  have hbeta : Summable beta := by
    change Summable (fun time =>
      ∑ who, blocks.flatChainNat.prescribedSeam who time)
    exact summable_sum fun who _ => hcoordinate who
  refine {
    roots := blocks.flatRootNat
    value := fun time => (blocks.flatCandidateNat time).1
    bellmanError := beta
    nashError := fun time => 2 * beta time
    value_bounded := blocks.flatChainNat.prescribed_bounded
    bellmanError_nonneg := ?_
    nashError_nonneg := ?_
    bellmanError_summable := hbeta
    nashError_summable := hbeta.mul_left 2
    bellman := ?_
    nash := ?_ }
  · intro time
    simpa [beta, flattenedBellmanError, blocks] using
      (Finset.sum_nonneg fun who _ =>
        blocks.flatChainNat.prescribedSeam_nonneg who time)
  · intro time
    have hbeta0 : 0 ≤ beta time := by
      simpa [beta, flattenedBellmanError, blocks] using
        (Finset.sum_nonneg fun who _ =>
          blocks.flatChainNat.prescribedSeam_nonneg who time)
    exact mul_nonneg (by norm_num) hbeta0
  · intro time who
    have hstep := blocks.flatChainNat.exact_step time
    have hmass0 := quittingStationaryContinueMass_nonneg
      (blocks.flatRootNat time)
    have hmass1 := quittingStationaryContinueMass_le_one
      (blocks.flatRootNat time)
    have hcoordinateLe :
        blocks.flatChainNat.prescribedSeam who time ≤ beta time := by
      simpa [beta, flattenedBellmanError, blocks] using
        (Finset.single_le_sum
          (fun player _ =>
            blocks.flatChainNat.prescribedSeam_nonneg player time)
          (Finset.mem_univ who))
    change |(blocks.flatCandidateNat time).1 who -
      quittingRootSuccessorPayoff reward
        (blocks.flatCandidateNat (time + 1)).1
        (blocks.flatRootNat time) who| ≤ beta time
    rw [show blocks.flatCandidateNat time =
        quittingTerminalSemanticPrefix reward (blocks.flatRootNat time)
          (blocks.flatSuccessorNat time) by exact hstep]
    calc
      |(quittingTerminalSemanticPrefix reward (blocks.flatRootNat time)
            (blocks.flatSuccessorNat time)).1 who -
          quittingRootSuccessorPayoff reward
            (blocks.flatCandidateNat (time + 1)).1
            (blocks.flatRootNat time) who| =
          quittingStationaryContinueMass (blocks.flatRootNat time) *
            blocks.flatChainNat.prescribedSeam who time := by
        exact abs_quittingTerminalSemanticPrefix_prescribed_sub_eq
          reward (blocks.flatRootNat time) (blocks.flatSuccessorNat time)
            (blocks.flatCandidateNat (time + 1)) who
      _ ≤ blocks.flatChainNat.prescribedSeam who time := by
        nlinarith [blocks.flatChainNat.prescribedSeam_nonneg who time]
      _ ≤ beta time := hcoordinateLe
  · intro time
    have hbeta0 : 0 ≤ beta time :=
      by simpa [beta, flattenedBellmanError, blocks] using
        (Finset.sum_nonneg fun who _ =>
          blocks.flatChainNat.prescribedSeam_nonneg who time)
    have hclose : ∀ who,
        |(blocks.flatSuccessorNat time).1 who -
          (blocks.flatCandidateNat (time + 1)).1 who| ≤ beta time := by
      intro who
      change blocks.flatChainNat.prescribedSeam who time ≤ beta time
      simpa [beta, flattenedBellmanError, blocks] using
        (Finset.single_le_sum (fun player _ =>
          blocks.flatChainNat.prescribedSeam_nonneg player time)
            (Finset.mem_univ who))
    simpa [blocks, beta] using
      (isεQuittingRootNash_of_continuation_close reward
        (blocks.flatSuccessorNat time).1
        (blocks.flatCandidateNat (time + 1)).1
        (blocks.flatRootNat time) hbeta0 hclose
        (returns.flatRootNat_isZeroNash valueBound hvalueBound time))

/-- The total flattened Bellman residual is at most one copy of the bridge
ledger per player. -/
theorem tsum_flattenedBellmanError_le_card_mul_bridgeDistance
    (valueBound : ℝ)
    (hvalueBound : ∀ point ∈ carrier, ∀ who,
      |point.1 who| ≤ valueBound) :
    (∑' time, flattenedBellmanError returns valueBound hvalueBound time) ≤
      Fintype.card ι * ∑' block, returns.bridgeDistance block := by
  let blocks := returns.toSeamBlocks valueBound hvalueBound
  have hcoordinate : ∀ who,
      Summable (blocks.flatChainNat.prescribedSeam who) := by
    intro who
    exact (blocks.summable_flatPrescribedSeamNat_and_tsum_le who
      (returns.summable_prescribedBlockSeamNat
        valueBound hvalueBound who)
      (returns.tsum_prescribedBlockSeamNat_le_bridgeDistance
        valueBound hvalueBound who)).1
  rw [show (∑' time,
      flattenedBellmanError returns valueBound hvalueBound time) =
      ∑ who, ∑' time, blocks.flatChainNat.prescribedSeam who time by
        change (∑' time, ∑ who,
          blocks.flatChainNat.prescribedSeam who time) = _
        exact Summable.tsum_finsetSum fun who _ => hcoordinate who]
  calc
    (∑ who, ∑' time, blocks.flatChainNat.prescribedSeam who time) ≤
        ∑ _who : ι, ∑' block, returns.bridgeDistance block := by
      apply Finset.sum_le_sum
      intro who _
      exact (blocks.summable_flatPrescribedSeamNat_and_tsum_le who
        (returns.summable_prescribedBlockSeamNat
          valueBound hvalueBound who)
        (returns.tsum_prescribedBlockSeamNat_le_bridgeDistance
          valueBound hvalueBound who)).2
    _ = Fintype.card ι * ∑' block, returns.bridgeDistance block := by
      simp

/-- The combined Bellman-plus-Nash residual ledger of the flattened spine is
at most four copies of the bridge ledger per player. -/
theorem residualLedger_le_four_mul_card_mul_bridgeDistance
    (valueBound : ℝ)
    (hvalueBound : ∀ point ∈ carrier, ∀ who,
      |point.1 who| ≤ valueBound) :
    let spine := returns.toSummableResidualNashBellmanSpine
      valueBound hvalueBound
    2 * (∑' time, spine.bellmanError time) +
        (∑' time, spine.nashError time) ≤
      4 * Fintype.card ι * ∑' block, returns.bridgeDistance block := by
  let spine := returns.toSummableResidualNashBellmanSpine
    valueBound hvalueBound
  have hbeta := returns.tsum_flattenedBellmanError_le_card_mul_bridgeDistance
    valueBound hvalueBound
  change 2 * (∑' time,
      flattenedBellmanError returns valueBound hvalueBound time) +
      (∑' time, 2 *
        flattenedBellmanError returns valueBound hvalueBound time) ≤ _
  rw [tsum_mul_left]
  linarith

/-- Each flattened calendar block carries exactly the literal hazard charge
between the two selected annotations of its returned exact block. -/
theorem consecutiveBlockSum_totalHazard_eq_hazardChargeBetween
    (valueBound : ℝ)
    (hvalueBound : ∀ point ∈ carrier, ∀ who,
      |point.1 who| ≤ valueBound)
    (block : ℕ) :
    consecutiveBlockSum returns.length
        (fun time => ∑ who,
          quittingMarginalQuitHazard
            (returns.toSeamBlocks valueBound hvalueBound).flatRootNat
            who time)
        block =
      (returns.returnedBlock block).block.hazardChargeBetween
        (returns.returnedBlock block).first
        (returns.returnedBlock block).second := by
  let blocks := returns.toSeamBlocks valueBound hvalueBound
  let returned := returns.returnedBlock block
  have hpointwise : ∀ offset ∈ Finset.range (returns.length block),
      (∑ who, quittingMarginalQuitHazard blocks.flatRootNat who
        (consecutiveBlockStart returns.length block + offset)) =
        returned.block.stageHazardCharge (returned.first + offset) := by
    intro offset hoffset
    have hoffsetLt : offset < returns.length block :=
      Finset.mem_range.mp hoffset
    apply Finset.sum_congr rfl
    intro who _
    unfold quittingMarginalQuitHazard
      QuittingVariableLengthSeamBlocksNat.flatRootNat
      QuittingFiniteExactNashBellmanBlock.marginalQuitHazard
    dsimp [blocks]
    simp only [toSeamBlocks]
    rw [consecutiveBlockIndex_start_add returns.length returns.length_pos
        block offset hoffsetLt,
      consecutiveBlockOffset_start_add returns.length returns.length_pos
        block offset hoffsetLt]
  unfold consecutiveBlockSum
  rw [Finset.sum_congr rfl hpointwise]
  have hfirstSecond : returned.first ≤ returned.second :=
    returned.first_lt_second.le
  rw [show returns.length block = returned.second - returned.first by rfl]
  rw [← Finset.sum_Ico_eq_sum_range]
  change (∑ time ∈ Finset.Ico returned.first returned.second,
      returned.block.stageHazardCharge time) =
    returned.block.hazardChargeBetween returned.first returned.second
  unfold QuittingFiniteExactNashBellmanBlock.hazardChargeBetween
  exact Finset.sum_Ico_eq_sub _ hfirstSecond

/-- Every selected calendar block has total marginal hazard at least one. -/
theorem one_le_consecutiveBlockSum_totalHazard
    (valueBound : ℝ)
    (hvalueBound : ∀ point ∈ carrier, ∀ who,
      |point.1 who| ≤ valueBound)
    (block : ℕ) :
    1 ≤ consecutiveBlockSum returns.length
      (fun time => ∑ who,
        quittingMarginalQuitHazard
          (returns.toSeamBlocks valueBound hvalueBound).flatRootNat who time)
      block := by
  rw [returns.consecutiveBlockSum_totalHazard_eq_hazardChargeBetween
    valueBound hvalueBound block]
  exact (returns.returnedBlock block).one_le_hazardCharge_sub

/-- At least one player label is persistent in every flattened return family.
This is the exact conclusion of total unbounded hazard; it does not produce the
second persistent label required by the chronological seam consumer. -/
theorem exists_not_summable_flatMarginalQuitHazard
    (valueBound : ℝ)
    (hvalueBound : ∀ point ∈ carrier, ∀ who,
      |point.1 who| ≤ valueBound) :
    ∃ who, ¬Summable (quittingMarginalQuitHazard
      (returns.toSeamBlocks valueBound hvalueBound).flatRootNat who) := by
  classical
  by_contra hnot
  have hall : ∀ who, Summable (quittingMarginalQuitHazard
      (returns.toSeamBlocks valueBound hvalueBound).flatRootNat who) := by
    simpa only [not_exists, not_not] using hnot
  let blocks := returns.toSeamBlocks valueBound hvalueBound
  let total : ℕ → ℝ := fun time =>
    ∑ who, quittingMarginalQuitHazard blocks.flatRootNat who time
  have htotal : Summable total :=
    summable_sum fun who _ => hall who
  obtain ⟨number, hnumber⟩ := exists_nat_gt (∑' time, total time)
  have hpartial :
      (∑ time ∈ Finset.range
          (consecutiveBlockStart returns.length number), total time) ≤
        ∑' time, total time :=
    htotal.sum_le_tsum _ fun time _ =>
      Finset.sum_nonneg fun who _ =>
        quittingMarginalQuitHazard_nonneg blocks.flatRootNat who time
  have hblocks : (number : ℝ) ≤
      ∑ block ∈ Finset.range number,
        consecutiveBlockSum returns.length total block := by
    calc
      (number : ℝ) = ∑ _block ∈ Finset.range number, (1 : ℝ) := by simp
      _ ≤ ∑ block ∈ Finset.range number,
          consecutiveBlockSum returns.length total block := by
        exact Finset.sum_le_sum fun block _ => by
          simpa [total, blocks] using
        returns.one_le_consecutiveBlockSum_totalHazard
            valueBound hvalueBound block
  rw [sum_consecutiveBlockSum_eq_sum_range] at hblocks
  exact (not_lt_of_ge (hblocks.trans hpartial)) hnumber

end QuittingSummableExactNashBellmanHazardReturns

/-! ## Residual-spine producer from unbounded exact-block capacity -/

/-- Explicit-bound helper for the compact capacity compiler. -/
theorem exists_summableResidualNashBellmanSpine_of_unboundedCapacity_of_valueBound
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : Set (QuittingNashBellmanPoint ι))
    (hcarrier : IsCompact carrier)
    (hcapacity :
      HasUnboundedFiniteExactNashBellmanHazardCapacity reward carrier)
    (valueBound : ℝ)
    (hvalueBound : ∀ point ∈ carrier, ∀ who,
      |point.1 who| ≤ valueBound)
    (residualTolerance : ℝ) (hresidualTolerance : 0 < residualTolerance) :
    ∃ spine : QuittingSummableResidualNashBellmanSpine reward,
      2 * (∑' time, spine.bellmanError time) +
          (∑' time, spine.nashError time) ≤ residualTolerance ∧
        ∃ owner,
          ¬Summable (quittingMarginalQuitHazard spine.roots owner) := by
  classical
  have hcardPosNat : 0 < Fintype.card ι := Fintype.card_pos
  have hcardPos : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hcardPosNat
  let bridgeBudget := residualTolerance / (4 * Fintype.card ι)
  have hbridgeBudget : 0 < bridgeBudget := by
    dsimp [bridgeBudget]
    positivity
  obtain ⟨returns, hreturns⟩ :=
    nonempty_summableExactNashBellmanHazardReturns_of_unboundedCapacity
      reward carrier hcarrier hcapacity bridgeBudget hbridgeBudget
  let spine := returns.toSummableResidualNashBellmanSpine
    valueBound hvalueBound
  refine ⟨spine, ?_, ?_⟩
  · have hledger :=
      returns.residualLedger_le_four_mul_card_mul_bridgeDistance
        valueBound hvalueBound
    have hfactor0 : 0 ≤ 4 * (Fintype.card ι : ℝ) := by positivity
    calc
      2 * (∑' time, spine.bellmanError time) +
          (∑' time, spine.nashError time) ≤
          4 * Fintype.card ι *
            ∑' block, returns.bridgeDistance block := hledger
      _ ≤ 4 * Fintype.card ι * bridgeBudget :=
        mul_le_mul_of_nonneg_left hreturns hfactor0
      _ = residualTolerance := by
        dsimp [bridgeBudget]
        field_simp
  · obtain ⟨owner, howner⟩ :=
      returns.exists_not_summable_flatMarginalQuitHazard
        valueBound hvalueBound
    exact ⟨owner, by simpa [spine,
      QuittingSummableExactNashBellmanHazardReturns.toSummableResidualNashBellmanSpine]
      using howner⟩

/-- Unbounded exact-block capacity in a compact carrier produces a
summable-residual spine at every positive residual tolerance.  Compactness
supplies the uniform payoff-coordinate bound used by the flattening ledger.
The flattened roots have at least one persistent marginal label.  The theorem
does not assert a second persistent label or an exact canonical spine. -/
theorem exists_summableResidualNashBellmanSpine_of_unboundedCapacity
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : Set (QuittingNashBellmanPoint ι))
    (hcarrier : IsCompact carrier)
    (hcapacity :
      HasUnboundedFiniteExactNashBellmanHazardCapacity reward carrier)
    (residualTolerance : ℝ) (hresidualTolerance : 0 < residualTolerance) :
    ∃ spine : QuittingSummableResidualNashBellmanSpine reward,
      2 * (∑' time, spine.bellmanError time) +
          (∑' time, spine.nashError time) ≤ residualTolerance ∧
        ∃ owner,
          ¬Summable (quittingMarginalQuitHazard spine.roots owner) := by
  classical
  obtain ⟨block, _hcharge⟩ :=
    (hasUnboundedFiniteExactNashBellmanHazardCapacity_iff
      reward carrier).mp hcapacity 0
  let center : QuittingNashBellmanPoint ι := block.state 0
  have hcenter : center ∈ carrier := block.state_mem 0 (Nat.zero_le _)
  obtain ⟨radius, hradius⟩ :=
    hcarrier.isBounded.subset_closedBall center
  let valueBound : ℝ := radius + ∑ who, |center.1 who|
  have hvalueBound : ∀ point ∈ carrier, ∀ who,
      |point.1 who| ≤ valueBound := by
    intro point hpoint who
    have hpointRadius : dist point center ≤ radius :=
      Metric.mem_closedBall.mp (hradius hpoint)
    have hcoordinateDist : |point.1 who - center.1 who| ≤ dist point center := by
      rw [← Real.dist_eq]
      calc
        dist (point.1 who) (center.1 who) ≤ dist point.1 center.1 :=
          (dist_pi_le_iff dist_nonneg).mp le_rfl who
        _ ≤ max (dist point.1 center.1) (dist point.2 center.2) :=
          le_max_left _ _
        _ = dist point center := Prod.dist_eq.symm
    have hcenterCoordinate : |center.1 who| ≤ ∑ who, |center.1 who| :=
      Finset.single_le_sum (fun player _ => abs_nonneg (center.1 player))
        (Finset.mem_univ who)
    calc
      |point.1 who| = |(point.1 who - center.1 who) + center.1 who| := by
        congr 1
        ring
      _ ≤ |point.1 who - center.1 who| + |center.1 who| :=
        abs_add_le _ _
      _ ≤ radius + ∑ player, |center.1 player| :=
        add_le_add (hcoordinateDist.trans hpointRadius) hcenterCoordinate
      _ = valueBound := rfl
  exact
    exists_summableResidualNashBellmanSpine_of_unboundedCapacity_of_valueBound
      reward carrier hcarrier hcapacity valueBound hvalueBound
        residualTolerance hresidualTolerance

namespace QuittingSummableResidualNashBellmanSpine

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A residual spine with two persistent marginal labels supplies the checked
summable-seam interface at any tolerance covering its total residual ledger. -/
def toSummableSeamSource
    (spine : QuittingSummableResidualNashBellmanSpine reward)
    (eta : ℝ)
    (hledger : 2 * (∑' time, spine.bellmanError time) +
      (∑' time, spine.nashError time) ≤ eta)
    (hpersistent : HasTwoPersistentQuittingMarginals spine.roots) :
    QuittingSummableSeamSource reward eta := by
  let chain := spine.shiftedChain 0
  have hbetaTail : Summable (fun time => spine.bellmanError (time + 1)) :=
    (summable_nat_add_iff 1).2 spine.bellmanError_summable
  have hnuTail : Summable (fun time => spine.nashError (time + 1)) :=
    (summable_nat_add_iff 1).2 spine.nashError_summable
  have hprescribed : ∀ who, Summable (chain.prescribedSeam who) := by
    intro who
    apply Summable.of_nonneg_of_le
      (fun time => chain.prescribedSeam_nonneg who time)
      (fun time => by simpa [chain, Nat.add_comm] using
        spine.shiftedChain_prescribedSeam_le 0 time who)
      hbetaTail
  have htotalMajor : Summable (fun time =>
      2 * spine.bellmanError (time + 1) + spine.nashError (time + 1)) :=
    (hbetaTail.mul_left 2).add hnuTail
  have htotal : ∀ who, Summable (chain.totalSeam who) := by
    intro who
    apply Summable.of_nonneg_of_le
      (fun time => chain.totalSeam_nonneg who time)
      (fun time => by simpa [chain, Nat.add_comm] using
        spine.shiftedChain_totalSeam_le 0 time who)
      htotalMajor
  have hbetaTsum0 : 0 ≤ ∑' time, spine.bellmanError time :=
    tsum_nonneg spine.bellmanError_nonneg
  have hnuTsum0 : 0 ≤ ∑' time, spine.nashError time :=
    tsum_nonneg spine.nashError_nonneg
  have hbetaTailLe : (∑' time, spine.bellmanError (time + 1)) ≤
      ∑' time, spine.bellmanError time := by
    have hsplit := spine.bellmanError_summable.sum_add_tsum_nat_add 1
    have hfirst : 0 ≤ ∑ time ∈ Finset.range 1,
        spine.bellmanError time :=
      Finset.sum_nonneg fun time _ => spine.bellmanError_nonneg time
    linarith
  have hnuTailLe : (∑' time, spine.nashError (time + 1)) ≤
      ∑' time, spine.nashError time := by
    have hsplit := spine.nashError_summable.sum_add_tsum_nat_add 1
    have hfirst : 0 ≤ ∑ time ∈ Finset.range 1, spine.nashError time :=
      Finset.sum_nonneg fun time _ => spine.nashError_nonneg time
    linarith
  have hprescribedTsum : ∀ who,
      (∑' time, chain.prescribedSeam who time) ≤ eta := by
    intro who
    have hseamTail := (hprescribed who).tsum_le_tsum
      (fun time => by simpa [chain, Nat.add_comm] using
        spine.shiftedChain_prescribedSeam_le 0 time who)
      hbetaTail
    linarith
  have htotalTsum : ∀ who,
      (∑' time, chain.totalSeam who time) ≤ eta := by
    intro who
    have hseamMajor := (htotal who).tsum_le_tsum
      (fun time => by simpa [chain, Nat.add_comm] using
        spine.shiftedChain_totalSeam_le 0 time who)
      htotalMajor
    have hmajorEq :
        (∑' time, (2 * spine.bellmanError (time + 1) +
          spine.nashError (time + 1))) =
        2 * (∑' time, spine.bellmanError (time + 1)) +
          ∑' time, spine.nashError (time + 1) := by
      rw [(hbetaTail.mul_left 2).tsum_add hnuTail, tsum_mul_left]
    rw [hmajorEq] at hseamMajor
    linarith
  have hinitial : ∀ who,
      quittingTerminalSemanticDebt (chain.candidate 0) who ≤ eta := by
    intro who
    have hdebt := spine.candidate_debt_le 0 who
    have hsingle := spine.nashError_summable.sum_le_tsum {0}
      (fun time _ => spine.nashError_nonneg time)
    have hnu0 : spine.nashError 0 ≤ ∑' time, spine.nashError time := by
      simpa using hsingle
    simpa [chain, shiftedChain] using hdebt.trans (by linarith)
  have hcard : 2 ≤ Fintype.card ι := by
    obtain ⟨first, second, hne, _, _⟩ := hpersistent
    exact Fintype.one_lt_card_iff.mpr ⟨first, second, hne⟩
  obtain ⟨hopponent, hjoint⟩ := hpersistent.survival hcard
  exact {
    chain := chain
    prescribed_summable := hprescribed
    total_summable := htotal
    prescribed_tsum_le := hprescribedTsum
    total_tsum_le := htotalTsum
    initial_debt_le := hinitial
    joint_survival := by
      intro start
      simpa [chain, shiftedChain] using hjoint start
    opponent_survival := by
      intro who start
      have hsurvival := hopponent who start
      rw [show quittingOpponentSurvivalWeight spine.roots who start =
          Math.survivalProduct
            (fun time => quittingRootOpponentContinueMass
              (spine.roots time) who) start by
        funext fuel
        rw [quittingOpponentSurvivalWeight_eq_survivalProduct]
        rfl] at hsurvival
      simpa [chain, shiftedChain] using hsurvival }

end QuittingSummableResidualNashBellmanSpine

/-- Conditional unrestricted-behavior consumer: arbitrarily small residual
spines with two persistent labels yield a uniform-equilibrium payoff through
the checked summable-seam compiler. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_summableResidualSpines
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hspines : ∀ eta : ℝ, 0 < eta →
      ∃ spine : QuittingSummableResidualNashBellmanSpine reward,
        2 * (∑' time, spine.bellmanError time) +
            (∑' time, spine.nashError time) ≤ eta ∧
          HasTwoPersistentQuittingMarginals spine.roots) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_summableSeams_all_errors
  intro eta heta
  obtain ⟨spine, hledger, hpersistent⟩ := hspines eta heta
  exact ⟨spine.toSummableSeamSource eta hledger hpersistent⟩

end GameTheory

/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Topology.MetricSpace.ProperSpace
import UniformEquilibrium.Quitting.AbsorptionPath.PrincipalQClockOrbit

/-!
# Sequentially closed principal-Q clock reachability

Finite concatenation and any fixed number of countable restart layers do not
capture examples whose switching order has higher countable rank. The honest
carrier is the least class of clock nodes containing the initial node, closed
under one local arc, and closed under convergent sequences of scaled boundary
states. This inductive closure retains a well-founded proof tree for every
reachable node while allowing arbitrary countable restart rank.
-/

noncomputable section

namespace GameTheory.QuittingLCPClassification

open Filter Math.LinearProgramming Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Rescale a boundary scaled state at a positive clock to a clock node. -/
def principalQClockNodeOfScaledState
    (time : ℝ) (htime : 0 < time) (scaledState : ι → ℝ)
    (hscaledState : scaledState ∈ nonnegativeBoundary) :
    PrincipalQClockNode ι where
  time := time
  time_pos := htime
  state := time⁻¹ • scaledState
  state_mem := by
    constructor
    · intro i
      exact mul_nonneg (inv_nonneg.mpr htime.le) (hscaledState.1 i)
    · obtain ⟨i, hi⟩ := hscaledState.2
      exact ⟨i, by simp [hi]⟩

omit [DecidableEq ι] in
@[simp] theorem principalQClockNodeOfScaledState_time
    (time : ℝ) (htime : 0 < time) (scaledState : ι → ℝ)
    (hscaledState : scaledState ∈ nonnegativeBoundary) :
    (principalQClockNodeOfScaledState time htime
      scaledState hscaledState).time = time :=
  rfl

omit [DecidableEq ι] in
@[simp] theorem principalQClockNodeOfScaledState_scaledState
    (time : ℝ) (htime : 0 < time) (scaledState : ι → ℝ)
    (hscaledState : scaledState ∈ nonnegativeBoundary) :
    principalQClockScaledState
      (principalQClockNodeOfScaledState time htime scaledState hscaledState) =
        scaledState := by
  funext i
  change time * (time⁻¹ * scaledState i) = scaledState i
  field_simp [htime.ne']

/-- Regard the endpoint of a local clock step as a clock node. -/
def PrincipalQClockStep.endNode
    {M : ι → ι → ℝ} {stepBound start : ℝ} {q : ι → ℝ}
    (step : PrincipalQClockStep M stepBound start q) :
    PrincipalQClockNode ι where
  time := step.endTime
  time_pos := step.endTime_pos
  state := step.endState
  state_mem := step.endState_mem

omit [DecidableEq ι] in
@[simp] theorem PrincipalQClockStep.endNode_time
    {M : ι → ι → ℝ} {stepBound start : ℝ} {q : ι → ℝ}
    (step : PrincipalQClockStep M stepBound start q) :
    step.endNode.time = step.endTime :=
  rfl

omit [DecidableEq ι] in
@[simp] theorem PrincipalQClockStep.endNode_state
    {M : ι → ι → ℝ} {stepBound start : ℝ} {q : ι → ℝ}
    (step : PrincipalQClockStep M stepBound start q) :
    step.endNode.state = step.endState :=
  rfl

omit [DecidableEq ι] in
/-- One arbitrary local step has scaled displacement at most matrix speed
times elapsed clock time. -/
theorem PrincipalQClockStep.dist_scaledState_endNode_le
    {M : ι → ι → ℝ} {stepBound start : ℝ} {q : ι → ℝ}
    (step : PrincipalQClockStep M stepBound start q) :
    dist (start • q) (principalQClockScaledState step.endNode) ≤
      principalQMatrixSpeedBound M * (step.endTime - start) := by
  have hdelta : 0 ≤ step.endTime - start := sub_nonneg.mpr step.start_lt_endTime.le
  have hbalance := principalQLocalArcState_scaled_balance M step.start_pos
    step.start_lt_endTime.le q step.direction
  change dist (start • q)
    (step.endTime • principalQLocalArcState M start q
      step.direction step.endTime) ≤ _
  rw [hbalance]
  calc
    dist (start • q)
        (start • q + (step.endTime - start) • fun i =>
          singletonLCPResidual M step.direction.weight i) =
      ‖(step.endTime - start) • fun i =>
        singletonLCPResidual M step.direction.weight i‖ := by
      rw [dist_eq_norm, sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg]
    _ = (step.endTime - start) *
        ‖fun i => singletonLCPResidual M step.direction.weight i‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hdelta]
    _ ≤ (step.endTime - start) * principalQMatrixSpeedBound M :=
      mul_le_mul_of_nonneg_left
        (norm_singletonLCPResidual_le_speedBound M step.direction.weight) hdelta
    _ = principalQMatrixSpeedBound M * (step.endTime - start) := mul_comm _ _

/-- Reachability from an initial clock node, closed under local arcs and
sequential scaled-state limits. The proof tree records arbitrary countable
restart rank. -/
inductive PrincipalQClockReachable
    (M : ι → ι → ℝ) (stepBound : ℝ) (initial : PrincipalQClockNode ι) :
    PrincipalQClockNode ι → Prop
  | initial : PrincipalQClockReachable M stepBound initial initial
  | step {node : PrincipalQClockNode ι}
      (hnode : PrincipalQClockReachable M stepBound initial node)
      (arc : PrincipalQClockStep M stepBound node.time node.state) :
      PrincipalQClockReachable M stepBound initial arc.endNode
  | limit (node : ℕ → PrincipalQClockNode ι)
      (hnode : ∀ n, PrincipalQClockReachable M stepBound initial (node n))
      (timeLimit : ℝ) (htimeLimit : 0 < timeLimit)
      (scaledStateLimit : ι → ℝ)
      (hscaledStateLimit : scaledStateLimit ∈ nonnegativeBoundary)
      (htime : Tendsto (fun n => (node n).time) atTop (nhds timeLimit))
      (hscaledState : Tendsto (fun n => principalQClockScaledState (node n))
        atTop (nhds scaledStateLimit)) :
      PrincipalQClockReachable M stepBound initial
        (principalQClockNodeOfScaledState timeLimit htimeLimit
          scaledStateLimit hscaledStateLimit)

omit [DecidableEq ι] in
/-- Every reachable clock is no earlier than the initial clock. -/
theorem PrincipalQClockReachable.initial_time_le
    {M : ι → ι → ℝ} {stepBound : ℝ} {initial node : PrincipalQClockNode ι}
    (hnode : PrincipalQClockReachable M stepBound initial node) :
    initial.time ≤ node.time := by
  induction hnode with
  | initial => exact le_rfl
  | step hnode arc ih => exact ih.trans arc.start_lt_endTime.le
  | limit node hnode timeLimit htimeLimit scaledStateLimit hscaledMem
      htime hscaled ih =>
      apply ge_of_tendsto htime
      exact Eventually.of_forall ih

omit [DecidableEq ι] in
/-- Every reachable scaled state lies in the matrix-speed cone from the
initial scaled state. This estimate is stable under sequential-limit nodes. -/
theorem PrincipalQClockReachable.scaled_distance_le
    {M : ι → ι → ℝ} {stepBound : ℝ} {initial node : PrincipalQClockNode ι}
    (hnode : PrincipalQClockReachable M stepBound initial node) :
    dist (principalQClockScaledState initial)
        (principalQClockScaledState node) ≤
      principalQMatrixSpeedBound M * (node.time - initial.time) := by
  induction hnode with
  | initial => simp
  | @step node hnode arc ih =>
      calc
        dist (principalQClockScaledState initial)
            (principalQClockScaledState arc.endNode) ≤
          dist (principalQClockScaledState initial)
              (principalQClockScaledState node) +
            dist (principalQClockScaledState node)
              (principalQClockScaledState arc.endNode) := dist_triangle _ _ _
        _ ≤ principalQMatrixSpeedBound M * (node.time - initial.time) +
            principalQMatrixSpeedBound M * (arc.endTime - node.time) :=
          add_le_add ih (by
            change dist (node.time • node.state)
              (principalQClockScaledState arc.endNode) ≤ _
            exact arc.dist_scaledState_endNode_le)
        _ = principalQMatrixSpeedBound M *
            (arc.endNode.time - initial.time) := by
          simp only [PrincipalQClockStep.endNode_time]
          ring
  | limit nodes hnodes timeLimit htimeLimit scaledStateLimit hscaledMem
      htime hscaled ih =>
      have hleft : Tendsto (fun n => dist
          (principalQClockScaledState initial)
          (principalQClockScaledState (nodes n))) atTop
          (nhds (dist (principalQClockScaledState initial) scaledStateLimit)) :=
        tendsto_const_nhds.dist hscaled
      have hright : Tendsto (fun n => principalQMatrixSpeedBound M *
          ((nodes n).time - initial.time)) atTop
          (nhds (principalQMatrixSpeedBound M *
            (timeLimit - initial.time))) :=
        tendsto_const_nhds.mul (htime.sub tendsto_const_nhds)
      simpa only [principalQClockNodeOfScaledState_scaledState,
        principalQClockNodeOfScaledState_time] using
        le_of_tendsto_of_tendsto' hleft hright ih

/-! ## Supremum closure and global clock reachability -/

/-- Clock values attained by sequentially closed reachability. -/
def principalQReachableTimes
    (M : ι → ι → ℝ) (stepBound : ℝ) (initial : PrincipalQClockNode ι) :
    Set ℝ :=
  {time | ∃ node : PrincipalQClockNode ι,
    PrincipalQClockReachable M stepBound initial node ∧ node.time = time}

omit [DecidableEq ι] in
/-- The initial clock belongs to the reachable clock set. -/
theorem initial_time_mem_principalQReachableTimes
    (M : ι → ι → ℝ) (stepBound : ℝ) (initial : PrincipalQClockNode ι) :
    initial.time ∈ principalQReachableTimes M stepBound initial :=
  ⟨initial, .initial, rfl⟩

/-- Every reachable node has a strictly later reachable local extension. -/
theorem PrincipalQClockReachable.exists_later
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound : ℝ}
    (hstepBound : 0 < stepBound) {initial node : PrincipalQClockNode ι}
    (hnode : PrincipalQClockReachable M stepBound initial node) :
    ∃ later : PrincipalQClockNode ι,
      PrincipalQClockReachable M stepBound initial later ∧
        node.time < later.time := by
  obtain ⟨arc⟩ := exists_principalQClockStep
    M hdiag hQ hstepBound node.time_pos node.state node.state_mem
  exact ⟨arc.endNode, .step hnode arc, arc.start_lt_endTime⟩

omit [DecidableEq ι] in
/-- **Global target reachability.** Sequential closure removes every finite
or countable-rank Zeno obstruction: from any positive boundary clock, some
reachable node attains every prescribed later finite clock. -/
theorem exists_principalQClockReachable_time_ge
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound : ℝ}
    (hstepBound : 0 < stepBound) (initial : PrincipalQClockNode ι)
    (target : ℝ) :
    ∃ node : PrincipalQClockNode ι,
      PrincipalQClockReachable M stepBound initial node ∧ target ≤ node.time := by
  classical
  by_cases htarget : target ≤ initial.time
  · exact ⟨initial, .initial, htarget⟩
  · have hinitialTarget : initial.time < target := lt_of_not_ge htarget
    by_contra hnone
    have hbelow : ∀ node : PrincipalQClockNode ι,
        PrincipalQClockReachable M stepBound initial node → node.time < target := by
      intro node hnode
      exact lt_of_not_ge fun hge => hnone ⟨node, hnode, hge⟩
    let times := principalQReachableTimes M stepBound initial
    have htimesNonempty : times.Nonempty :=
      ⟨initial.time, initial_time_mem_principalQReachableTimes M stepBound initial⟩
    have htimesBdd : BddAbove times := by
      refine ⟨target, ?_⟩
      rintro time ⟨node, hnode, rfl⟩
      exact (hbelow node hnode).le
    let supremum : ℝ := sSup times
    have hinitialLeSupremum : initial.time ≤ supremum := by
      exact le_csSup htimesBdd
        (initial_time_mem_principalQReachableTimes M stepBound initial)
    have hsupremumPos : 0 < supremum :=
      initial.time_pos.trans_le hinitialLeSupremum
    have happrox (n : ℕ) : ∃ node : PrincipalQClockNode ι,
        PrincipalQClockReachable M stepBound initial node ∧
          supremum - 1 / ((n : ℝ) + 1) < node.time := by
      have hdenom : 0 < (n : ℝ) + 1 := by positivity
      have hlt : supremum - 1 / ((n : ℝ) + 1) < supremum := by
        linarith [one_div_pos.mpr hdenom]
      obtain ⟨time, htimeMem, htime⟩ :=
        exists_lt_of_lt_csSup htimesNonempty hlt
      obtain ⟨node, hnode, rfl⟩ := htimeMem
      exact ⟨node, hnode, htime⟩
    choose node hnode hlower using happrox
    have hupper (n : ℕ) : (node n).time ≤ supremum :=
      le_csSup htimesBdd ⟨node n, hnode n, rfl⟩
    have htime : Tendsto (fun n => (node n).time) atTop (nhds supremum) := by
      have herror : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
          atTop (nhds 0) := by
        simpa [Nat.cast_add, Nat.cast_one] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hdiff : Tendsto (fun n => supremum - (node n).time)
          atTop (nhds 0) := by
        exact squeeze_zero (fun n => sub_nonneg.mpr (hupper n))
          (fun n => le_of_lt (by linarith [hlower n])) herror
      have hreconstruct : Tendsto
          (fun n : ℕ => supremum - (supremum - (node n).time))
          atTop (nhds (supremum - 0)) :=
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => supremum)
          atTop (nhds supremum)).sub hdiff
      simpa only [sub_sub_cancel, sub_zero] using hreconstruct
    let radius := principalQMatrixSpeedBound M * (target - initial.time)
    have hscaledBall (n : ℕ) : principalQClockScaledState (node n) ∈
        Metric.closedBall (principalQClockScaledState initial) radius := by
      rw [Metric.mem_closedBall]
      rw [dist_comm]
      exact (hnode n).scaled_distance_le.trans
        (mul_le_mul_of_nonneg_left
          (sub_le_sub_right (hbelow (node n) (hnode n)).le initial.time)
          (principalQMatrixSpeedBound_nonneg M))
    have hfrequent : ∃ᶠ n in atTop, principalQClockScaledState (node n) ∈
        Metric.closedBall (principalQClockScaledState initial) radius :=
      Frequently.of_forall hscaledBall
    obtain ⟨scaledStateLimit, hscaledBallLimit, subsequence,
        hsubsequence, hscaledState⟩ :=
      (isCompact_closedBall (principalQClockScaledState initial) radius).isSeqCompact
        |>.subseq_of_frequently_in hfrequent
    have hscaledBoundary : scaledStateLimit ∈ nonnegativeBoundary := by
      apply isClosed_nonnegativeBoundary.mem_of_tendsto hscaledState
      exact Eventually.of_forall fun n =>
        principalQClockScaledState_mem (node (subsequence n))
    have htimeSubsequence : Tendsto (fun n => (node (subsequence n)).time)
        atTop (nhds supremum) :=
      htime.comp hsubsequence.tendsto_atTop
    have hlimitReachable : PrincipalQClockReachable M stepBound initial
        (principalQClockNodeOfScaledState supremum hsupremumPos
          scaledStateLimit hscaledBoundary) := by
      exact .limit (fun n => node (subsequence n))
        (fun n => hnode (subsequence n)) supremum hsupremumPos
        scaledStateLimit hscaledBoundary htimeSubsequence hscaledState
    obtain ⟨later, hlaterReachable, hlater⟩ :=
      hlimitReachable.exists_later M hdiag hQ hstepBound
    have hlaterLe : later.time ≤ supremum :=
      le_csSup htimesBdd ⟨later, hlaterReachable, rfl⟩
    have hsupremumLt : supremum < later.time := by
      simpa only [principalQClockNodeOfScaledState_time] using hlater
    exact (not_lt_of_ge hlaterLe hsupremumLt).elim

end GameTheory.QuittingLCPClassification

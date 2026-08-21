/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Viability.AdaptiveEulerLimit
import UniformEquilibrium.Quitting.AbsorptionPath.PrincipalQClockChain
import UniformEquilibrium.Quitting.AbsorptionPath.PrincipalQSupportCorrespondence

/-!
# Infinite adaptive principal-Q clock orbits

Classical choice iterates the serial local-arc construction. Its clock is
strictly increasing. Hence either it escapes every finite horizon, or it has a
finite Zeno limit and its clock increments form a summable series. The state
limit at that Zeno clock is handled separately from this order-theoretic split.
-/

noncomputable section

namespace GameTheory.QuittingLCPClassification

open Filter Finset Math Math.LinearProgramming Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A positive paper clock together with a boundary state. -/
structure PrincipalQClockNode (ι : Type) [Fintype ι] where
  time : ℝ
  time_pos : 0 < time
  state : ι → ℝ
  state_mem : IsNonnegativeBoundary state

/-- A chosen local step from a clock node. -/
def chosenPrincipalQClockStep
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound : ℝ}
    (hstepBound : 0 < stepBound) (node : PrincipalQClockNode ι) :
    PrincipalQClockStep M stepBound node.time node.state :=
  Classical.choice (exists_principalQClockStep M hdiag hQ hstepBound
    node.time_pos node.state node.state_mem)

/-- Advance a node by its chosen local clock step. -/
def principalQClockSuccessor
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound : ℝ}
    (hstepBound : 0 < stepBound) (node : PrincipalQClockNode ι) :
    PrincipalQClockNode ι := by
  let step := chosenPrincipalQClockStep M hdiag hQ hstepBound node
  exact
    { time := step.endTime
      time_pos := step.endTime_pos
      state := step.endState
      state_mem := step.endState_mem }

/-- The infinite adaptive orbit obtained by repeatedly choosing a local arc. -/
def principalQClockOrbit
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound : ℝ}
    (hstepBound : 0 < stepBound) (initial : PrincipalQClockNode ι) :
    ℕ → PrincipalQClockNode ι
  | 0 => initial
  | n + 1 => principalQClockSuccessor M hdiag hQ hstepBound
      (principalQClockOrbit M hdiag hQ hstepBound initial n)

@[simp] theorem principalQClockOrbit_zero
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound : ℝ}
    (hstepBound : 0 < stepBound) (initial : PrincipalQClockNode ι) :
    principalQClockOrbit M hdiag hQ hstepBound initial 0 = initial :=
  rfl

@[simp] theorem principalQClockOrbit_succ
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound : ℝ}
    (hstepBound : 0 < stepBound) (initial : PrincipalQClockNode ι) (n : ℕ) :
    principalQClockOrbit M hdiag hQ hstepBound initial (n + 1) =
      principalQClockSuccessor M hdiag hQ hstepBound
        (principalQClockOrbit M hdiag hQ hstepBound initial n) :=
  rfl

/-- Every successor step strictly advances the selected paper clock. -/
theorem principalQClockOrbit_time_lt_succ
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound : ℝ}
    (hstepBound : 0 < stepBound) (initial : PrincipalQClockNode ι) (n : ℕ) :
    (principalQClockOrbit M hdiag hQ hstepBound initial n).time <
      (principalQClockOrbit M hdiag hQ hstepBound initial (n + 1)).time := by
  rw [principalQClockOrbit_succ]
  exact (chosenPrincipalQClockStep M hdiag hQ hstepBound _).start_lt_endTime

/-- The selected orbit clock is strictly increasing. -/
theorem strictMono_principalQClockOrbit_time
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound : ℝ}
    (hstepBound : 0 < stepBound) (initial : PrincipalQClockNode ι) :
    StrictMono (fun n =>
      (principalQClockOrbit M hdiag hQ hstepBound initial n).time) :=
  strictMono_nat_of_lt_succ fun n =>
    principalQClockOrbit_time_lt_succ M hdiag hQ hstepBound initial n

/-- An adaptive clock either reaches arbitrarily late times, or converges to
a finite Zeno clock and has summable positive increments. -/
theorem principalQClockOrbit_escape_or_zeno
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound : ℝ}
    (hstepBound : 0 < stepBound) (initial : PrincipalQClockNode ι) :
    Tendsto (fun n =>
      (principalQClockOrbit M hdiag hQ hstepBound initial n).time)
        atTop atTop ∨
      ∃ limit : ℝ,
        Tendsto (fun n =>
          (principalQClockOrbit M hdiag hQ hstepBound initial n).time)
            atTop (nhds limit) ∧
        Summable (fun n =>
          (principalQClockOrbit M hdiag hQ hstepBound initial (n + 1)).time -
            (principalQClockOrbit M hdiag hQ hstepBound initial n).time) := by
  let time : ℕ → ℝ := fun n =>
    (principalQClockOrbit M hdiag hQ hstepBound initial n).time
  have hstrict : StrictMono time :=
    strictMono_principalQClockOrbit_time M hdiag hQ hstepBound initial
  by_cases hbdd : BddAbove (range time)
  · right
    let limit : ℝ := ⨆ n, time n
    have hlimit : Tendsto time atTop (nhds limit) :=
      tendsto_atTop_ciSup hstrict.monotone hbdd
    have hincrement : ∀ n, 0 ≤ time (n + 1) - time n := fun n =>
      sub_nonneg.mpr (hstrict.monotone (Nat.le_succ n))
    have hhasSum : HasSum (fun n => time (n + 1) - time n)
        (limit - time 0) := by
      apply (hasSum_iff_tendsto_nat_of_nonneg hincrement _).2
      simpa only [Finset.sum_range_sub] using
        hlimit.sub tendsto_const_nhds
    exact ⟨limit, hlimit, hhasSum.summable⟩
  · left
    exact tendsto_atTop_atTop_of_monotone' hstrict.monotone hbdd

/-! ## The scaled-state endpoint in the Zeno branch -/

/-- A matrix-only uniform bound for every simplex-weighted column mixture. -/
def principalQMatrixSpeedBound (M : ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, |M i j|

omit [DecidableEq ι] in
/-- The matrix speed bound is nonnegative. -/
theorem principalQMatrixSpeedBound_nonneg (M : ι → ι → ℝ) :
    0 ≤ principalQMatrixSpeedBound M := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _

omit [DecidableEq ι] in
/-- Every simplex-weighted matrix mixture has norm bounded solely by `M`. -/
theorem norm_singletonLCPResidual_le_speedBound
    (M : ι → ι → ℝ) (weight : stdSimplex ℝ ι) :
    ‖fun i => singletonLCPResidual M weight i‖ ≤
      principalQMatrixSpeedBound M := by
  apply (pi_norm_le_iff_of_nonneg (principalQMatrixSpeedBound_nonneg M)).2
  intro i
  rw [Real.norm_eq_abs]
  unfold singletonLCPResidual wsum dotProduct
  calc
    |∑ j, weight j * M i j| ≤ ∑ j, |weight j * M i j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, weight j * |M i j| := by
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_mul]
      congr 1
      exact abs_of_nonneg (weight.property.1 j)
    _ ≤ ∑ j, |M i j| := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_of_le_one_left (abs_nonneg _) (stdSimplex.le_one weight j)
    _ ≤ principalQMatrixSpeedBound M := by
      exact Finset.single_le_sum
        (fun k _ => Finset.sum_nonneg fun j _ => abs_nonneg (M k j))
        (Finset.mem_univ i)

/-- The scaled state at an orbit node. -/
def principalQClockScaledState (node : PrincipalQClockNode ι) : ι → ℝ :=
  node.time • node.state

omit [DecidableEq ι] in
/-- Positive scaling preserves membership in the nonnegative boundary. -/
theorem principalQClockScaledState_mem (node : PrincipalQClockNode ι) :
    principalQClockScaledState node ∈ nonnegativeBoundary := by
  constructor
  · intro i
    exact mul_nonneg node.time_pos.le (node.state_mem.1 i)
  · obtain ⟨i, hi⟩ := node.state_mem.2
    exact ⟨i, by simp [principalQClockScaledState, hi]⟩

/-- One clock successor changes the scaled state by elapsed time times a
simplex-weighted matrix mixture. -/
theorem principalQClockSuccessor_scaled_balance
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound : ℝ}
    (hstepBound : 0 < stepBound) (node : PrincipalQClockNode ι) :
    principalQClockScaledState
        (principalQClockSuccessor M hdiag hQ hstepBound node) =
      principalQClockScaledState node +
        ((principalQClockSuccessor M hdiag hQ hstepBound node).time -
          node.time) • fun i => singletonLCPResidual M
            (chosenPrincipalQClockStep M hdiag hQ hstepBound node).direction.weight i := by
  let step := chosenPrincipalQClockStep M hdiag hQ hstepBound node
  change step.endTime • step.endState =
    node.time • node.state + (step.endTime - node.time) • fun i =>
      singletonLCPResidual M step.direction.weight i
  exact principalQLocalArcState_scaled_balance M step.start_pos
    step.start_lt_endTime.le node.state step.direction

/-- Successive scaled orbit states move by at most the elapsed clock time
times the matrix speed bound. -/
theorem dist_principalQClockOrbit_scaledState_succ_le
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound : ℝ}
    (hstepBound : 0 < stepBound) (initial : PrincipalQClockNode ι) (n : ℕ) :
    dist
        (principalQClockScaledState
          (principalQClockOrbit M hdiag hQ hstepBound initial n))
        (principalQClockScaledState
          (principalQClockOrbit M hdiag hQ hstepBound initial (n + 1))) ≤
      principalQMatrixSpeedBound M *
        ((principalQClockOrbit M hdiag hQ hstepBound initial (n + 1)).time -
          (principalQClockOrbit M hdiag hQ hstepBound initial n).time) := by
  let node := principalQClockOrbit M hdiag hQ hstepBound initial n
  let step := chosenPrincipalQClockStep M hdiag hQ hstepBound node
  have hdelta : 0 ≤ step.endTime - node.time := sub_nonneg.mpr step.start_lt_endTime.le
  rw [principalQClockOrbit_succ]
  change dist (principalQClockScaledState node)
      (principalQClockScaledState
        (principalQClockSuccessor M hdiag hQ hstepBound node)) ≤ _
  rw [principalQClockSuccessor_scaled_balance]
  change dist (principalQClockScaledState node)
      (principalQClockScaledState node +
        (step.endTime - node.time) • fun i =>
          singletonLCPResidual M step.direction.weight i) ≤
    principalQMatrixSpeedBound M * (step.endTime - node.time)
  calc
    dist (principalQClockScaledState node)
        (principalQClockScaledState node +
          (step.endTime - node.time) • fun i =>
            singletonLCPResidual M step.direction.weight i) =
      ‖(step.endTime - node.time) • fun i =>
        singletonLCPResidual M step.direction.weight i‖ := by
      rw [dist_eq_norm, sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg]
    _ = (step.endTime - node.time) *
        ‖fun i => singletonLCPResidual M step.direction.weight i‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hdelta]
    _ ≤ (step.endTime - node.time) * principalQMatrixSpeedBound M :=
      mul_le_mul_of_nonneg_left
        (norm_singletonLCPResidual_le_speedBound M step.direction.weight) hdelta
    _ = principalQMatrixSpeedBound M * (step.endTime - node.time) := mul_comm _ _

/-- The total scaled-state displacement along any finite orbit prefix is
bounded by elapsed clock time times the same matrix-only speed bound. -/
theorem dist_principalQClockOrbit_scaledState_le
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound : ℝ}
    (hstepBound : 0 < stepBound) (initial : PrincipalQClockNode ι) (n : ℕ) :
    dist (principalQClockScaledState initial)
        (principalQClockScaledState
          (principalQClockOrbit M hdiag hQ hstepBound initial n)) ≤
      principalQMatrixSpeedBound M *
        ((principalQClockOrbit M hdiag hQ hstepBound initial n).time -
          initial.time) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        dist (principalQClockScaledState initial)
            (principalQClockScaledState
              (principalQClockOrbit M hdiag hQ hstepBound initial (n + 1))) ≤
          dist (principalQClockScaledState initial)
              (principalQClockScaledState
                (principalQClockOrbit M hdiag hQ hstepBound initial n)) +
            dist
              (principalQClockScaledState
                (principalQClockOrbit M hdiag hQ hstepBound initial n))
              (principalQClockScaledState
                (principalQClockOrbit M hdiag hQ hstepBound initial (n + 1))) :=
          dist_triangle _ _ _
        _ ≤ principalQMatrixSpeedBound M *
              ((principalQClockOrbit M hdiag hQ hstepBound initial n).time -
                initial.time) +
            principalQMatrixSpeedBound M *
              ((principalQClockOrbit M hdiag hQ hstepBound initial (n + 1)).time -
                (principalQClockOrbit M hdiag hQ hstepBound initial n).time) :=
          add_le_add ih (dist_principalQClockOrbit_scaledState_succ_le
            M hdiag hQ hstepBound initial n)
        _ = principalQMatrixSpeedBound M *
            ((principalQClockOrbit M hdiag hQ hstepBound initial (n + 1)).time -
              initial.time) := by ring

/-- Summable clock increments force the scaled orbit states to converge to a
point of the closed nonnegative boundary. -/
theorem exists_principalQClockOrbit_scaledState_limit
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound : ℝ}
    (hstepBound : 0 < stepBound) (initial : PrincipalQClockNode ι)
    (hsummable : Summable (fun n =>
      (principalQClockOrbit M hdiag hQ hstepBound initial (n + 1)).time -
        (principalQClockOrbit M hdiag hQ hstepBound initial n).time)) :
    ∃ limit ∈ nonnegativeBoundary,
      Tendsto (fun n => principalQClockScaledState
        (principalQClockOrbit M hdiag hQ hstepBound initial n))
          atTop (nhds limit) := by
  apply Math.Viability.exists_tendsto_mem_of_summable_step_bound
    isClosed_nonnegativeBoundary
    (fun n => principalQClockScaledState
      (principalQClockOrbit M hdiag hQ hstepBound initial n))
    (fun n => principalQClockScaledState_mem
      (principalQClockOrbit M hdiag hQ hstepBound initial n))
    (fun n =>
      (principalQClockOrbit M hdiag hQ hstepBound initial (n + 1)).time -
        (principalQClockOrbit M hdiag hQ hstepBound initial n).time)
    (principalQMatrixSpeedBound M)
    (dist_principalQClockOrbit_scaledState_succ_le
      M hdiag hQ hstepBound initial) hsummable

/-- The infinite adaptive construction either escapes every finite horizon,
or has both a finite Zeno clock and a boundary scaled-state endpoint. -/
theorem principalQClockOrbit_escape_or_zenoEndpoint
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound : ℝ}
    (hstepBound : 0 < stepBound) (initial : PrincipalQClockNode ι) :
    Tendsto (fun n =>
      (principalQClockOrbit M hdiag hQ hstepBound initial n).time)
        atTop atTop ∨
      ∃ (timeLimit : ℝ) (scaledStateLimit : ι → ℝ),
        Tendsto (fun n =>
          (principalQClockOrbit M hdiag hQ hstepBound initial n).time)
            atTop (nhds timeLimit) ∧
        scaledStateLimit ∈ nonnegativeBoundary ∧
        Tendsto (fun n => principalQClockScaledState
          (principalQClockOrbit M hdiag hQ hstepBound initial n))
            atTop (nhds scaledStateLimit) := by
  rcases principalQClockOrbit_escape_or_zeno
      M hdiag hQ hstepBound initial with hescape | ⟨timeLimit, htime, hsum⟩
  · exact Or.inl hescape
  · right
    obtain ⟨scaledStateLimit, hscaledMem, hscaled⟩ :=
      exists_principalQClockOrbit_scaledState_limit
        M hdiag hQ hstepBound initial hsum
    exact ⟨timeLimit, scaledStateLimit, htime, hscaledMem, hscaled⟩

/-- A finite Zeno endpoint canonically rescales to a new positive-clock
boundary node, and the original orbit states converge to that restart state. -/
theorem exists_principalQClockOrbit_zenoRestart
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound : ℝ}
    (hstepBound : 0 < stepBound) (initial : PrincipalQClockNode ι)
    {timeLimit : ℝ} {scaledStateLimit : ι → ℝ}
    (htime : Tendsto (fun n =>
      (principalQClockOrbit M hdiag hQ hstepBound initial n).time)
        atTop (nhds timeLimit))
    (hscaledMem : scaledStateLimit ∈ nonnegativeBoundary)
    (hscaled : Tendsto (fun n => principalQClockScaledState
      (principalQClockOrbit M hdiag hQ hstepBound initial n))
        atTop (nhds scaledStateLimit)) :
    ∃ restart : PrincipalQClockNode ι,
      restart.time = timeLimit ∧
      Tendsto (fun n =>
        (principalQClockOrbit M hdiag hQ hstepBound initial n).state)
          atTop (nhds restart.state) := by
  let orbit := principalQClockOrbit M hdiag hQ hstepBound initial
  have hmono : Monotone (fun n => (orbit n).time) :=
    (strictMono_principalQClockOrbit_time
      M hdiag hQ hstepBound initial).monotone
  have hinitialLe : initial.time ≤ timeLimit := by
    apply ge_of_tendsto htime
    exact Eventually.of_forall fun n => by
      simpa only [orbit, principalQClockOrbit_zero] using hmono (Nat.zero_le n)
  have htimeLimitPos : 0 < timeLimit := initial.time_pos.trans_le hinitialLe
  let restartState : ι → ℝ := timeLimit⁻¹ • scaledStateLimit
  have hrestartMem : IsNonnegativeBoundary restartState := by
    constructor
    · intro i
      exact mul_nonneg (inv_nonneg.mpr htimeLimitPos.le) (hscaledMem.1 i)
    · obtain ⟨i, hi⟩ := hscaledMem.2
      exact ⟨i, by simp [restartState, hi]⟩
  let restart : PrincipalQClockNode ι :=
    { time := timeLimit
      time_pos := htimeLimitPos
      state := restartState
      state_mem := hrestartMem }
  refine ⟨restart, rfl, ?_⟩
  have hreconstructed : (fun n =>
      ((orbit n).time)⁻¹ • principalQClockScaledState (orbit n)) =
      fun n => (orbit n).state := by
    funext n i
    simp [principalQClockScaledState, (orbit n).time_pos.ne']
  have hrescaled := (htime.inv₀ htimeLimitPos.ne').smul hscaled
  rw [hreconstructed] at hrescaled
  exact hrescaled

end GameTheory.QuittingLCPClassification

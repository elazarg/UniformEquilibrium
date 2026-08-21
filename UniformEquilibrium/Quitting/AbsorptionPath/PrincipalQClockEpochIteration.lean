/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.PrincipalQClockEpoch

/-!
# Countable iteration of principal-Q clock epochs

Epochs restart after first-order Zeno limits. Iterating that restart either
reaches a prescribed finite target, or exposes a second-order Zeno sequence:
the restart clocks increase strictly, remain bounded, and have summable
increments. This module states that boundary explicitly rather than silently
assuming that countably many restarts must reach the target.
-/

noncomputable section

namespace GameTheory.QuittingLCPClassification

open Filter Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Status of a countable epoch iteration. -/
inductive PrincipalQClockProgress (ι : Type) [Fintype ι] : Type
  | active (node : PrincipalQClockNode ι)
  | reached (node : PrincipalQClockNode ι)

/-- The node carried by either progress status. -/
def PrincipalQClockProgress.node : PrincipalQClockProgress ι →
    PrincipalQClockNode ι
  | .active node => node
  | .reached node => node

/-- Whether the target has already been reached. -/
def PrincipalQClockProgress.IsReached : PrincipalQClockProgress ι → Prop
  | .active _ => False
  | .reached _ => True

/-- A chosen outcome of one complete epoch. -/
def chosenPrincipalQClockEpochOutcome
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound : ℝ}
    (hstepBound : 0 < stepBound) (node : PrincipalQClockNode ι)
    (target : ℝ) :
    PrincipalQClockEpochOutcome M hdiag hQ hstepBound node target :=
  Classical.choice (nonempty_principalQClockEpochOutcome
    M hdiag hQ hstepBound node target)

/-- Advance one countable-epoch status. A reached status is absorbing; a
restart at or beyond the target is immediately marked reached. -/
def principalQClockProgressNext
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound : ℝ}
    (hstepBound : 0 < stepBound) (target : ℝ) :
    PrincipalQClockProgress ι → PrincipalQClockProgress ι
  | .reached node => .reached node
  | .active node =>
      match chosenPrincipalQClockEpochOutcome
          M hdiag hQ hstepBound node target with
      | .reaches index _ => .reached
          (principalQClockOrbit M hdiag hQ hstepBound node index)
      | .restarts restart _ _ _ =>
          if target ≤ restart.time then .reached restart else .active restart

/-- From an active node, the next epoch either reaches the target or remains
active at a strictly later clock still below the target. -/
theorem principalQClockProgressNext_active
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound : ℝ}
    (hstepBound : 0 < stepBound) (target : ℝ)
    (node : PrincipalQClockNode ι) :
    (principalQClockProgressNext M hdiag hQ hstepBound target
        (.active node)).IsReached ∨
      node.time <
          (principalQClockProgressNext M hdiag hQ hstepBound target
            (.active node)).node.time ∧
        (principalQClockProgressNext M hdiag hQ hstepBound target
            (.active node)).node.time < target := by
  cases houtcome : chosenPrincipalQClockEpochOutcome
      M hdiag hQ hstepBound node target with
  | reaches index htarget =>
      exact Or.inl (by
        simp [principalQClockProgressNext, houtcome,
          PrincipalQClockProgress.IsReached])
  | restarts restart hstrict htendsto hdistance =>
      by_cases htarget : target ≤ restart.time
      · exact Or.inl (by
          simp [principalQClockProgressNext, houtcome, htarget,
            PrincipalQClockProgress.IsReached])
      · right
        simpa [principalQClockProgressNext, houtcome, htarget,
          PrincipalQClockProgress.node] using
          And.intro hstrict (lt_of_not_ge htarget)

/-- One completed epoch satisfies the same scaled-state displacement bound
as its underlying finite or Zeno orbit. -/
theorem dist_principalQClockProgressNext_active_scaledState_le
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound : ℝ}
    (hstepBound : 0 < stepBound) (target : ℝ)
    (node : PrincipalQClockNode ι) :
    dist (principalQClockScaledState node)
        (principalQClockScaledState
          (principalQClockProgressNext M hdiag hQ hstepBound
            target (.active node)).node) ≤
      principalQMatrixSpeedBound M *
        ((principalQClockProgressNext M hdiag hQ hstepBound
          target (.active node)).node.time - node.time) := by
  cases houtcome : chosenPrincipalQClockEpochOutcome
      M hdiag hQ hstepBound node target with
  | reaches index htarget =>
      simpa [principalQClockProgressNext, houtcome,
        PrincipalQClockProgress.node] using
        dist_principalQClockOrbit_scaledState_le
          M hdiag hQ hstepBound node index
  | restarts restart hstrict htendsto hdistance =>
      by_cases htarget : target ≤ restart.time
      · simpa [principalQClockProgressNext, houtcome, htarget,
          PrincipalQClockProgress.node] using hdistance
      · simpa [principalQClockProgressNext, houtcome, htarget,
          PrincipalQClockProgress.node] using hdistance

/-- Completing an epoch never moves its carried clock backwards. -/
theorem principalQClockProgressNext_time_mono
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound : ℝ}
    (hstepBound : 0 < stepBound) (target : ℝ)
    (progress : PrincipalQClockProgress ι) :
    progress.node.time ≤
      (principalQClockProgressNext M hdiag hQ hstepBound target progress).node.time := by
  cases progress with
  | reached node => simp [principalQClockProgressNext, PrincipalQClockProgress.node]
  | active node =>
      cases houtcome : chosenPrincipalQClockEpochOutcome
          M hdiag hQ hstepBound node target with
      | reaches index htarget =>
          simpa [principalQClockProgressNext, houtcome,
            PrincipalQClockProgress.node] using
            (strictMono_principalQClockOrbit_time
              M hdiag hQ hstepBound node).monotone (Nat.zero_le index)
      | restarts restart hstrict htendsto hdistance =>
          by_cases htarget : target ≤ restart.time
          · simpa [principalQClockProgressNext, houtcome, htarget,
              PrincipalQClockProgress.node] using hstrict.le
          · simpa [principalQClockProgressNext, houtcome, htarget,
              PrincipalQClockProgress.node] using hstrict.le

/-- The countable sequence obtained by repeatedly completing one epoch. -/
def principalQClockProgressOrbit
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound : ℝ}
    (hstepBound : 0 < stepBound) (target : ℝ)
    (initial : PrincipalQClockNode ι) : ℕ → PrincipalQClockProgress ι
  | 0 => .active initial
  | n + 1 => principalQClockProgressNext M hdiag hQ hstepBound target
      (principalQClockProgressOrbit M hdiag hQ hstepBound target initial n)

@[simp] theorem principalQClockProgressOrbit_zero
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound : ℝ}
    (hstepBound : 0 < stepBound) (target : ℝ)
    (initial : PrincipalQClockNode ι) :
    principalQClockProgressOrbit M hdiag hQ hstepBound target initial 0 =
      .active initial :=
  rfl

@[simp] theorem principalQClockProgressOrbit_succ
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound : ℝ}
    (hstepBound : 0 < stepBound) (target : ℝ)
    (initial : PrincipalQClockNode ι) (n : ℕ) :
    principalQClockProgressOrbit M hdiag hQ hstepBound target initial (n + 1) =
      principalQClockProgressNext M hdiag hQ hstepBound target
        (principalQClockProgressOrbit M hdiag hQ hstepBound target initial n) :=
  rfl

/-- Countable epoch iteration either reaches the target, or its restart clocks
have a finite second-order Zeno limit with summable increments. -/
theorem principalQClockProgressOrbit_reaches_or_zeno
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound : ℝ}
    (hstepBound : 0 < stepBound) (target : ℝ)
    (initial : PrincipalQClockNode ι) :
    (∃ n, (principalQClockProgressOrbit
      M hdiag hQ hstepBound target initial n).IsReached) ∨
      ∃ limit : ℝ,
        Tendsto (fun n => (principalQClockProgressOrbit
          M hdiag hQ hstepBound target initial n).node.time)
            atTop (nhds limit) ∧
        Summable (fun n =>
          (principalQClockProgressOrbit M hdiag hQ hstepBound
            target initial (n + 1)).node.time -
          (principalQClockProgressOrbit M hdiag hQ hstepBound
            target initial n).node.time) := by
  let progress := principalQClockProgressOrbit
    M hdiag hQ hstepBound target initial
  by_cases hreached : ∃ n, (progress n).IsReached
  · exact Or.inl hreached
  · right
    have hactive (n : ℕ) : ∃ node, progress n = .active node := by
      cases hprogress : progress n with
      | active node => exact ⟨node, rfl⟩
      | reached node =>
          exfalso
          exact hreached ⟨n, by simp [hprogress, PrincipalQClockProgress.IsReached]⟩
    have hstep (n : ℕ) : (progress n).node.time < (progress (n + 1)).node.time ∧
        (progress (n + 1)).node.time < target := by
      obtain ⟨node, hnode⟩ := hactive n
      have hnext := principalQClockProgressNext_active
        M hdiag hQ hstepBound target node
      have hsucc : progress (n + 1) =
          principalQClockProgressNext M hdiag hQ hstepBound target
            (.active node) := by
        change principalQClockProgressNext M hdiag hQ hstepBound target
            (progress n) = _
        rw [hnode]
      rw [hnode, hsucc]
      exact hnext.resolve_left fun hreach =>
        hreached ⟨n + 1, by rw [hsucc]; exact hreach⟩
    have hstrict : StrictMono (fun n => (progress n).node.time) :=
      strictMono_nat_of_lt_succ fun n => (hstep n).1
    have hbdd : BddAbove (range fun n => (progress n).node.time) := by
      refine ⟨max initial.time target, ?_⟩
      rintro _ ⟨n, rfl⟩
      cases n with
      | zero =>
          change initial.time ≤ max initial.time target
          exact le_max_left _ _
      | succ n => exact (hstep n).2.le.trans (le_max_right _ _)
    let limit : ℝ := ⨆ n, (progress n).node.time
    have hlimit : Tendsto (fun n => (progress n).node.time)
        atTop (nhds limit) := tendsto_atTop_ciSup hstrict.monotone hbdd
    have hincrement : ∀ n, 0 ≤
        (progress (n + 1)).node.time - (progress n).node.time := fun n =>
      sub_nonneg.mpr (hstrict.monotone (Nat.le_succ n))
    have hsum : HasSum (fun n =>
        (progress (n + 1)).node.time - (progress n).node.time)
        (limit - (progress 0).node.time) := by
      apply (hasSum_iff_tendsto_nat_of_nonneg hincrement _).2
      have hconst : Tendsto (fun _ : ℕ => (progress 0).node.time)
          atTop (nhds (progress 0).node.time) := tendsto_const_nhds
      have heq : (fun n => ∑ i ∈ Finset.range n,
          ((progress (i + 1)).node.time - (progress i).node.time)) =
          fun n => (progress n).node.time - (progress 0).node.time := by
        funext n
        exact Finset.sum_range_sub (fun i => (progress i).node.time) n
      rw [heq]
      exact hlimit.sub hconst
    exact ⟨limit, hlimit, hsum.summable⟩

/-- Successive countable-epoch nodes obey the matrix speed bound, including
the absorbing reached status where both sides vanish. -/
theorem dist_principalQClockProgressOrbit_scaledState_succ_le
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound : ℝ}
    (hstepBound : 0 < stepBound) (target : ℝ)
    (initial : PrincipalQClockNode ι) (n : ℕ) :
    dist (principalQClockScaledState
        (principalQClockProgressOrbit M hdiag hQ hstepBound
          target initial n).node)
      (principalQClockScaledState
        (principalQClockProgressOrbit M hdiag hQ hstepBound
          target initial (n + 1)).node) ≤
      principalQMatrixSpeedBound M *
        ((principalQClockProgressOrbit M hdiag hQ hstepBound
          target initial (n + 1)).node.time -
        (principalQClockProgressOrbit M hdiag hQ hstepBound
          target initial n).node.time) := by
  let progress := principalQClockProgressOrbit
    M hdiag hQ hstepBound target initial
  change dist (principalQClockScaledState (progress n).node)
      (principalQClockScaledState (progress (n + 1)).node) ≤
    principalQMatrixSpeedBound M *
      ((progress (n + 1)).node.time - (progress n).node.time)
  have hsucc : progress (n + 1) =
      principalQClockProgressNext M hdiag hQ hstepBound target (progress n) :=
    rfl
  rw [hsucc]
  cases hprogress : progress n with
  | active node =>
      exact dist_principalQClockProgressNext_active_scaledState_le
        M hdiag hQ hstepBound target node
  | reached node =>
      simp [principalQClockProgressNext, PrincipalQClockProgress.node]

/-- If countable epoch iteration has a second-order Zeno clock, its scaled
states also converge to the closed nonnegative boundary. -/
theorem principalQClockProgressOrbit_reaches_or_zenoEndpoint
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound : ℝ}
    (hstepBound : 0 < stepBound) (target : ℝ)
    (initial : PrincipalQClockNode ι) :
    (∃ n, (principalQClockProgressOrbit
      M hdiag hQ hstepBound target initial n).IsReached) ∨
      ∃ (timeLimit : ℝ) (scaledStateLimit : ι → ℝ),
        Tendsto (fun n => (principalQClockProgressOrbit
          M hdiag hQ hstepBound target initial n).node.time)
            atTop (nhds timeLimit) ∧
        scaledStateLimit ∈ nonnegativeBoundary ∧
        Tendsto (fun n => principalQClockScaledState
          (principalQClockProgressOrbit M hdiag hQ hstepBound
            target initial n).node) atTop (nhds scaledStateLimit) := by
  rcases principalQClockProgressOrbit_reaches_or_zeno
      M hdiag hQ hstepBound target initial with hreach |
        ⟨timeLimit, htime, hsum⟩
  · exact Or.inl hreach
  · right
    obtain ⟨scaledStateLimit, hscaledMem, hscaled⟩ :=
      Math.Viability.exists_tendsto_mem_of_summable_step_bound
        isClosed_nonnegativeBoundary
        (fun n => principalQClockScaledState
          (principalQClockProgressOrbit M hdiag hQ hstepBound
            target initial n).node)
        (fun n => principalQClockScaledState_mem
          (principalQClockProgressOrbit M hdiag hQ hstepBound
            target initial n).node)
        (fun n =>
          (principalQClockProgressOrbit M hdiag hQ hstepBound
            target initial (n + 1)).node.time -
          (principalQClockProgressOrbit M hdiag hQ hstepBound
            target initial n).node.time)
        (principalQMatrixSpeedBound M)
        (dist_principalQClockProgressOrbit_scaledState_succ_le
          M hdiag hQ hstepBound target initial) hsum
    exact ⟨timeLimit, scaledStateLimit, htime, hscaledMem, hscaled⟩

/-- A second-order Zeno endpoint of countable epoch iteration rescales to a
new positive-clock boundary node, just as a first-order orbit endpoint does. -/
theorem exists_principalQClockProgressOrbit_zenoRestart
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound : ℝ}
    (hstepBound : 0 < stepBound) (target : ℝ)
    (initial : PrincipalQClockNode ι)
    {timeLimit : ℝ} {scaledStateLimit : ι → ℝ}
    (htime : Tendsto (fun n => (principalQClockProgressOrbit
      M hdiag hQ hstepBound target initial n).node.time)
        atTop (nhds timeLimit))
    (hscaledMem : scaledStateLimit ∈ nonnegativeBoundary)
    (hscaled : Tendsto (fun n => principalQClockScaledState
      (principalQClockProgressOrbit M hdiag hQ hstepBound
        target initial n).node) atTop (nhds scaledStateLimit)) :
    ∃ restart : PrincipalQClockNode ι,
      restart.time = timeLimit ∧
      Tendsto (fun n => (principalQClockProgressOrbit
        M hdiag hQ hstepBound target initial n).node.state)
          atTop (nhds restart.state) := by
  let progress := principalQClockProgressOrbit
    M hdiag hQ hstepBound target initial
  have hmono : Monotone (fun n => (progress n).node.time) := by
    apply monotone_nat_of_le_succ
    intro n
    change (progress n).node.time ≤
      (principalQClockProgressNext M hdiag hQ hstepBound
        target (progress n)).node.time
    exact principalQClockProgressNext_time_mono
      M hdiag hQ hstepBound target (progress n)
  have hinitialLe : initial.time ≤ timeLimit := by
    apply ge_of_tendsto htime
    exact Eventually.of_forall fun n => by
      simpa only [progress, principalQClockProgressOrbit_zero,
        PrincipalQClockProgress.node] using hmono (Nat.zero_le n)
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
  have hreconstructed : (fun n => ((progress n).node.time)⁻¹ •
      principalQClockScaledState (progress n).node) =
      fun n => (progress n).node.state := by
    funext n i
    simp [principalQClockScaledState, (progress n).node.time_pos.ne']
  have hrescaled := (htime.inv₀ htimeLimitPos.ne').smul hscaled
  rw [hreconstructed] at hrescaled
  exact hrescaled

end GameTheory.QuittingLCPClassification

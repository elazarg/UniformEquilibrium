import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Bounded affine recursions and geometric schedules

The scalar telescope is promoted from the previously checked Sorin paper
proof; its former private declaration delegates here. The sequence theorem
selects all stages and residual states from the actual one-step relation.
-/

noncomputable section

open scoped BigOperators

namespace Math.RealSeries

/-- A bounded affine recursion is realized by its normalized geometric
series. The endpoint weight one is included. -/
theorem geometric_sum_eq_of_bounded_affine_recurrence
    (weight : ℝ) (hweight : 0 < weight) (hweight1 : weight ≤ 1)
    (state stage : ℕ → ℝ) (bound : ℝ)
    (hbound : ∀ time, |state time| ≤ bound)
    (hrec : ∀ time,
      state time = weight * stage time + (1 - weight) * state (time + 1)) :
    weight * ∑' time : ℕ, (1 - weight) ^ time * stage time = state 0 := by
  let beta := 1 - weight
  have hbeta0 : 0 ≤ beta := by
    dsimp only [beta]
    linarith
  have hbeta1 : beta < 1 := by
    dsimp only [beta]
    linarith
  have hbound0 : 0 ≤ bound :=
    (abs_nonneg (state 0)).trans (hbound 0)
  have hgeom : Summable (fun time : ℕ => beta ^ time) :=
    summable_geometric_of_lt_one hbeta0 hbeta1
  let weightedState : ℕ → ℝ :=
    fun time => beta ^ time * state time
  have hweightedState : Summable weightedState := by
    apply Summable.of_norm_bounded (hgeom.mul_left bound)
    intro time
    dsimp only [weightedState]
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hbeta0]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left (hbound time) (pow_nonneg hbeta0 time)
  have hweightedTail : Summable (fun time => weightedState (time + 1)) :=
    hweightedState.comp_injective Nat.succ_injective
  rw [← tsum_mul_left]
  calc
    (∑' time : ℕ, weight * ((1 - weight) ^ time * stage time)) =
        ∑' time : ℕ, (weightedState time - weightedState (time + 1)) := by
      apply tsum_congr
      intro time
      have h := hrec time
      dsimp only [weightedState, beta]
      rw [pow_succ']
      calc
        weight * ((1 - weight) ^ time * stage time) =
            (1 - weight) ^ time * (weight * stage time) := by ring
        _ = (1 - weight) ^ time *
            (state time - (1 - weight) * state (time + 1)) := by
          congr 1
          linarith
        _ = (1 - weight) ^ time * state time -
            (1 - weight) * (1 - weight) ^ time * state (time + 1) := by
          ring
    _ = (∑' time : ℕ, weightedState time) -
        ∑' time : ℕ, weightedState (time + 1) :=
      hweightedState.tsum_sub hweightedTail
    _ = state 0 := by
      rw [hweightedState.tsum_eq_zero_add]
      simp [weightedState]

/-- An actual one-step affine representation at every residual point
internally supplies a complete geometric stage schedule. No sequence,
residual orbit, limit or delivered-payoff certificate is supplied. -/
theorem exists_geometric_schedule_of_bounded_affine_steps
    {I A : Type*} (region : Set (I → ℝ)) (stageValue : A → I → ℝ)
    (weight : ℝ) (hweight : 0 < weight) (hweight1 : weight ≤ 1)
    (bound : I → ℝ)
    (hbound : ∀ value ∈ region, ∀ who, |value who| ≤ bound who)
    (hstep : ∀ value ∈ region, ∃ current : A, ∃ next ∈ region,
      value = weight • stageValue current + (1 - weight) • next)
    (point : I → ℝ) (hpoint : point ∈ region) :
    ∃ stages : ℕ → A, ∀ who,
      weight * ∑' time : ℕ, (1 - weight) ^ time * stageValue (stages time) who =
        point who := by
  classical
  let Carrier := {value : I → ℝ // value ∈ region}
  let current (state : Carrier) : A := Classical.choose (hstep state.1 state.2)
  have current_spec (state : Carrier) : ∃ next ∈ region,
      state.1 = weight • stageValue (current state) + (1 - weight) • next :=
    Classical.choose_spec (hstep state.1 state.2)
  let nextValue (state : Carrier) : I → ℝ := Classical.choose (current_spec state)
  have nextValue_spec (state : Carrier) : nextValue state ∈ region ∧
      state.1 = weight • stageValue (current state) + (1 - weight) • nextValue state :=
    Classical.choose_spec (current_spec state)
  let next (state : Carrier) : Carrier := ⟨nextValue state, (nextValue_spec state).1⟩
  let state : ℕ → Carrier := fun time =>
    Nat.rec ⟨point, hpoint⟩ (fun _ previous => next previous) time
  let stages : ℕ → A := fun time => current (state time)
  have hrec (time : ℕ) : (state time).1 =
      weight • stageValue (stages time) + (1 - weight) • (state (time + 1)).1 := by
    simpa [state, stages, next] using (nextValue_spec (state time)).2
  refine ⟨stages, fun who => ?_⟩
  have hscalarRec (time : ℕ) : (state time).1 who =
      weight * stageValue (stages time) who + (1 - weight) * (state (time + 1)).1 who := by
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using congrFun (hrec time) who
  exact geometric_sum_eq_of_bounded_affine_recurrence weight hweight hweight1
    (fun time => (state time).1 who) (fun time => stageValue (stages time) who)
    (bound who) (fun time => hbound _ (state time).2 who) hscalarRec

end Math.RealSeries

/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.CyclicContraction
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Total variation on a finite cycle

The distance between any two values on a nonempty finite cycle is bounded by
the total absolute variation around the cycle.
-/

namespace Math

/-- Norm telescoping along the first `steps` iterates of an arbitrary map. -/
theorem norm_iterate_sub_le_sum_norm_step {X E : Type*}
    [SeminormedAddCommGroup E]
    (next : X → X) (v : X → E) (start : X) (steps : ℕ) :
    ‖v ((next^[steps]) start) - v start‖ ≤
      ∑ offset ∈ Finset.range steps,
        ‖v ((next^[offset + 1]) start) - v ((next^[offset]) start)‖ := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [Finset.sum_range_succ]
      have htriangle :
          ‖v ((next^[steps + 1]) start) - v start‖ ≤
            ‖v ((next^[steps + 1]) start) - v ((next^[steps]) start)‖ +
              ‖v ((next^[steps]) start) - v start‖ := by
        simpa only [← dist_eq_norm] using
          dist_triangle (v ((next^[steps + 1]) start))
            (v ((next^[steps]) start)) (v start)
      calc
        ‖v ((next^[steps + 1]) start) - v start‖ ≤
            ‖v ((next^[steps + 1]) start) - v ((next^[steps]) start)‖ +
              ‖v ((next^[steps]) start) - v start‖ := htriangle
        _ ≤ ‖v ((next^[steps + 1]) start) - v ((next^[steps]) start)‖ +
              ∑ offset ∈ Finset.range steps,
                ‖v ((next^[offset + 1]) start) - v ((next^[offset]) start)‖ :=
          add_le_add (le_refl _) ih
        _ = ∑ offset ∈ Finset.range steps,
                ‖v ((next^[offset + 1]) start) - v ((next^[offset]) start)‖ +
              ‖v ((next^[steps + 1]) start) - v ((next^[steps]) start)‖ := by
          rw [add_comm]

/-- Telescoping along the first `steps` iterates of an arbitrary map. -/
theorem abs_iterate_sub_le_sum_abs_step {X : Type*}
    (next : X → X) (v : X → ℝ) (start : X) (steps : ℕ) :
    |v ((next^[steps]) start) - v start| ≤
      ∑ offset ∈ Finset.range steps,
        |v ((next^[offset + 1]) start) - v ((next^[offset]) start)| := by
  simpa only [Real.norm_eq_abs] using
    (norm_iterate_sub_le_sum_norm_step next v start steps)

/-- Norm-valued finite-cycle variation bound. -/
theorem norm_sub_le_sum_norm_finRotate {n : ℕ} {E : Type*}
    [SeminormedAddCommGroup E] (v : Fin n → E) (source target : Fin n) :
    ‖v source - v target‖ ≤
      ∑ phase : Fin n, ‖v (finRotate n phase) - v phase‖ := by
  haveI : NeZero n := source.neZero
  obtain ⟨steps, hsteps, hreach⟩ := exists_iterate_finRotate_eq target source
  let orbit : ℕ → Fin n := fun offset => (finRotate n)^[offset] target
  let edge : Fin n → ℝ := fun phase => ‖v (finRotate n phase) - v phase‖
  have horbitInjective : Set.InjOn orbit (Finset.range steps) := by
    intro first hfirst second hsecond heq
    have hfirstN : first < n :=
      (Finset.mem_range.mp hfirst).trans hsteps
    have hsecondN : second < n :=
      (Finset.mem_range.mp hsecond).trans hsteps
    let firstFin : Fin n := ⟨first, hfirstN⟩
    let secondFin : Fin n := ⟨second, hsecondN⟩
    have hcycle : finCycle firstFin target = finCycle secondFin target := by
      rw [finCycle_eq_finRotate_iterate, finCycle_eq_finRotate_iterate]
      exact heq
    have hadd : target + firstFin = target + secondFin := by
      simpa only [finCycle_apply] using hcycle
    have hfin : firstFin = secondFin := add_left_cancel hadd
    exact Fin.mk.inj hfin
  have hpath := norm_iterate_sub_le_sum_norm_step
    (finRotate n) v target steps
  rw [hreach] at hpath
  have hstep : ∀ offset,
      ‖v (((finRotate n)^[offset + 1]) target) -
          v (((finRotate n)^[offset]) target)‖ = edge (orbit offset) := by
    intro offset
    rw [Function.iterate_succ_apply']
  simp_rw [hstep] at hpath
  have himage :
      ∑ phase ∈ Finset.image orbit (Finset.range steps), edge phase =
        ∑ offset ∈ Finset.range steps, edge (orbit offset) :=
    Finset.sum_image horbitInjective
  calc
    ‖v source - v target‖ ≤
        ∑ offset ∈ Finset.range steps, edge (orbit offset) := hpath
    _ = ∑ phase ∈ Finset.image orbit (Finset.range steps), edge phase :=
      himage.symm
    _ ≤ ∑ phase ∈ (Finset.univ : Finset (Fin n)), edge phase :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun phase _ _ => norm_nonneg (v (finRotate n phase) - v phase))
    _ = ∑ phase : Fin n, ‖v (finRotate n phase) - v phase‖ := rfl

/-- On a nonempty finite cyclic index set, any two values differ by at most
the total absolute variation around the cycle. -/
theorem abs_sub_le_sum_abs_finRotate {n : ℕ} (v : Fin n → ℝ)
    (source target : Fin n) :
    |v source - v target| ≤
      ∑ phase : Fin n, |v (finRotate n phase) - v phase| := by
  simpa only [Real.norm_eq_abs] using
    (norm_sub_le_sum_norm_finRotate v source target)

end Math

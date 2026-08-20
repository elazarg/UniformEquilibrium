/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Sparse schedules below a vanishing mesh

This file records the elementary scheduling fact used by the conditioned-tail
search.  A nonnegative mesh tending to zero admits a strictly increasing
subsequence on which the mesh is at most `2⁻ⁿ`.  The harmonic clock on that
subsequence still has divergent total mass, while its mesh-weighted collision
cost is summable.

This is only a scheduling lemma.  In particular, it does **not** say that the
clock is a constant multiple of the selected mesh, nor does it supply any
game-semantic Snell or vector-recursion estimate.
-/

noncomputable section

open Filter Topology

namespace Math

local instance (p : Prop) : Decidable p := Classical.propDecidable p

private theorem exists_sparseTimesOn_zero (P : ℕ → Prop) (hP : ∀ start,
    ∃ t, start ≤ t ∧ P t) (alpha : ℕ → ℝ)
    (hα : Tendsto alpha atTop (nhds 0)) : ∃ t, P t ∧ alpha t ≤ 1 := by
  have he : ∀ᶠ n : ℕ in atTop, alpha n < 1 :=
    (tendsto_order.1 hα).2 1 zero_lt_one
  rcases eventually_atTop.1 he with ⟨N, hN⟩
  rcases hP N with ⟨s, hs, hPs⟩
  exact ⟨s, hPs, (hN s hs).le⟩

private theorem exists_sparseTimesOn_succ (P : ℕ → Prop)
    (hP : ∀ start, ∃ t, start ≤ t ∧ P t) (alpha : ℕ → ℝ)
    (hα : Tendsto alpha atTop (nhds 0)) (n previous : ℕ) :
    ∃ t, previous < t ∧ P t ∧ alpha t ≤ (1 : ℝ) / 2 ^ (n + 1) := by
  have he : ∀ᶠ t : ℕ in atTop,
      alpha t < (1 : ℝ) / 2 ^ (n + 1) :=
    (tendsto_order.1 hα).2 _ (by positivity)
  rcases eventually_atTop.1 he with ⟨N, hN⟩
  rcases hP (max (previous + 1) N) with ⟨t, ht, hPt⟩
  refine ⟨t, lt_of_lt_of_le (Nat.lt_succ_self previous)
    (le_trans (le_max_left _ _) ht), hPt, (hN t (le_trans (le_max_right _ _) ht)).le⟩

private noncomputable def sparseTimesOn (P : ℕ → Prop)
    (hP : ∀ start, ∃ t, start ≤ t ∧ P t) (alpha : ℕ → ℝ)
    (hα : Tendsto alpha atTop (nhds 0)) : ℕ → ℕ :=
  Nat.rec
    (Nat.find (exists_sparseTimesOn_zero P hP alpha hα))
    (fun n previous =>
      Nat.find (exists_sparseTimesOn_succ P hP alpha hα n previous))

private theorem sparseTimesOn_succ (P : ℕ → Prop)
    (hP : ∀ start, ∃ t, start ≤ t ∧ P t) (alpha : ℕ → ℝ)
    (hα : Tendsto alpha atTop (nhds 0)) (n : ℕ) :
    sparseTimesOn P hP alpha hα n < sparseTimesOn P hP alpha hα (n + 1) ∧
      P (sparseTimesOn P hP alpha hα (n + 1)) ∧
      alpha (sparseTimesOn P hP alpha hα (n + 1)) ≤ (1 : ℝ) / 2 ^ (n + 1) := by
  unfold sparseTimesOn
  exact Nat.find_spec
    (exists_sparseTimesOn_succ P hP alpha hα n
      (sparseTimesOn P hP alpha hα n))

/-- The sparse schedule can additionally be required to lie in any cofinal
set of dates.  This is the form needed when inactivity and an endpoint gap
hold only on cofinal selected dates. -/
theorem exists_sparse_vanishing_nonsummable_schedule_of_cofinal
    (P : ℕ → Prop) (hP : ∀ start, ∃ t, start ≤ t ∧ P t)
    (alpha : ℕ → ℝ) (halpha : ∀ n, 0 ≤ alpha n)
    (hα : Tendsto alpha atTop (nhds 0)) :
    ∃ time : ℕ → ℕ, ∃ theta : ℕ → ℝ,
      (∀ n, P (time n)) ∧ StrictMono time ∧
      (∀ n, alpha (time n) ≤ (1 / 2 : ℝ) ^ n) ∧
      (∀ n, 0 < theta n) ∧ (∀ n, theta n ≤ 1) ∧
      Tendsto theta atTop (nhds 0) ∧
      ¬Summable theta ∧
      Summable (fun n => theta n * alpha (time n)) := by
  let time := sparseTimesOn P hP alpha hα
  let theta : ℕ → ℝ := fun n => (1 : ℝ) / (n + 1)
  have hpos : ∀ n, 0 < theta n := by intro n; dsimp [theta]; positivity
  have hzero : Tendsto theta atTop (nhds 0) := by
    dsimp [theta]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hdiv : ¬Summable theta := by
    simpa [theta] using
      (show ¬Summable (fun n : ℕ => (1 : ℝ) / (n + 1)) by
        exact_mod_cast mt (summable_nat_add_iff 1).1
          Real.not_summable_one_div_natCast)
  have hmono : StrictMono time := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact (sparseTimesOn_succ P hP alpha hα m).1
    | succ n hmn ih => exact ih.trans (sparseTimesOn_succ P hP alpha hα n).1
  have hPtime : ∀ n, P (time n) := by
    intro n
    cases n with
    | zero => exact (Nat.find_spec (exists_sparseTimesOn_zero P hP alpha hα)).1
    | succ n => exact (sparseTimesOn_succ P hP alpha hα n).2.1
  have hmesh : ∀ n, alpha (time n) ≤ (1 / 2 : ℝ) ^ n := by
    intro n
    cases n with
    | zero =>
        change alpha (sparseTimesOn P hP alpha hα 0) ≤ 1
        unfold sparseTimesOn
        exact (Nat.find_spec (exists_sparseTimesOn_zero P hP alpha hα)).2
    | succ n =>
        simpa [div_pow] using (sparseTimesOn_succ P hP alpha hα n).2.2
  have hbound : ∀ n, theta n * alpha (time n) ≤ (1 / 2 : ℝ) ^ n := by
    intro n
    cases n with
    | zero =>
        calc
          theta 0 * alpha (time 0) ≤ alpha (time 0) := by
            rw [mul_comm]
            exact mul_le_of_le_one_right (halpha _) (by norm_num : theta 0 ≤ 1)
          _ ≤ 1 := by
            exact (Nat.find_spec (exists_sparseTimesOn_zero P hP alpha hα)).2
    | succ n =>
        have hm := (sparseTimesOn_succ P hP alpha hα n).2.2
        have hp := mul_le_mul_of_nonneg_left hm (hpos (n + 1)).le
        have hθ : theta (n + 1) ≤ 1 := by
          dsimp [theta]
          rw [one_div]
          apply (inv_le_one₀ (by positivity)).2
          have hn : (0 : ℝ) ≤ (n + 1 : ℕ) := by positivity
          linarith
        calc
          theta (n + 1) * alpha (time (n + 1)) ≤
              theta (n + 1) * (1 / 2 ^ (n + 1) : ℝ) := by simpa [time] using hp
          _ ≤ 1 / 2 ^ (n + 1) := mul_le_of_le_one_left (by positivity) hθ
          _ = (1 / 2 : ℝ) ^ (n + 1) := by rw [div_pow]; norm_num
  have hgeom : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) := by
    apply summable_geometric_of_norm_lt_one
    norm_num
  have hthetaLe : ∀ n, theta n ≤ 1 := by
    intro n
    dsimp [theta]
    rw [one_div]
    apply (inv_le_one₀ (by positivity)).2
    have hn : (0 : ℝ) ≤ (n : ℕ) := by positivity
    linarith
  exact ⟨time, theta, hPtime, hmono, hmesh, hpos, hthetaLe, hzero, hdiv,
    Summable.of_nonneg_of_le (fun n => mul_nonneg (hpos n).le (halpha _)) hbound
      hgeom⟩

/-- A sparse schedule with a divergent vanishing clock and summable collision
cost.  The nonnegativity assumption is needed only for the comparison proof.
-/
theorem exists_sparse_vanishing_nonsummable_schedule
    (alpha : ℕ → ℝ) (halpha : ∀ n, 0 ≤ alpha n)
    (hα : Tendsto alpha atTop (nhds 0)) :
    ∃ time : ℕ → ℕ, ∃ theta : ℕ → ℝ,
      StrictMono time ∧
      (∀ n, alpha (time n) ≤ (1 / 2 : ℝ) ^ n) ∧
      (∀ n, 0 < theta n) ∧ (∀ n, theta n ≤ 1) ∧
      Tendsto theta atTop (nhds 0) ∧
      ¬Summable theta ∧
      Summable (fun n => theta n * alpha (time n)) := by
  obtain ⟨time, theta, _, hmono, hmesh, hpos, hle, hzero, hdiv,
      hcollision⟩ :=
    exists_sparse_vanishing_nonsummable_schedule_of_cofinal
      (fun _ => True) (fun start => ⟨start, le_rfl, trivial⟩)
      alpha halpha hα
  exact ⟨time, theta, hmono, hmesh, hpos, hle, hzero, hdiv, hcollision⟩

end Math

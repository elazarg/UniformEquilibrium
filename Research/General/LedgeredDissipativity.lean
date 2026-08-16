/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib

/-!
# Ledgered dissipativity telescoping

This file proves the deterministic algebra underneath the dynamic
signal-processing interpretation of an adaptive certificate. It deliberately
does not construct a strategy, potential, target, or charge process.
-/

namespace Math
namespace LedgeredDissipativity

open scoped BigOperators

theorem prefix_error_le_of_step_dissipative
    (stageError potential charge : ℕ → ℝ)
    (epsilon : ℝ)
    (N : ℕ)
    (step : ∀ t < N,
      stageError t + (potential (t + 1) - potential t) ≤
        epsilon + (charge (t + 1) - charge t)) :
    (∑ t ∈ Finset.range N, stageError t) ≤
      (N : ℝ) * epsilon + (charge N - charge 0) +
        (potential 0 - potential N) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have ih' := ih (fun t ht => step t (Nat.lt_trans ht (Nat.lt_succ_self N)))
      have last := step N (Nat.lt_succ_self N)
      rw [Finset.sum_range_succ]
      push_cast
      linarith

theorem average_error_le
    (stageError potential charge : ℕ → ℝ)
    (epsilon bill storageBound : ℝ)
    (N : ℕ)
    (N_pos : 0 < N)
    (step : ∀ t < N,
      stageError t + (potential (t + 1) - potential t) ≤
        epsilon + (charge (t + 1) - charge t))
    (charge_growth : charge N - charge 0 ≤ bill)
    (storage_boundary : potential 0 - potential N ≤ storageBound) :
    (∑ t ∈ Finset.range N, stageError t) / N ≤
      epsilon + (bill + storageBound) / N := by
  have hprefix :
      (∑ t ∈ Finset.range N, stageError t) ≤
        (N : ℝ) * epsilon + (charge N - charge 0) +
          (potential 0 - potential N) :=
    prefix_error_le_of_step_dissipative
      stageError potential charge epsilon N step
  have N_real_pos : (0 : ℝ) < N := by exact_mod_cast N_pos
  apply (div_le_iff₀ N_real_pos).2
  calc
    ∑ t ∈ Finset.range N, stageError t ≤
        (N : ℝ) * epsilon + (charge N - charge 0) +
          (potential 0 - potential N) := hprefix
    _ ≤ (N : ℝ) * epsilon + bill + storageBound := by linarith
    _ = (epsilon + (bill + storageBound) / N) * N := by
      field_simp
      ring

end LedgeredDissipativity
end Math

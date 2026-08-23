/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic.Linarith

/-!
# Suprema of convergent tails

The supremum of every translated tail of a convergent real sequence converges
to the same limit.  No monotonicity assumption on the original sequence is
needed.
-/

namespace Math

open Filter

/-- Suprema of translated tails preserve the limit of a real sequence. -/
theorem tendsto_csSup_range_natAdd_of_tendsto {u : ℕ → ℝ} {a : ℝ}
    (hu : Tendsto u atTop (nhds a)) :
    Tendsto (fun start ↦ sSup (Set.range fun offset ↦ u (start + offset)))
      atTop (nhds a) := by
  rw [Metric.tendsto_atTop] at hu ⊢
  intro ε hε
  obtain ⟨cutoff, hcutoff⟩ := hu (ε / 2) (by positivity)
  refine ⟨cutoff, fun start hstart ↦ ?_⟩
  let shifted : ℕ → ℝ := fun offset ↦ u (start + offset)
  have hclose : ∀ offset, dist (shifted offset) a < ε / 2 := by
    intro offset
    exact hcutoff (start + offset) (hstart.trans (Nat.le_add_right start offset))
  have hbdd : BddAbove (Set.range shifted) := by
    refine ⟨a + ε / 2, ?_⟩
    rintro value ⟨offset, rfl⟩
    have h := hclose offset
    rw [Real.dist_eq] at h
    have hright := (abs_lt.mp h).2
    linarith
  have hupper : sSup (Set.range shifted) ≤ a + ε / 2 := by
    apply csSup_le (Set.range_nonempty shifted)
    rintro value ⟨offset, rfl⟩
    have h := hclose offset
    rw [Real.dist_eq] at h
    have hright := (abs_lt.mp h).2
    linarith
  have hlower : a - ε / 2 < sSup (Set.range shifted) := by
    have hone := le_csSup hbdd (Set.mem_range_self 0 : shifted 0 ∈ Set.range shifted)
    have h := hclose 0
    rw [Real.dist_eq] at h
    have hleft := (abs_lt.mp h).1
    linarith
  change dist (sSup (Set.range shifted)) a < ε
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end Math

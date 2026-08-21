/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Limits of adaptive Euler prefixes

An adaptive Euler construction can encounter a Zeno prefix: infinitely many
positive steps whose accumulated time is finite. If its velocities are
uniformly bounded, then its states nevertheless converge. Closed constraints
retain the limit, so this endpoint is available for restarting the construction.
-/

namespace Math
namespace Viability

open Filter Set

variable {State : Type*} [PseudoMetricSpace State] [CompleteSpace State]

/-- A sequence whose successive displacements are bounded by a constant
times a summable nonnegative step schedule converges. -/
theorem exists_tendsto_of_summable_step_bound
    (state : ℕ → State) (step : ℕ → ℝ) (speedBound : ℝ)
    (hmove : ∀ n, dist (state n) (state (n + 1)) ≤ speedBound * step n)
    (hsummable : Summable step) :
    ∃ limit, Tendsto state atTop (nhds limit) := by
  have hboundSummable : Summable (fun n => speedBound * step n) :=
    hsummable.mul_left speedBound
  have hcauchy : CauchySeq state :=
    cauchySeq_of_dist_le_of_summable (fun n => speedBound * step n)
      (fun n => hmove n) hboundSummable
  exact cauchySeq_tendsto_of_complete hcauchy

/-- A Zeno Euler prefix in a closed constraint converges to another point of
the constraint. This is the state from which a maximal construction restarts. -/
theorem exists_tendsto_mem_of_summable_step_bound
    {constraint : Set State} (hconstraint : IsClosed constraint)
    (state : ℕ → State) (hstate : ∀ n, state n ∈ constraint)
    (step : ℕ → ℝ) (speedBound : ℝ)
    (hmove : ∀ n, dist (state n) (state (n + 1)) ≤ speedBound * step n)
    (hsummable : Summable step) :
    ∃ limit ∈ constraint, Tendsto state atTop (nhds limit) := by
  obtain ⟨limit, hlimit⟩ := exists_tendsto_of_summable_step_bound
    state step speedBound hmove hsummable
  exact ⟨limit, hconstraint.mem_of_tendsto hlimit (Eventually.of_forall hstate), hlimit⟩

/-- The clock accumulated from an initial time along a summable step schedule
converges to the initial time plus the total step mass. -/
theorem tendsto_partialSum_add_of_summable
    (start : ℝ) {step : ℕ → ℝ} (hsummable : Summable step) :
    Tendsto (fun n => start + ∑ k ∈ Finset.range n, step k) atTop
      (nhds (start + ∑' k, step k)) := by
  exact tendsto_const_nhds.add hsummable.hasSum.tendsto_sum_nat

end Viability
end Math

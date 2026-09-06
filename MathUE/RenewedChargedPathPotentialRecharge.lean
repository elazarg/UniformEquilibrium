/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import MathUE.PathFamilyPotentialRecharge
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Potential recharge across renewed charged paths

A renewed path sequence alternates a charged vertical path with an
unconstrained horizontal move.  The horizontal target is required to be
literally the source of the next vertical path.  A potential therefore makes
the vertical charge telescope against the signed potential restored by the
horizontal moves.

The structure is supplied data.  It does not construct the next source,
assert that a horizontal move is an admissible edge, or provide a renewal
mechanism.
-/

open scoped BigOperators

namespace Math
namespace ChargedPathBudget
namespace ChargedRelation

universe u v

variable {State : Type u} {Edge : Type v}
variable {R : ChargedRelation State Edge}

/-- Supplied positively charged vertical paths with literal horizontal
renewal into the next source.  Horizontal moves need not be edges of `R`. -/
structure RenewedPathSequence (R : ChargedRelation State Edge) where
  /-- Source of each vertical path. -/
  source : ℕ → State
  /-- Endpoint of each vertical path. -/
  endpoint : ℕ → State
  /-- Target reached by the unconstrained horizontal move. -/
  horizontalTarget : ℕ → State
  /-- Literal charged path from the phase source to its endpoint. -/
  verticalPath : ∀ phase, R.Path (source phase) (endpoint phase)
  /-- The horizontal target is exactly reused as the next phase source. -/
  horizontalTarget_eq_nextSource : ∀ phase,
    horizontalTarget phase = source (phase + 1)
  /-- One common lower bound for all vertical charges. -/
  minimumCharge : ℝ
  /-- The common charge lower bound is strictly positive. -/
  minimumCharge_pos : 0 < minimumCharge
  /-- Every supplied vertical path pays the common positive charge. -/
  minimumCharge_le_verticalCharge : ∀ phase,
    minimumCharge ≤ (verticalPath phase).chargeSum

namespace RenewedPathSequence

/-- Signed potential restored by the horizontal move after one vertical
path. -/
def potentialRecharge (sequence : RenewedPathSequence R)
    (potential : State → ℝ) (phase : ℕ) : ℝ :=
  potential (sequence.horizontalTarget phase) -
    potential (sequence.endpoint phase)

/-- Exact finite telescope relating horizontal recharge to vertical potential
drops and the two boundary source potentials. -/
theorem sum_potentialRecharge_eq_sum_verticalPotentialDrop_add_boundary
    (sequence : RenewedPathSequence R)
    (potential : State → ℝ) (horizon : ℕ) :
    (∑ phase ∈ Finset.range horizon,
        sequence.potentialRecharge potential phase) =
      (∑ phase ∈ Finset.range horizon,
        (potential (sequence.source phase) -
          potential (sequence.endpoint phase))) +
        potential (sequence.source horizon) -
        potential (sequence.source 0) := by
  simp_rw [potentialRecharge, sequence.horizontalTarget_eq_nextSource]
  have hpoint : ∀ phase,
      potential (sequence.source (phase + 1)) -
          potential (sequence.endpoint phase) =
        (potential (sequence.source phase) -
            potential (sequence.endpoint phase)) +
          (potential (sequence.source (phase + 1)) -
            potential (sequence.source phase)) := by
    intro phase
    ring
  simp_rw [hpoint, Finset.sum_add_distrib]
  have htelescope :=
    Finset.sum_range_sub (fun phase => potential (sequence.source phase)) horizon
  linarith

/-- Potential decrease along every vertical path forces the sum of
horizontal recharge to cover all vertical charges, up to the source boundary
term. -/
theorem sum_verticalCharge_add_terminalPotentialDifference_le_sum_recharge
    (sequence : RenewedPathSequence R)
    (potential : State → ℝ) (hpotential : R.IsPotential potential)
    (horizon : ℕ) :
    (∑ phase ∈ Finset.range horizon,
        (sequence.verticalPath phase).chargeSum) +
        potential (sequence.source horizon) -
        potential (sequence.source 0) ≤
      ∑ phase ∈ Finset.range horizon,
        sequence.potentialRecharge potential phase := by
  simpa only [potentialRecharge, sequence.horizontalTarget_eq_nextSource] using
    sum_pathFamily_charge_add_boundary_le_sum_recharge
      sequence.source sequence.endpoint sequence.verticalPath potential hpotential horizon

/-- A common positive vertical charge produces linear horizontal potential
recharge, modulo the exact two source boundary values. -/
theorem card_mul_minimumCharge_add_terminalPotentialDifference_le_sum_recharge
    (sequence : RenewedPathSequence R)
    (potential : State → ℝ) (hpotential : R.IsPotential potential)
    (horizon : ℕ) :
    (horizon : ℝ) * sequence.minimumCharge +
        potential (sequence.source horizon) -
        potential (sequence.source 0) ≤
      ∑ phase ∈ Finset.range horizon,
        sequence.potentialRecharge potential phase := by
  have hminimum :
      (horizon : ℝ) * sequence.minimumCharge ≤
        ∑ phase ∈ Finset.range horizon,
          (sequence.verticalPath phase).chargeSum := by
    calc
      (horizon : ℝ) * sequence.minimumCharge =
          ∑ _phase ∈ Finset.range horizon, sequence.minimumCharge := by
        simp
      _ ≤ ∑ phase ∈ Finset.range horizon,
          (sequence.verticalPath phase).chargeSum := by
        exact Finset.sum_le_sum fun phase _ =>
          sequence.minimumCharge_le_verticalCharge phase
  have hcharge :=
    sequence.sum_verticalCharge_add_terminalPotentialDifference_le_sum_recharge
      potential hpotential horizon
  linarith

/-- For the canonical budget-to-go potential, horizontal recharge is at
least the linear vertical expenditure minus the global finite path budget.
-/
theorem card_mul_minimumCharge_sub_budget_le_sum_valueRecharge
    (sequence : RenewedPathSequence R)
    (hbudget : R.HasFiniteBudget) (horizon : ℕ) :
    (horizon : ℝ) * sequence.minimumCharge - R.budget ≤
      ∑ phase ∈ Finset.range horizon,
        sequence.potentialRecharge R.value phase := by
  have hrecharge :=
    sequence.card_mul_minimumCharge_add_terminalPotentialDifference_le_sum_recharge
      R.value (R.value_isBoundedPotential hbudget).isPotential horizon
  have hterminal := R.value_nonneg hbudget (sequence.source horizon)
  have hinitial := R.value_le_budget hbudget (sequence.source 0)
  linarith

end RenewedPathSequence
end ChargedRelation
end ChargedPathBudget
end Math

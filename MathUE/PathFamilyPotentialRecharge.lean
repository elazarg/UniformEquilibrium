import MathUE.ChargedPathBudget
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-! # Potential recharge along arbitrary finite-path families

No positive minimum phase expenditure or horizontal-edge condition is required.
-/

noncomputable section

open scoped BigOperators

namespace Math.ChargedPathBudget.ChargedRelation

variable {State Edge : Type*} {relation : ChargedRelation State Edge}

/-- Arbitrary path families telescope against the horizontal moves to their next sources. -/
theorem sum_pathFamily_charge_add_boundary_le_sum_recharge
    (source endpoint : ℕ → State)
    (path : ∀ phase, relation.Path (source phase) (endpoint phase))
    (potential : State → ℝ) (hpotential : relation.IsPotential potential) (horizon : ℕ) :
    (∑ phase ∈ Finset.range horizon, (path phase).chargeSum) + potential (source horizon) -
        potential (source 0) ≤
      ∑ phase ∈ Finset.range horizon,
        (potential (source (phase + 1)) - potential (endpoint phase)) := by
  have hcharge : (∑ phase ∈ Finset.range horizon, (path phase).chargeSum) ≤
      ∑ phase ∈ Finset.range horizon,
        (potential (source phase) - potential (endpoint phase)) :=
    Finset.sum_le_sum fun phase _ ↦ hpotential.chargeSum_le (path phase)
  have htelescope := Finset.sum_range_sub (fun phase ↦ potential (source phase)) horizon
  simp only [Finset.sum_sub_distrib] at hcharge htelescope ⊢
  linarith

/-- Finite budget allows the terminal capacity to be dropped, without any phase-charge floor. -/
theorem sum_pathFamily_charge_sub_initialValue_le_sum_valueRecharge
    (source endpoint : ℕ → State)
    (path : ∀ phase, relation.Path (source phase) (endpoint phase))
    (hbudget : relation.HasFiniteBudget) (horizon : ℕ) :
    (∑ phase ∈ Finset.range horizon, (path phase).chargeSum) - relation.value (source 0) ≤
      ∑ phase ∈ Finset.range horizon,
        (relation.value (source (phase + 1)) - relation.value (endpoint phase)) := by
  have hledger := sum_pathFamily_charge_add_boundary_le_sum_recharge source endpoint path
    relation.value (relation.value_isBoundedPotential hbudget).isPotential horizon
  have hterminal := relation.value_nonneg hbudget (source horizon)
  linarith

end Math.ChargedPathBudget.ChargedRelation

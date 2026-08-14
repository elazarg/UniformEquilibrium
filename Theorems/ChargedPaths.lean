import MathUE.ChargedPathBudget

/-!
# Finite path budgets and bounded potentials

Reader-facing statement of the charged-path budget theorem. The canonical
proof remains in `MathUE.ChargedPathBudget`.
-/

namespace Theorems.ChargedPaths

open Math.ChargedPathBudget

universe u v

/-- A nonnegative charged relation has a finite path budget exactly when it
admits a bounded potential. -/
theorem finiteBudget_iff_exists_boundedPotential
    {State : Type u} {Edge : Type v} (R : ChargedRelation State Edge) :
    R.HasFiniteBudget ↔ ∃ Φ : State → ℝ, R.IsBoundedPotential Φ := by
  exact R.hasFiniteBudget_iff_exists_boundedPotential

end Theorems.ChargedPaths

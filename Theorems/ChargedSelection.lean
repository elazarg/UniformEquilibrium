import MathUE.ChargedPathSelection

/-!
# Renewal and divergent charged paths

Reader-facing statement of the charged-path renewal theorem. The canonical
proof remains in `MathUE.ChargedPathSelection`.
-/

namespace Theorems.ChargedSelection

open Math.ChargedPathBudget

universe u v

/-- Charge renewal is exactly what lets every unbounded finite charge be
consolidated into one divergent infinite path. -/
theorem renewal_iff_unboundedFiniteCharge_implies_divergentPath
    {State : Type u} {Edge : Type v} (R : ChargedRelation State Edge) :
    R.ChargeRenewal ↔
      ∀ start, R.HasUnboundedFiniteCharge start → R.CanDiverge start := by
  exact R.chargeRenewal_iff_unboundedFiniteCharge_implies_canDiverge

end Theorems.ChargedSelection

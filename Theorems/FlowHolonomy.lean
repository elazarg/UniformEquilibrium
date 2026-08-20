import MathUE.LinearAlgebra.OwnerLabeledFlowHolonomy

/-!
# Flow holonomy and account potentials

Reader-facing statement of the finite gluing/potential duality. The canonical
proof remains in `MathUE.LinearAlgebra.OwnerLabeledFlowHolonomy`.
-/

namespace Theorems.FlowHolonomy

open Math.LinearAlgebra.OwnerLabeledFlowHolonomy

/-- A charge has nonpositive holonomy on every circulation exactly when a
scalar account potential discharges every row charge. -/
theorem zeroHolonomy_iff_exists_accountPotential
    {R V : Type*} [Fintype R] [Fintype V] [DecidableEq V]
    (src : R → V) (P : R → V → ℝ) (c : R → ℝ) :
    ZeroHolonomy src P c ↔
      ∃ H : V → ℝ, IsAccountPotential src P c H := by
  exact
    Math.LinearAlgebra.OwnerLabeledFlowHolonomy.zeroHolonomy_iff_exists_accountPotential
      src P c

end Theorems.FlowHolonomy

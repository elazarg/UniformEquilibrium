import MathUE.LinearAlgebra.OwnerTypedDualLifting

/-!
# Owner-visible dual lifting

Reader-facing statement of the typed-lift characterization. The canonical
proof remains in `MathUE.LinearAlgebra.OwnerTypedDualLifting`.
-/

namespace Theorems.TypedLifting

open Math.LinearAlgebra.OwnerTypedDualLifting

/-- Under full-system feasibility, an owner-typed lift exists exactly when the
inequality is valid on that owner's visible relaxation. -/
theorem hasTypedLift_iff_validOnVisible
    {Ω E N U Y T : Type*}
    [Fintype Y] [Fintype T] [Fintype E] [Fintype N] [Fintype U]
    (P : TypedCell Ω E N U Y T)
    (i : Ω) (α : T → ℝ) (β : ℝ) (hfeas : ∃ y t, MemFull P y t) :
    HasTypedLift P i α β ↔ ValidOnVisible P i α β := by
  exact hasTypedLift_iff_validOnVisible_of_full P i α β hfeas

end Theorems.TypedLifting

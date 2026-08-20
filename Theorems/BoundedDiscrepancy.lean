import MathUE.BoundedDiscrepancyCirculation

/-!
# Bounded discrepancy and connected integer circulations

Reader-facing statement of the finite certificate theorem. The canonical
proof remains in `MathUE.BoundedDiscrepancyCirculation`.
-/

namespace Theorems.BoundedDiscrepancy

open Math

universe uV uE uκ

/-- Over finite vertices and integer-lattice charges, a bounded-discrepancy
infinite walk exists exactly when a reachable connected zero-charge integer
circulation exists. -/
theorem exists_walk_iff_connectedIntegerCirculation
    {V : Type uV} {E : Type uE} (G : Math.EdgeGraph V E)
    [Finite V] [Fintype E] [DecidableEq V]
    {κ : Type uκ} (edgeCharge : E → κ → ℤ) (start : V) :
    (∃ walk : G.InfiniteWalk start,
      walk.HasBoundedDiscrepancy edgeCharge) ↔
      Nonempty (G.ReachableConnectedIntegerCirculation edgeCharge start) := by
  exact G.exists_boundedDiscrepancy_iff_reachableConnectedIntegerCirculation
    edgeCharge start

end Theorems.BoundedDiscrepancy

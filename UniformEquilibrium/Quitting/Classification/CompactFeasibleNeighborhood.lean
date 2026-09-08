import Mathlib.Analysis.Convex.Topology
import UniformEquilibrium.Quitting.Classification.SimonFiniteOrbit.SuppliedCorrespondence

/-!
# Compact closed neighborhoods of the feasible payoff set

The feasible payoff set is the convex hull of finitely many terminal reward
vectors and zero. Its closed norm neighborhood is therefore compact in the
finite-dimensional payoff space.
-/

noncomputable section

namespace GameTheory

open Set StochasticGame

variable {ι : Type} [Fintype ι]

/-- The closed norm neighborhood of the feasible payoff set. -/
def QuittingFeasibleClosedNeighborhood
    (reward : {coalition : Finset ι // coalition.Nonempty} → Payoff ι)
    (radius : ℝ) : Set (Payoff ι) :=
  {point | ∃ feasible,
    QuittingSimonFeasiblePayoff reward feasible ∧
      ‖point - feasible‖ ≤ radius}

/-- A closed norm neighborhood of the finite feasible payoff polytope is
compact. -/
theorem isCompact_quittingFeasibleClosedNeighborhood
    (reward : {coalition : Finset ι // coalition.Nonempty} → Payoff ι)
    (radius : ℝ) :
    IsCompact (QuittingFeasibleClosedNeighborhood reward radius) := by
  let feasibleSet : Set (Payoff ι) :=
    convexHull ℝ (Set.range reward ∪ {0})
  have hfeasible : IsCompact feasibleSet :=
    ((Set.finite_range reward).union (Set.finite_singleton 0)).isCompact_convexHull ℝ
  have hoffset : IsCompact (Metric.closedBall (0 : Payoff ι) radius) :=
    isCompact_closedBall 0 radius
  have hsum : IsCompact
      ((fun pair : Payoff ι × Payoff ι ↦ pair.1 + pair.2) ''
        (feasibleSet ×ˢ Metric.closedBall 0 radius)) :=
    (hfeasible.prod hoffset).image (continuous_fst.add continuous_snd)
  rw [show QuittingFeasibleClosedNeighborhood reward radius =
      (fun pair : Payoff ι × Payoff ι ↦ pair.1 + pair.2) ''
        (feasibleSet ×ˢ Metric.closedBall 0 radius) by
    ext point
    constructor
    · rintro ⟨feasible, hfeasiblePoint, hdistance⟩
      refine ⟨(feasible, point - feasible), ?_, by simp⟩
      refine ⟨hfeasiblePoint, ?_⟩
      simpa only [Metric.mem_closedBall, dist_zero_right] using hdistance
    · rintro ⟨pair, ⟨hfeasiblePoint, hoffsetPoint⟩, rfl⟩
      refine ⟨pair.1, hfeasiblePoint, ?_⟩
      simpa only [add_sub_cancel_left, Metric.mem_closedBall, dist_zero_right]
        using hoffsetPoint]
  exact hsum

end GameTheory

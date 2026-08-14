import MathUE.LinearAlgebra.MixedCompatibilityAlternative

/-!
# A normalized mixed-owner compatibility alternative

Reader-facing statement of the mixed-owner Farkas alternative. The canonical
proof remains in `MathUE.LinearAlgebra.MixedCompatibilityAlternative`.
-/

namespace Theorems.MixedObstruction

open Math.LinearAlgebra

/-- If every owner-specific subsystem is feasible, then either the coupled
system is feasible or it has a normalized positive obstruction supported by
constraints belonging to at least two distinct owners. -/
theorem coupledFeasible_or_genuinelyMixedObstruction
    {Facet Player : Type*}
    [Fintype Facet] [Fintype Player] [Nonempty Player]
    {Constraint : Player → Type*}
    [∀ player, Fintype (Constraint player)]
    {n : ℕ}
    (facetNormal : Facet → Fin n → ℝ)
    (facetRhs : Facet → ℝ)
    (playerNormal : ∀ player, Constraint player → Fin n → ℝ)
    (playerRhs : ∀ player, Constraint player → ℝ)
    (hplayerFeasible : ∀ player, IsFeasible
      (playerSubsystemNormal facetNormal playerNormal player)
      (playerSubsystemRelaxedRhs facetRhs playerRhs 0 player)) :
    IsFeasible
      (coupledNormal facetNormal playerNormal)
      (coupledRelaxedRhs facetRhs playerRhs 0) ∨
    Nonempty
      (NormalizedGenuinelyMixedCompatibilityObstruction
        facetNormal facetRhs playerNormal playerRhs) := by
  exact coupledFeasible_or_normalizedGenuinelyMixedObstruction
    facetNormal facetRhs playerNormal playerRhs hplayerFeasible

end Theorems.MixedObstruction

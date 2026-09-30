import MathUE.RealQuantifierElimination.AlgebraicWitnesses
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseRationalFormula
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseEscape

/-! # Algebraic witnesses for rational crossed degree escape

This is an existence adapter for the auxiliary crossed fixed point. Original-game
Nash conclusions still require the actual source guards. No rational search or
accuracy-dependent finite enumeration is asserted here.
-/

noncomputable section

namespace GameTheory

open Math.LinearProgramming

variable {n : ℕ}

/-- Every existing nonzero crossed fixed point for rational data can be replaced
by one with algebraic hazards, without excluding boundary faces. -/
theorem exists_isAlgebraic_nonzero_quittingCrossedClippedMap_fixedPoint_of_exists
    (reward : RationalQuittingReward n) (first second : Fin n) (height : ℚ)
    (hheight : 0 < (height : ℝ))
    (hexists : ∃ hazard : Fin n → ℝ, hazard ≠ 0 ∧
      quittingCrossedClippedMap (rationalQuittingRewardToReal reward)
        first second (height : ℝ) hazard = hazard) :
    ∃ hazard : Fin n → ℝ, (∀ coordinate, IsAlgebraic ℚ (hazard coordinate)) ∧
      hazard ≠ 0 ∧ quittingCrossedClippedMap (rationalQuittingRewardToReal reward)
        first second (height : ℝ) hazard = hazard := by
  have hformula : ∃ hazard : Fin n → ℝ,
      (rationalQuittingCrossedFixedPointFormula reward first second height).HoldsAt hazard := by
    obtain ⟨hazard, hnonzero, hfixed⟩ := hexists
    exact ⟨hazard, (rationalQuittingCrossedFixedPointFormula_holdsAt_iff
      reward first second height hheight hazard).mpr ⟨hnonzero, hfixed⟩⟩
  let formula := rationalQuittingCrossedFixedPointFormula reward first second height
  obtain ⟨hazard, halgebraic, hholds⟩ :=
    formula.exists_isAlgebraic_environment_of_exists_holdsAt hformula
  exact ⟨hazard, halgebraic, (rationalQuittingCrossedFixedPointFormula_holdsAt_iff
    reward first second height hheight hazard).mp hholds⟩

/-- Actual R0/nonunit-degree source data produce an algebraic auxiliary witness;
neither an initial root nor a regular-fiber condition is supplied. -/
theorem exists_isAlgebraic_nonzero_quittingCrossedClippedMap_fixedPoint
    (reward : RationalQuittingReward n) (first second : Fin n) (height : ℚ)
    (hheight : 0 < (height : ℝ)) (hheightOne : (height : ℝ) ≤ 1)
    (hR0 : IsR0Matrix (quittingCrossedSingletonMatrix
      (rationalQuittingRewardToReal reward) first second))
    (hdegree : r0Degree (quittingCrossedSingletonMatrix
      (rationalQuittingRewardToReal reward) first second) hR0 ≠ 1) :
    ∃ hazard : Fin n → ℝ, (∀ coordinate, IsAlgebraic ℚ (hazard coordinate)) ∧
      hazard ≠ 0 ∧ quittingCrossedClippedMap (rationalQuittingRewardToReal reward)
        first second (height : ℝ) hazard = hazard := by
  apply exists_isAlgebraic_nonzero_quittingCrossedClippedMap_fixedPoint_of_exists
    reward first second height hheight
  exact exists_nonzero_quittingCrossedClippedMap_fixedPoint
    (rationalQuittingRewardToReal reward) first second (height : ℝ)
      hheight hheightOne hR0 hdegree

end GameTheory

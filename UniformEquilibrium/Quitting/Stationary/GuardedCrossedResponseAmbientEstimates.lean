import MathUE.LinearProgramming.R0MinMapCoercivity
import UniformEquilibrium.Quitting.Stationary.DiscountedAmbientQuadraticRemainder
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseLocal

/-! # Literal ambient remainder and R0 margin for the crossed source

These supporting estimates supplement the existing degree proof. They require
neither regular zeros nor finite fibers and do not change the source game.
-/

noncomputable section

namespace GameTheory

open Filter Math.LinearProgramming
open scoped Topology ContDiff

variable {n : ℕ}

/-- The actual `-PΔ` differs quadratically from the actual `PΓ` linear field. -/
theorem exists_quittingCrossedResponse_quadratic_bound
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) :
    ∃ constant > 0, ∃ radius > 0, ∀ hazard : Fin n → ℝ, ‖hazard‖ < radius →
      ‖-quittingCrossedResponse reward first second hazard -
        (quittingCrossedSingletonMatrix reward first second).mulVec hazard‖ ≤
          constant * ‖hazard‖ ^ 2 := by
  let function := quittingCrossedResponse reward first second
  have hanalytic : AnalyticAt ℝ function 0 := by
    have hdiff : ContDiff ℝ ω function := by
      unfold function quittingCrossedResponse quittingDiscountedDisplacement
        continueMassExcl sigmaValue excludedValue
      fun_prop
    exact hdiff.contDiffAt.analyticAt
  obtain ⟨constant, hconstant, radius, hradius, hbound⟩ :=
    Math.exists_quadratic_remainder_bound_of_analyticAt_zero hanalytic
      hanalytic.differentiableAt.hasFDerivAt
  refine ⟨constant, hconstant, radius, hradius, fun hazard hsmall => ?_⟩
  have hsource := hbound hazard hsmall
  change ‖quittingCrossedResponse reward first second hazard -
    quittingCrossedResponse reward first second 0 -
    fderiv ℝ (quittingCrossedResponse reward first second) 0 hazard‖ ≤ _ at hsource
  rw [quittingCrossedResponse_zero, sub_zero,
    quittingCrossedResponse_derivative_apply, sub_neg_eq_add] at hsource
  simpa only [sub_eq_add_neg, ← neg_add, norm_neg] using hsource

/-- The crossed R0 hypothesis supplies the global signed minimum-map margin. -/
theorem exists_quittingCrossedSingleton_minMap_margin
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n)
    (hR0 : IsR0Matrix (quittingCrossedSingletonMatrix reward first second)) :
    ∃ constant > 0, ∀ point : Fin n → ℝ,
      constant * ‖point‖ ≤
        ‖lcpMinMap (quittingCrossedSingletonMatrix reward first second) 0 point‖ :=
  exists_pos_mul_norm_le_lcpMinMap_zero _ hR0

end GameTheory

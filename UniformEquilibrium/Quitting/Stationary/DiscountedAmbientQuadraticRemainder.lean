import MathUE.Analysis.AnalyticQuadraticRemainder
import UniformEquilibrium.Quitting.Stationary.DiscountedAmbientDerivative

/-! # Quadratic displacement remainder on the full ambient space

Unlike the probabilistic reward-box bound, these existential constants apply
also to negative hazards and negative discounts. They are derived from the
actual finite product formula and its established singleton derivative.
-/

noncomputable section

namespace GameTheory

open QuittingLCPClassification
open scoped ContDiff

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The joint discount/hazard displacement is analytic on the entire space. -/
theorem analyticAt_quittingDiscountedDisplacement
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (point : ℝ × (ι → ℝ)) :
    AnalyticAt ℝ (fun input : ℝ × (ι → ℝ) =>
      quittingDiscountedDisplacement reward input.1 input.2) point := by
  have hdiff : ContDiff ℝ ω (fun input : ℝ × (ι → ℝ) =>
      quittingDiscountedDisplacement reward input.1 input.2) := by
    unfold quittingDiscountedDisplacement continueMassExcl sigmaValue excludedValue
    fun_prop
  exact hdiff.contDiffAt.analyticAt

/-- One constant bounds all recipient remainders in the ambient product norm. -/
theorem exists_ambient_quittingDiscountedSingletonRemainder_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∃ constant > 0, ∃ radius > 0, ∀ discount : ℝ, ∀ hazard : ι → ℝ,
      ‖(discount, hazard)‖ < radius →
      ‖quittingDiscountedSingletonRemainder reward discount hazard‖ ≤
        constant * ‖(discount, hazard)‖ ^ 2 := by
  let linear := ContinuousLinearMap.pi (quittingDiscountedSingletonLinearization reward)
  have hderivative : HasFDerivAt (fun input : ℝ × (ι → ℝ) =>
      quittingDiscountedDisplacement reward input.1 input.2) linear 0 :=
    hasFDerivAt_pi.mpr (hasFDerivAt_quittingDiscountedDisplacement_zero reward)
  obtain ⟨constant, hconstant, radius, hradius, hbound⟩ :=
    Math.exists_quadratic_remainder_bound_of_analyticAt_zero
      (analyticAt_quittingDiscountedDisplacement reward 0) hderivative
  refine ⟨constant, hconstant, radius, hradius, fun discount hazard hsmall => ?_⟩
  have hequal : (quittingDiscountedDisplacement reward discount hazard -
      quittingDiscountedDisplacement reward 0 0 - linear (discount, hazard)) =
      quittingDiscountedSingletonRemainder reward discount hazard := by
    funext who
    simp only [Pi.sub_apply, quittingDiscountedDisplacement_zero,
      ContinuousLinearMap.pi_apply, linear, quittingDiscountedSingletonLinearization_apply,
      quittingDiscountedSingletonRemainder]
    ring
  simpa only [Prod.fst_zero, Prod.snd_zero, hequal] using hbound (discount, hazard) hsmall

/-- Literal undiscounted packet expansion on a full signed ambient ball. -/
theorem exists_ambient_quittingDisplacement_singleton_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∃ constant > 0, ∃ radius > 0, ∀ hazard : ι → ℝ, ‖hazard‖ < radius →
      ‖quittingDiscountedDisplacement reward 0 hazard +
        (quittingSingletonMatrix reward).mulVec hazard‖ ≤ constant * ‖hazard‖ ^ 2 := by
  obtain ⟨constant, hconstant, radius, hradius, hbound⟩ :=
    exists_ambient_quittingDiscountedSingletonRemainder_bound reward
  refine ⟨constant, hconstant, radius, hradius, fun hazard hsmall => ?_⟩
  have hequal : quittingDiscountedSingletonRemainder reward 0 hazard =
      quittingDiscountedDisplacement reward 0 hazard +
        (quittingSingletonMatrix reward).mulVec hazard := by
    funext who
    simp only [quittingDiscountedSingletonRemainder, zero_mul, sub_zero, Pi.add_apply,
      Matrix.mulVec, dotProduct, mul_comm]
  have hnorm : ‖((0 : ℝ), hazard)‖ = ‖hazard‖ := by
    simp only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg hazard)]
  have hsmall' : ‖((0 : ℝ), hazard)‖ < radius := by
    rwa [hnorm]
  simpa only [hequal, hnorm] using hbound 0 hazard hsmall'

end GameTheory

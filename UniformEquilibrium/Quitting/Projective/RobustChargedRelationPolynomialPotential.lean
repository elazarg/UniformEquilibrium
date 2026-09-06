import MathUE.Interval.RationalPolynomialChargedDrift
import UniformEquilibrium.Quitting.Projective.RobustChargedRelationTranslation

/-! # Rational polynomial compilation of a supplied smooth robust-edge potential

The theorem is conditional on one supplied global C¹ potential with actual drift on every
robust edge. It does not construct that smooth potential from finite capacity.
-/

noncomputable section

namespace GameTheory

open Math.Interval Math.Interval.RationalPolynomial

variable {dimension : ℕ}

/-- Actual absorption-relative displacement turns a supplied smooth robust-edge potential into
one rational polynomial potential on the entire same relation. No charge lower bound, normality,
punishment floor, or positivity assumption on the box or tolerance is required. -/
theorem exists_quittingRobustChargedRelation_rationalPotential_of_contDiff
    (reward : {coalition : Finset (Fin dimension) // coalition.Nonempty} → Payoff (Fin dimension))
    (rewardBound tolerance bound : ℝ)
    (hreward : ∀ terminal who, |reward terminal who| ≤ rewardBound)
    (potential : Payoff (Fin dimension) → ℝ) (hsmooth : ContDiff ℝ 1 potential)
    (hpotential : (quittingFloorFreeRobustChargedRelation reward tolerance bound).IsPotential
      (fun state ↦ potential state.1)) :
    ∃ expression : RationalPolynomial dimension,
      (quittingFloorFreeRobustChargedRelation reward tolerance bound).IsPotential
        (fun state ↦ evalReal state.1 expression) := by
  let domain : Set (Fin dimension → ℝ) := {point | ∀ coordinate, |point coordinate| ≤ bound}
  have hdomain : domain = Set.Icc (fun _ ↦ -bound) (fun _ ↦ bound) := by
    ext point
    simp only [domain, Set.mem_setOf_eq, Set.mem_Icc, Pi.le_def, abs_le, forall_and]
  have hconvex : Convex ℝ domain := by rw [hdomain]; exact convex_Icc _ _
  let displacementBound := max 1 (rewardBound + bound + tolerance)
  have hdisplacementBound : 0 < displacementBound := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hdisplacement (edge : QuittingRobustChargedEdge reward tolerance bound) :
      ‖edge.1.1.1.1 - edge.1.2.1‖ ≤ displacementBound *
        quittingRootAbsorptionMass (quittingRootOfSimplex edge.1.1.2) := by
    have habsorption := quittingRootAbsorptionMass_nonneg (quittingRootOfSimplex edge.1.1.2)
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hdisplacementBound.le habsorption)).mpr
    intro coordinate
    have hcoordinate := abs_quittingRobustChargedEdge_target_sub_source_le
      reward rewardBound tolerance bound hreward edge coordinate
    have hscale := mul_le_mul_of_nonneg_right
      (le_max_right 1 (rewardBound + bound + tolerance)) habsorption
    simpa only [Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm] using hcoordinate.trans hscale
  obtain ⟨expression, hexpression⟩ := exists_evalReal_charge_drift_of_contDiff domain
    (isCompact_quittingRobustChargedState bound) hconvex
    (fun edge : QuittingRobustChargedEdge reward tolerance bound ↦ edge.1.1.1.1)
    (fun edge ↦ edge.1.2.1)
    (fun edge ↦ quittingRootAbsorptionMass (quittingRootOfSimplex edge.1.1.2))
    (fun edge ↦ edge.1.1.1.2) (fun edge ↦ edge.1.2.2)
    displacementBound hdisplacementBound hdisplacement potential hsmooth
    (fun edge ↦ by
      have hedge := hpotential edge
      change potential edge.1.2.1 +
        quittingRootAbsorptionMass (quittingRootOfSimplex edge.1.1.2) ≤
          potential edge.1.1.1.1 at hedge
      linarith)
  refine ⟨expression, ?_⟩
  intro edge
  have hedge := hexpression edge
  change evalReal edge.1.2.1 expression +
    quittingRootAbsorptionMass (quittingRootOfSimplex edge.1.1.2) ≤
      evalReal edge.1.1.1.1 expression
  linarith

end GameTheory

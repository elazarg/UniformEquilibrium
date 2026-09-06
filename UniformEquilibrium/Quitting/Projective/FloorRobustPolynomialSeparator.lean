import MathUE.Interval.RationalPolynomialChargedDrift
import UniformEquilibrium.Quitting.Projective.FloorRobustCapacitySmoothing

/-! # Rational polynomial separators for robust relations with endpoint floors -/

noncomputable section

namespace GameTheory

open Math.Interval Math.Interval.RationalPolynomial

variable {dimension : ℕ}

/-- A supplied actual smooth potential on all floor-bearing edges compiles to a rational
polynomial on exactly that same relation. The floor vector is arbitrary. -/
theorem exists_quittingFloorRobustChargedRelation_rationalPotential_of_contDiff
    (reward : {coalition : Finset (Fin dimension) // coalition.Nonempty} → Payoff (Fin dimension))
    (floor : Payoff (Fin dimension)) (rewardBound tolerance bound : ℝ)
    (hreward : ∀ terminal who, |reward terminal who| ≤ rewardBound)
    (potential : Payoff (Fin dimension) → ℝ) (hsmooth : ContDiff ℝ 1 potential)
    (hpotential :
      (quittingFloorRobustChargedRelation reward floor tolerance bound).IsPotential
        (fun state ↦ potential state.1)) :
    ∃ expression : RationalPolynomial dimension,
      (quittingFloorRobustChargedRelation reward floor tolerance bound).IsPotential
        (fun state ↦ evalReal state.1 expression) := by
  let domain : Set (Fin dimension → ℝ) :=
    {point | ∀ coordinate, |point coordinate| ≤ bound ∧
      floor coordinate - tolerance ≤ point coordinate}
  have hdomain : domain = Set.Icc
      (fun coordinate ↦ max (-bound) (floor coordinate - tolerance)) (fun _ ↦ bound) := by
    ext point
    simp only [domain, Set.mem_setOf_eq, Set.mem_Icc, Pi.le_def, max_le_iff, abs_le, forall_and]
    tauto
  have hconvex : Convex ℝ domain := by rw [hdomain]; exact convex_Icc _ _
  let displacementBound := max 1 (rewardBound + bound + tolerance)
  have hdisplacementBound : 0 < displacementBound := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hdisplacement (edge : QuittingFloorRobustChargedEdge reward floor tolerance bound) :
      ‖edge.1.1.1.1.1 - edge.1.1.2.1‖ ≤ displacementBound *
        quittingRootAbsorptionMass (quittingRootOfSimplex edge.1.1.1.2) := by
    have habsorption := quittingRootAbsorptionMass_nonneg (quittingRootOfSimplex edge.1.1.1.2)
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hdisplacementBound.le habsorption)).mpr
    intro coordinate
    have hcoordinate := abs_quittingRobustChargedEdge_target_sub_source_le
      reward rewardBound tolerance bound hreward edge.1 coordinate
    have hscale := mul_le_mul_of_nonneg_right
      (le_max_right 1 (rewardBound + bound + tolerance)) habsorption
    simpa only [Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm] using hcoordinate.trans hscale
  let relation := quittingFloorRobustChargedRelation reward floor tolerance bound
  obtain ⟨expression, hexpression⟩ := exists_evalReal_charge_drift_of_contDiff domain
    (isCompact_quittingFloorRobustChargedState floor tolerance bound) hconvex
    (fun edge ↦ (relation.src edge).1) (fun edge ↦ (relation.tgt edge).1) relation.charge
    (fun edge ↦ (relation.src edge).2) (fun edge ↦ (relation.tgt edge).2)
    displacementBound hdisplacementBound hdisplacement potential hsmooth
    (fun edge ↦ by have hedge := hpotential edge; linarith)
  refine ⟨expression, ?_⟩
  intro edge
  have hedge := hexpression edge
  change evalReal (relation.tgt edge).1 expression + relation.charge edge ≤
    evalReal (relation.src edge).1 expression
  linarith

/-- Finite capacity of the complete outer floor-bearing relation constructs one rational
polynomial with full-unit drift on all inner edges. No normality or rational floor is assumed. -/
theorem exists_quittingFloorRobustChargedRelation_rationalPotential_of_finiteBudget
    (reward : {coalition : Finset (Fin dimension) // coalition.Nonempty} → Payoff (Fin dimension))
    (floor : Payoff (Fin dimension)) (rewardBound epsilon bound : ℝ)
    (hreward : ∀ terminal who, |reward terminal who| ≤ rewardBound)
    (hepsilon : 0 < epsilon) (hepsilonMax : epsilon ≤ 1)
    (hbudget :
      (quittingFloorRobustChargedRelation reward floor epsilon (bound + 1)).HasFiniteBudget) :
    ∃ expression : RationalPolynomial dimension,
      (quittingFloorRobustChargedRelation reward floor (epsilon / 4) bound).IsPotential
        (fun state ↦ evalReal state.1 expression) := by
  apply exists_quittingFloorRobustChargedRelation_rationalPotential_of_contDiff
    reward floor rewardBound (epsilon / 4) bound hreward
    (quittingFloorRobustSmoothedCapacity reward floor epsilon bound hepsilon)
    ((contDiff_quittingFloorRobustSmoothedCapacity hepsilon hbudget).of_le (by norm_num))
  intro edge
  have hedge := quittingFloorRobustChargedEdge_charge_add_smoothedCapacity_target_le_source
    hepsilon hepsilonMax hbudget edge
  change quittingFloorRobustSmoothedCapacity reward floor epsilon bound hepsilon
      edge.1.1.2.1 +
    (quittingFloorRobustChargedRelation reward floor (epsilon / 4) bound).charge edge ≤
      quittingFloorRobustSmoothedCapacity reward floor epsilon bound hepsilon edge.1.1.1.1.1
  linarith

end GameTheory

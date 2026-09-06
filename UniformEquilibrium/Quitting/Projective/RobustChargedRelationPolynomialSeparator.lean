import UniformEquilibrium.Quitting.Projective.RobustChargedRelationSmoothing
import UniformEquilibrium.Quitting.Projective.RobustChargedRelationPolynomialPotential

/-! # Rational polynomial separators from finite full-box robust capacity -/

noncomputable section

namespace GameTheory

open Math.Interval Math.Interval.RationalPolynomial

/-- Finite capacity of the entire outer robust relation constructs one rational polynomial
with full absorption drift on every edge of the inner relation. -/
theorem exists_quittingRobustChargedRelation_rationalPotential_of_finiteBudget
    {dimension : ℕ}
    (reward : {coalition : Finset (Fin dimension) // coalition.Nonempty} → Payoff (Fin dimension))
    (rewardBound epsilon bound : ℝ)
    (hreward : ∀ terminal who, |reward terminal who| ≤ rewardBound)
    (hepsilon : 0 < epsilon) (hepsilonMax : epsilon ≤ 1)
    (hbudget :
      (quittingFloorFreeRobustChargedRelation reward epsilon (bound + 1)).HasFiniteBudget) :
    ∃ expression : RationalPolynomial dimension,
      (quittingFloorFreeRobustChargedRelation reward (epsilon / 4) bound).IsPotential
        (fun state ↦ evalReal state.1 expression) := by
  apply exists_quittingRobustChargedRelation_rationalPotential_of_contDiff reward rewardBound
    (epsilon / 4) bound hreward (quittingRobustSmoothedCapacity reward epsilon bound hepsilon)
    ((contDiff_quittingRobustSmoothedCapacity hepsilon hbudget).of_le (by norm_num))
  intro edge
  have hedge := quittingRobustChargedEdge_charge_add_smoothedCapacity_target_le_source
    hepsilon hepsilonMax hbudget edge
  change quittingRobustSmoothedCapacity reward epsilon bound hepsilon edge.1.2.1 +
    (quittingFloorFreeRobustChargedRelation reward (epsilon / 4) bound).charge edge ≤
      quittingRobustSmoothedCapacity reward epsilon bound hepsilon edge.1.1.1.1
  linarith

end GameTheory

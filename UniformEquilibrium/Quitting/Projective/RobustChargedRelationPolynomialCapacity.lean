import MathUE.Interval.PolynomialLipschitz
import UniformEquilibrium.Quitting.Projective.RobustChargedRelation

/-! # All-start finite charge bounds from rational polynomial robust-edge potentials -/

noncomputable section

namespace GameTheory

open Math.Interval Math.Interval.RationalPolynomial Math.ChargedPathBudget

variable {dimension : ℕ}
variable {reward : {coalition : Finset (Fin dimension) // coalition.Nonempty} →
  Payoff (Fin dimension)}
variable {tolerance bound : ℝ}

/-- A native rational ALL-edge potential is bounded on the full compact state box. -/
theorem quittingRobustChargedRelation_isBoundedPotential_of_rationalPotential
    (expression : RationalPolynomial dimension)
    (hpotential : (quittingFloorFreeRobustChargedRelation reward tolerance bound).IsPotential
      (fun state ↦ evalReal state.1 expression)) :
    (quittingFloorFreeRobustChargedRelation reward tolerance bound).IsBoundedPotential
      (fun state ↦ evalReal state.1 expression) := by
  have hcontinuous : Continuous (fun point : Fin dimension → ℝ ↦ evalReal point expression) :=
    continuous_iff_continuousAt.mpr fun point ↦
      (hasFDerivAt_evalReal expression point).continuousAt
  have hcompact : IsCompact (Set.range (fun state : QuittingRobustChargedState
      (Fin dimension) bound ↦ evalReal state.1 expression)) :=
    isCompact_range (hcontinuous.comp continuous_subtype_val)
  exact ⟨hcompact.bddAbove, hcompact.bddBelow, hpotential⟩

/-- Every finite path, including the nil path at every source, is bounded by the same finite
box oscillation. No selected component, prescribed start, or positive charge is required. -/
theorem quittingRobustPath_chargeSum_le_rationalPotential_oscillation
    (expression : RationalPolynomial dimension)
    (hpotential : (quittingFloorFreeRobustChargedRelation reward tolerance bound).IsPotential
      (fun state ↦ evalReal state.1 expression))
    {source target : QuittingRobustChargedState (Fin dimension) bound}
    (path : (quittingFloorFreeRobustChargedRelation reward tolerance bound).Path source target) :
    path.chargeSum ≤ Math.ChargedPathBudget.oscillation
      (fun state : QuittingRobustChargedState (Fin dimension) bound ↦
        evalReal state.1 expression) :=
  (quittingRobustChargedRelation_isBoundedPotential_of_rationalPotential expression
    hpotential).chargeSum_le_oscillation path

/-- One rational polynomial ALL-edge potential bounds the complete free-start robust capacity. -/
theorem quittingRobustChargedRelation_hasFiniteBudget_of_rationalPotential
    (expression : RationalPolynomial dimension)
    (hpotential : (quittingFloorFreeRobustChargedRelation reward tolerance bound).IsPotential
      (fun state ↦ evalReal state.1 expression)) :
    (quittingFloorFreeRobustChargedRelation reward tolerance bound).HasFiniteBudget :=
  (quittingRobustChargedRelation_isBoundedPotential_of_rationalPotential expression
    hpotential).hasFiniteBudget

end GameTheory

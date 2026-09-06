import MathUE.CompactChargedPathCapacity
import UniformEquilibrium.Quitting.Projective.RobustChargedRelation

/-! # Compact-capacity interface for the floor-free robust relation -/

noncomputable section

namespace GameTheory

open Math.ChargedPathBudget

variable {player : Type} [Fintype player] [DecidableEq player]

/-- Finite-horizon robust charge is attained by one literal relation path. -/
theorem exists_quittingRobustPath_eq_compactFiniteHorizonMaxCharge
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (tolerance bound : ℝ) (state : QuittingRobustChargedState player bound)
    (horizon : ℕ) :
    ∃ target, ∃ path :
        (quittingFloorFreeRobustChargedRelation reward tolerance bound).Path
          state target,
      path.length ≤ horizon ∧
        path.chargeSum =
          ChargedRelation.compactFiniteHorizonMaxCharge
            (quittingFloorFreeRobustChargedRelation reward tolerance bound)
            state horizon := by
  let relation := quittingFloorFreeRobustChargedRelation
    reward tolerance bound
  exact relation.exists_path_eq_compactFiniteHorizonMaxCharge
      (continuous_quittingFloorFreeRobustChargedRelation_src
        reward tolerance bound)
      (continuous_quittingFloorFreeRobustChargedRelation_tgt
        reward tolerance bound)
      (continuous_quittingFloorFreeRobustChargedRelation_charge
        reward tolerance bound) state horizon

/-- Finite-horizon robust capacity is upper semicontinuous on the whole
boxed state space, including states with no outgoing edge. -/
theorem upperSemicontinuous_quittingRobustCompactFiniteHorizonMaxCharge
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (tolerance bound : ℝ) (horizon : ℕ) :
    UpperSemicontinuous (fun state : QuittingRobustChargedState player bound ↦
      ChargedRelation.compactFiniteHorizonMaxCharge
        (quittingFloorFreeRobustChargedRelation reward tolerance bound)
        state horizon) := by
  let relation := quittingFloorFreeRobustChargedRelation
    reward tolerance bound
  exact relation.upperSemicontinuous_compactFiniteHorizonMaxCharge
      (continuous_quittingFloorFreeRobustChargedRelation_src
        reward tolerance bound)
      (continuous_quittingFloorFreeRobustChargedRelation_tgt
        reward tolerance bound)
      (continuous_quittingFloorFreeRobustChargedRelation_charge
        reward tolerance bound) horizon

/-- Under finite total robust capacity, the existing all-horizon capacity
function is Borel measurable. No semicontinuity of that supremum is claimed. -/
theorem measurable_quittingRobustChargedRelation_value
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (tolerance bound : ℝ)
    (hbudget : (quittingFloorFreeRobustChargedRelation
      reward tolerance bound).HasFiniteBudget) :
    Measurable (quittingFloorFreeRobustChargedRelation
      reward tolerance bound).value := by
  let relation := quittingFloorFreeRobustChargedRelation
    reward tolerance bound
  exact relation.measurable_value_of_compact_edges
      (continuous_quittingFloorFreeRobustChargedRelation_src
        reward tolerance bound)
      (continuous_quittingFloorFreeRobustChargedRelation_tgt
        reward tolerance bound)
      (continuous_quittingFloorFreeRobustChargedRelation_charge
        reward tolerance bound) hbudget

end GameTheory

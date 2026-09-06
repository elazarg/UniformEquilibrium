import MathUE.Analysis.OneSidedCapacitySmoothing
import MathUE.Analysis.CompactSubtypeZeroExtension
import UniformEquilibrium.Quitting.Projective.FloorRobustChargedRelationTranslation

/-! # One-sided smoothing of finite robust capacity with endpoint floors -/

noncomputable section

namespace GameTheory

open Math.OneSidedCapacitySmoothing MeasureTheory
open scoped ContDiff

variable {player : Type} [Fintype player] [DecidableEq player]
variable {reward : {coalition : Finset player // coalition.Nonempty} → Payoff player}
variable {floor : Payoff player} {tolerance bound : ℝ}

/-- Zero extension of the actual all-horizon capacity from the entire floor-bearing domain. -/
def quittingFloorRobustCapacityZeroExtension
    (reward : {coalition : Finset player // coalition.Nonempty} → Payoff player)
    (floor : Payoff player) (tolerance bound : ℝ) : Payoff player → ℝ :=
  Function.extend Subtype.val
    (quittingFloorRobustChargedRelation reward floor tolerance bound).value 0

theorem integrable_quittingFloorRobustCapacityZeroExtension
    (hbudget : (quittingFloorRobustChargedRelation reward floor tolerance bound).HasFiniteBudget) :
    Integrable (quittingFloorRobustCapacityZeroExtension reward floor tolerance bound) := by
  let relation := quittingFloorRobustChargedRelation reward floor tolerance bound
  apply Math.integrable_extend_subtype_zero_of_isCompact _
    (isCompact_quittingFloorRobustChargedState floor tolerance bound) relation.value
    (measurable_quittingFloorRobustChargedRelation_value reward floor tolerance bound hbudget)
    relation.budget
  intro state
  rw [Real.norm_eq_abs, abs_of_nonneg (relation.value_nonneg hbudget state)]
  exact relation.value_le_budget hbudget state

/-- One globally smooth potential is obtained from the outer floor-bearing capacity. -/
def quittingFloorRobustSmoothedCapacity
    (reward : {coalition : Finset player // coalition.Nonempty} → Payoff player)
    (floor : Payoff player) (epsilon bound : ℝ) (hepsilon : 0 < epsilon) : Payoff player → ℝ :=
  let kernel := canonicalOneSidedSmoothKernel
    (coordinate := player) (epsilon / 4) (by positivity)
  kernel.average (quittingFloorRobustCapacityZeroExtension reward floor epsilon (bound + 1))

theorem contDiff_quittingFloorRobustSmoothedCapacity
    (hepsilon : 0 < tolerance)
    (hbudget :
      (quittingFloorRobustChargedRelation reward floor tolerance (bound + 1)).HasFiniteBudget) :
    ContDiff ℝ ∞ (quittingFloorRobustSmoothedCapacity reward floor tolerance bound hepsilon) := by
  let kernel := canonicalOneSidedSmoothKernel
    (coordinate := player) (tolerance / 4) (by positivity)
  exact kernel.contDiff_average _
    (integrable_quittingFloorRobustCapacityZeroExtension hbudget).locallyIntegrable

/-- Every inner floor-bearing edge retains its full actual absorption drift after smoothing. -/
theorem quittingFloorRobustChargedEdge_charge_add_smoothedCapacity_target_le_source
    (hepsilon : 0 < tolerance) (hepsilonMax : tolerance ≤ 1)
    (hbudget :
      (quittingFloorRobustChargedRelation reward floor tolerance (bound + 1)).HasFiniteBudget)
    (edge : QuittingFloorRobustChargedEdge reward floor (tolerance / 4) bound) :
    (quittingFloorRobustChargedRelation reward floor (tolerance / 4) bound).charge edge +
        quittingFloorRobustSmoothedCapacity reward floor tolerance bound hepsilon edge.1.1.2.1 ≤
      quittingFloorRobustSmoothedCapacity reward floor tolerance bound hepsilon edge.1.1.1.1.1 := by
  let kernel := canonicalOneSidedSmoothKernel
    (coordinate := player) (tolerance / 4) (by positivity)
  apply kernel.charge_add_average_le_average _
    (integrable_quittingFloorRobustCapacityZeroExtension hbudget).locallyIntegrable
  intro displacement hdisplacement
  have hshift := kernel.shift_mem displacement hdisplacement
  let outerRelation := quittingFloorRobustChargedRelation reward floor tolerance (bound + 1)
  have hdrift := floorRobust_zeroExtension_translated_drift
    outerRelation.value (outerRelation.value_isBoundedPotential hbudget).isPotential
    edge (-displacement) hepsilon.le hepsilonMax
    (fun who ↦ (hshift who).1.le) (fun who ↦ (hshift who).2.le)
  have htranslate (point : Payoff player) :
      quittingPayoffVectorTranslate point (-displacement) = point - displacement := by
    ext who
    simp only [quittingPayoffVectorTranslate, Pi.neg_apply, Pi.sub_apply, sub_eq_add_neg]
  rw [htranslate, htranslate] at hdrift
  exact hdrift

end GameTheory

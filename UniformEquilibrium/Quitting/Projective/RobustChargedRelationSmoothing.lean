import MathUE.Analysis.OneSidedCapacitySmoothing
import MathUE.Analysis.CompactSubtypeZeroExtension
import UniformEquilibrium.Quitting.Projective.RobustChargedRelationCapacity
import UniformEquilibrium.Quitting.Projective.RobustChargedRelationTranslation

/-! # One-sided smoothing of full-box robust charged capacity -/

noncomputable section

open Filter Function MeasureTheory Set
open scoped ContDiff Convolution Topology

namespace GameTheory

open Math.ChargedPathBudget Math.OneSidedCapacitySmoothing Math.Probability

variable {player : Type} [Fintype player] [DecidableEq player]
variable {reward : {S : Finset player // S.Nonempty} → Payoff player}
variable {tolerance bound : ℝ}

/-- Extend the Borel robust capacity by zero from its closed coordinate box to
the ambient payoff space. -/
def quittingRobustCapacityZeroExtension
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (tolerance bound : ℝ) : Payoff player → ℝ :=
  Function.extend Subtype.val
    (quittingFloorFreeRobustChargedRelation reward tolerance bound).value 0

@[simp] theorem quittingRobustCapacityZeroExtension_apply_state
    (state : QuittingRobustChargedState player bound) :
    quittingRobustCapacityZeroExtension reward tolerance bound state.1 =
      (quittingFloorFreeRobustChargedRelation
        reward tolerance bound).value state := by
  exact Subtype.val_injective.extend_apply _ _ state

theorem measurable_quittingRobustCapacityZeroExtension
    (hbudget : (quittingFloorFreeRobustChargedRelation
      reward tolerance bound).HasFiniteBudget) :
    Measurable (quittingRobustCapacityZeroExtension reward tolerance bound) := by
  let carrier : Set (Payoff player) :=
    {value | ∀ who, |value who| ≤ bound}
  have hcarrier : MeasurableSet carrier :=
    (isCompact_quittingRobustChargedState
      (player := player) bound).isClosed.measurableSet
  exact (MeasurableEmbedding.subtype_coe hcarrier).measurable_extend
    (measurable_quittingRobustChargedRelation_value
      reward tolerance bound hbudget) measurable_const

theorem quittingRobustCapacityZeroExtension_eq_zero_of_not_mem
    (value : Payoff player) (hvalue : ¬ ∀ who, |value who| ≤ bound) :
    quittingRobustCapacityZeroExtension reward tolerance bound value = 0 := by
  apply Function.extend_apply'
  rintro ⟨state, hstate⟩
  apply hvalue
  rw [← hstate]
  exact state.2

theorem quittingRobustCapacityZeroExtension_nonneg
    (hbudget : (quittingFloorFreeRobustChargedRelation
      reward tolerance bound).HasFiniteBudget)
    (value : Payoff player) :
    0 ≤ quittingRobustCapacityZeroExtension reward tolerance bound value := by
  by_cases hvalue : ∀ who, |value who| ≤ bound
  · let state : QuittingRobustChargedState player bound := ⟨value, hvalue⟩
    rw [show value = state.1 from rfl,
      quittingRobustCapacityZeroExtension_apply_state]
    exact (quittingFloorFreeRobustChargedRelation
      reward tolerance bound).value_nonneg hbudget state
  · rw [quittingRobustCapacityZeroExtension_eq_zero_of_not_mem
      value hvalue]

theorem quittingRobustCapacityZeroExtension_le_budget
    (hbudget : (quittingFloorFreeRobustChargedRelation
      reward tolerance bound).HasFiniteBudget)
    (value : Payoff player) :
    quittingRobustCapacityZeroExtension reward tolerance bound value ≤
      (quittingFloorFreeRobustChargedRelation reward tolerance bound).budget := by
  by_cases hvalue : ∀ who, |value who| ≤ bound
  · let state : QuittingRobustChargedState player bound := ⟨value, hvalue⟩
    rw [show value = state.1 from rfl,
      quittingRobustCapacityZeroExtension_apply_state]
    exact (quittingFloorFreeRobustChargedRelation
      reward tolerance bound).value_le_budget hbudget state
  · rw [quittingRobustCapacityZeroExtension_eq_zero_of_not_mem
      value hvalue]
    exact (quittingFloorFreeRobustChargedRelation
      reward tolerance bound).budget_nonneg

theorem hasCompactSupport_quittingRobustCapacityZeroExtension :
    HasCompactSupport
      (quittingRobustCapacityZeroExtension reward tolerance bound) := by
  apply HasCompactSupport.intro
    (isCompact_quittingRobustChargedState (player := player) bound)
  intro value hvalue
  exact quittingRobustCapacityZeroExtension_eq_zero_of_not_mem value hvalue

theorem integrable_quittingRobustCapacityZeroExtension
    (hbudget : (quittingFloorFreeRobustChargedRelation
      reward tolerance bound).HasFiniteBudget) :
    Integrable (quittingRobustCapacityZeroExtension
      reward tolerance bound) := by
  apply Math.integrable_extend_subtype_zero_of_isCompact
    {value : Payoff player | ∀ who, |value who| ≤ bound}
    (isCompact_quittingRobustChargedState bound)
    (quittingFloorFreeRobustChargedRelation reward tolerance bound).value
    (measurable_quittingRobustChargedRelation_value reward tolerance bound hbudget)
    (quittingFloorFreeRobustChargedRelation reward tolerance bound).budget
  intro state
  rw [Real.norm_eq_abs, abs_of_nonneg
    ((quittingFloorFreeRobustChargedRelation reward tolerance bound).value_nonneg
      hbudget state)]
  exact (quittingFloorFreeRobustChargedRelation reward tolerance bound).value_le_budget
    hbudget state

theorem locallyIntegrable_quittingRobustCapacityZeroExtension
    (hbudget : (quittingFloorFreeRobustChargedRelation
      reward tolerance bound).HasFiniteBudget) :
    LocallyIntegrable (quittingRobustCapacityZeroExtension
      reward tolerance bound) :=
  (integrable_quittingRobustCapacityZeroExtension hbudget).locallyIntegrable

/-- The one-sided smoothing of the zero-extended outer robust capacity. -/
def quittingRobustSmoothedCapacity
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (epsilon bound : ℝ) (hepsilon : 0 < epsilon) : Payoff player → ℝ :=
  let kernel := canonicalOneSidedSmoothKernel
    (coordinate := player) (epsilon / 4) (by positivity)
  kernel.average
    (quittingRobustCapacityZeroExtension reward epsilon (bound + 1))

theorem contDiff_quittingRobustSmoothedCapacity
    (hepsilon : 0 < tolerance)
    (hbudget : (quittingFloorFreeRobustChargedRelation
      reward tolerance (bound + 1)).HasFiniteBudget) :
    ContDiff ℝ ∞ (quittingRobustSmoothedCapacity
      reward tolerance bound hepsilon) := by
  let kernel := canonicalOneSidedSmoothKernel
    (coordinate := player) (tolerance / 4) (by positivity)
  exact kernel.contDiff_average _
    (locallyIntegrable_quittingRobustCapacityZeroExtension hbudget)

/-- The single smoothed capacity drops by at least the exact absorption charge
on every edge of the inner robust relation. -/
theorem quittingRobustChargedEdge_charge_add_smoothedCapacity_target_le_source
    (hepsilon : 0 < tolerance) (hepsilonMax : tolerance ≤ 1)
    (hbudget : (quittingFloorFreeRobustChargedRelation
      reward tolerance (bound + 1)).HasFiniteBudget)
    (edge : QuittingRobustChargedEdge reward (tolerance / 4) bound) :
    (quittingFloorFreeRobustChargedRelation reward
        (tolerance / 4) bound).charge edge +
      quittingRobustSmoothedCapacity reward tolerance bound hepsilon edge.1.2.1 ≤
        quittingRobustSmoothedCapacity reward tolerance bound
          hepsilon edge.1.1.1.1 := by
  let kernel := canonicalOneSidedSmoothKernel
    (coordinate := player) (tolerance / 4) (by positivity)
  apply kernel.charge_add_average_le_average _
    (locallyIntegrable_quittingRobustCapacityZeroExtension hbudget)
  intro displacement hdisplacement
  have hshift := kernel.shift_mem displacement hdisplacement
  let shift : Payoff player := fun who ↦ -displacement who
  have hshiftNonneg : ∀ who, 0 ≤ shift who := fun who ↦ (hshift who).1.le
  have hshiftUpper : ∀ who, shift who ≤ tolerance / 4 :=
    fun who ↦ (hshift who).2.le
  let outerEdge := QuittingRobustChargedEdge.vectorTranslate edge shift
    hepsilon.le hepsilonMax hshiftNonneg hshiftUpper
  let outerRelation := quittingFloorFreeRobustChargedRelation
    reward tolerance (bound + 1)
  have hpotential := outerRelation.value_tgt_add_charge_le_value_src
    hbudget outerEdge
  have hsourceAmbient : edge.1.1.1.1 - displacement = outerEdge.1.1.1.1 := by
    rw [QuittingRobustChargedEdge.vectorTranslate_source]
    funext who
    simp only [shift, quittingPayoffVectorTranslate, Pi.sub_apply,
      sub_eq_add_neg]
  have htargetAmbient : edge.1.2.1 - displacement = outerEdge.1.2.1 := by
    rw [QuittingRobustChargedEdge.vectorTranslate_target]
    funext who
    simp only [shift, quittingPayoffVectorTranslate, Pi.sub_apply,
      sub_eq_add_neg]
  rw [hsourceAmbient, htargetAmbient,
    quittingRobustCapacityZeroExtension_apply_state,
    quittingRobustCapacityZeroExtension_apply_state]
  have hcharge := QuittingRobustChargedEdge.vectorTranslate_charge edge shift
    hepsilon.le hepsilonMax hshiftNonneg hshiftUpper
  change outerRelation.charge outerEdge =
    (quittingFloorFreeRobustChargedRelation reward
      (tolerance / 4) bound).charge edge at hcharge
  dsimp only [outerRelation, quittingFloorFreeRobustChargedRelation] at hpotential hcharge ⊢
  linarith

end GameTheory

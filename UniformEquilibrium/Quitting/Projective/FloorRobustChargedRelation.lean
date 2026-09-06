import UniformEquilibrium.Quitting.Projective.RobustChargedRelation
import MathUE.CompactChargedPathCapacity

/-! # Robust charged relations with arbitrary coordinate endpoint floors -/

noncomputable section

namespace GameTheory

open Set Math.ChargedPathBudget

variable {player : Type} [Fintype player] [DecidableEq player]

/-- The robust box with the tolerance-dependent floor imposed at every state. -/
abbrev QuittingFloorRobustChargedState (floor : Payoff player) (tolerance bound : ℝ) :=
  {value : Payoff player // ∀ who, |value who| ≤ bound ∧ floor who - tolerance ≤ value who}

/-- Forgetting the floor leaves exactly the same boxed payoff vector. -/
def QuittingFloorRobustChargedState.forgetFloor {floor : Payoff player} {tolerance bound : ℝ}
    (state : QuittingFloorRobustChargedState floor tolerance bound) :
    QuittingRobustChargedState player bound :=
  ⟨state.1, fun who ↦ (state.2 who).1⟩

omit [Fintype player] [DecidableEq player] in
theorem isCompact_quittingFloorRobustChargedState
    (floor : Payoff player) (tolerance bound : ℝ) :
    IsCompact {value : Payoff player |
      ∀ who, |value who| ≤ bound ∧ floor who - tolerance ≤ value who} := by
  have hdomain : {value : Payoff player |
      ∀ who, |value who| ≤ bound ∧ floor who - tolerance ≤ value who} =
      Icc (fun who ↦ max (-bound) (floor who - tolerance)) (fun _ ↦ bound) := by
    ext value
    simp only [mem_setOf_eq, mem_Icc, Pi.le_def, max_le_iff, abs_le, forall_and]
    tauto
  rw [hdomain]
  exact isCompact_Icc

instance (floor : Payoff player) (tolerance bound : ℝ) :
    CompactSpace (QuittingFloorRobustChargedState floor tolerance bound) :=
  isCompact_iff_compactSpace.mp
    (isCompact_quittingFloorRobustChargedState floor tolerance bound)

/-- All robust edges whose two endpoints meet the specified approximate floor. -/
abbrev QuittingFloorRobustChargedEdge
    (reward : {coalition : Finset player // coalition.Nonempty} → Payoff player)
    (floor : Payoff player) (tolerance bound : ℝ) :=
  {edge : QuittingRobustChargedEdge reward tolerance bound //
    ∀ who, floor who - tolerance ≤ edge.1.1.1.1 who ∧
      floor who - tolerance ≤ edge.1.2.1 who}

/-- The full floor-bearing relation; no source is anchored or restricted by reachability. -/
def quittingFloorRobustChargedRelation
    (reward : {coalition : Finset player // coalition.Nonempty} → Payoff player)
    (floor : Payoff player) (tolerance bound : ℝ) :
    ChargedRelation (QuittingFloorRobustChargedState floor tolerance bound)
      (QuittingFloorRobustChargedEdge reward floor tolerance bound) where
  src edge := ⟨edge.1.1.1.1.1, fun who ↦ ⟨edge.1.1.1.1.2 who, (edge.2 who).1⟩⟩
  tgt edge := ⟨edge.1.1.2.1, fun who ↦ ⟨edge.1.1.2.2 who, (edge.2 who).2⟩⟩
  charge edge := quittingRootAbsorptionMass (quittingRootOfSimplex edge.1.1.1.2)
  charge_nonneg _ := quittingRootAbsorptionMass_nonneg _

theorem isClosed_quittingFloorRobustChargedEdge
    (reward : {coalition : Finset player // coalition.Nonempty} → Payoff player)
    (floor : Payoff player) (tolerance bound : ℝ) :
    IsClosed {edge : QuittingRobustChargedEdge reward tolerance bound |
      ∀ who, floor who - tolerance ≤ edge.1.1.1.1 who ∧
        floor who - tolerance ≤ edge.1.2.1 who} := by
  simp only [setOf_forall]
  apply isClosed_iInter
  intro who
  apply IsClosed.inter
  · exact isClosed_le continuous_const
      ((continuous_apply who).comp (continuous_subtype_val.comp
        (continuous_quittingFloorFreeRobustChargedRelation_src reward tolerance bound)))
  · exact isClosed_le continuous_const
      ((continuous_apply who).comp (continuous_subtype_val.comp
        (continuous_quittingFloorFreeRobustChargedRelation_tgt reward tolerance bound)))

instance (reward : {coalition : Finset player // coalition.Nonempty} → Payoff player)
    (floor : Payoff player) (tolerance bound : ℝ) :
    CompactSpace (QuittingFloorRobustChargedEdge reward floor tolerance bound) :=
  isCompact_iff_compactSpace.mp
    (isClosed_quittingFloorRobustChargedEdge reward floor tolerance bound).isCompact

theorem continuous_quittingFloorRobustChargedRelation_src
    (reward : {coalition : Finset player // coalition.Nonempty} → Payoff player)
    (floor : Payoff player) (tolerance bound : ℝ) :
    Continuous (quittingFloorRobustChargedRelation reward floor tolerance bound).src := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.comp
    ((continuous_quittingFloorFreeRobustChargedRelation_src reward tolerance bound).comp
      continuous_subtype_val)

theorem continuous_quittingFloorRobustChargedRelation_tgt
    (reward : {coalition : Finset player // coalition.Nonempty} → Payoff player)
    (floor : Payoff player) (tolerance bound : ℝ) :
    Continuous (quittingFloorRobustChargedRelation reward floor tolerance bound).tgt := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.comp
    ((continuous_quittingFloorFreeRobustChargedRelation_tgt reward tolerance bound).comp
      continuous_subtype_val)

theorem continuous_quittingFloorRobustChargedRelation_charge
    (reward : {coalition : Finset player // coalition.Nonempty} → Payoff player)
    (floor : Payoff player) (tolerance bound : ℝ) :
    Continuous (quittingFloorRobustChargedRelation reward floor tolerance bound).charge :=
  (continuous_quittingFloorFreeRobustChargedRelation_charge reward tolerance bound).comp
    continuous_subtype_val

/-- The all-horizon capacity on the floor-bearing domain is Borel under finite capacity. -/
theorem measurable_quittingFloorRobustChargedRelation_value
    (reward : {coalition : Finset player // coalition.Nonempty} → Payoff player)
    (floor : Payoff player) (tolerance bound : ℝ)
    (hbudget : (quittingFloorRobustChargedRelation reward floor tolerance bound).HasFiniteBudget) :
    Measurable (quittingFloorRobustChargedRelation reward floor tolerance bound).value := by
  let relation := quittingFloorRobustChargedRelation reward floor tolerance bound
  exact relation.measurable_value_of_compact_edges
    (continuous_quittingFloorRobustChargedRelation_src reward floor tolerance bound)
    (continuous_quittingFloorRobustChargedRelation_tgt reward floor tolerance bound)
    (continuous_quittingFloorRobustChargedRelation_charge reward floor tolerance bound) hbudget

end GameTheory

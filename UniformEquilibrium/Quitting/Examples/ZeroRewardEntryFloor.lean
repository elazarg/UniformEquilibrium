import UniformEquilibrium.Quitting.Projective.RobustChargedRelation
import UniformEquilibrium.Quitting.Paths.SureExitSet
import UniformEquilibrium.Quitting.Punishment.ContinueFloor

/-! # Arbitrarily charged exact paths with a below-floor entry -/

noncomputable section

namespace GameTheory

open Math.ChargedPathBudget Math.Probability QuittingSureSetOwnerRepair

namespace ZeroRewardEntryFloor

def reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun _ _ ↦ 0

def quitters : Finset (Fin 4) := {0, 1}

def root : Fin 4 → PMF Bool := quittingPureSetRoot quitters

def negativeValue (bound : ℝ) : Payoff (Fin 4) := fun _ ↦ -bound

def zeroValue : Payoff (Fin 4) := fun _ ↦ 0

theorem quitters_nonempty : quitters.Nonempty := by
  exact ⟨0, by simp [quitters]⟩

theorem quitters_erase_nonempty (who : Fin 4) :
    (quitters.erase who).Nonempty := by
  fin_cases who
  · exact ⟨1, by simp [quitters]⟩
  · exact ⟨0, by simp [quitters]⟩
  · exact ⟨0, by simp [quitters]⟩
  · exact ⟨0, by simp [quitters]⟩

@[simp] theorem successor_eq_zero (value : Payoff (Fin 4)) :
    quittingRootSuccessorPayoff reward value root = zeroValue := by
  funext who
  simp only [root]
  rw [quittingRootSuccessorPayoff,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootAbsorbingContribution_pureSetRoot,
    stationaryContinueMass_pureSetRoot_of_nonempty quitters_nonempty]
  simp [reward, zeroValue, quittingSetReward]

@[simp] theorem coordinateNashDefect_eq_zero
    (value : Payoff (Fin 4)) (who : Fin 4) :
    quittingRootCoordinateNashDefect reward value root who = 0 := by
  simp only [root]
  rw [quittingRootCoordinateNashDefect,
    quittingRootQuitPayoff_pureSetRoot_eq_insert,
    quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty
      value quitters who (quitters_erase_nonempty who)]
  have hsuccessor := congrFun (successor_eq_zero value) who
  simp only [root, zeroValue] at hsuccessor
  rw [hsuccessor]
  simp [reward, quittingSetReward]

@[simp] theorem absorptionMass_eq_one :
    quittingRootAbsorptionMass root = 1 :=
  quittingRootAbsorptionMass_pureSetRoot_of_nonempty quitters_nonempty

theorem punishmentValue_eq_zero (who : Fin 4) :
    quittingPunishmentValue reward who = 0 := by
  apply le_antisymm
  · refine (quittingPunishmentValue_le_max_solo reward who).trans ?_
    simp [reward, quittingSetReward]
  · refine (show 0 ≤ quittingContinueFloor reward who from ?_).trans
      (quittingContinueFloor_le_quittingPunishmentValue reward who)
    unfold quittingContinueFloor quittingBlockContinueFloor
    apply Math.Finset.le_insertMin le_rfl
    intro terminal _
    simp [reward]

/-- The literal exact row from the arbitrary negative entry annotation to
zero, with two sure quitters. -/
def entryEdge (bound tolerance : ℝ) (hbound : 0 ≤ bound)
    (htolerance : 0 ≤ tolerance) :
    QuittingRobustChargedEdge reward tolerance bound := by
  let source : QuittingRobustChargedState (Fin 4) bound :=
    ⟨negativeValue bound, fun who ↦ by
      simp only [negativeValue, abs_neg, abs_of_nonneg hbound]
      exact le_rfl⟩
  let target : QuittingRobustChargedState (Fin 4) bound :=
    ⟨zeroValue, fun who ↦ by
      simp only [zeroValue, abs_zero]
      exact hbound⟩
  let data : QuittingRobustChargedEdgeData (Fin 4) bound :=
    ((source, quittingSimplexOfRoot root), target)
  refine ⟨data, ?_⟩
  intro who
  dsimp only [data, source, target, IsQuittingFloorFreeRobustEdge,
    quittingRobustChargedEdgeResidual, quittingRobustChargedEdgeAbsorption,
    quittingRobustChargedEdgeRegret]
  rw [quittingRootOfSimplex_simplexOfRoot]
  rw [coordinateNashDefect_eq_zero, absorptionMass_eq_one]
  have hsuccessor := congrFun (successor_eq_zero (negativeValue bound)) who
  simp only [zeroValue] at hsuccessor
  rw [hsuccessor]
  simp only [zeroValue, sub_zero, abs_zero]
  constructor <;> simpa using htolerance

@[simp] theorem entryEdge_root
    (bound tolerance : ℝ) (hbound : 0 ≤ bound)
    (htolerance : 0 ≤ tolerance) :
    (entryEdge bound tolerance hbound htolerance).1.1.2 =
      quittingSimplexOfRoot root := rfl

@[simp] theorem entryEdge_source
    (bound tolerance : ℝ) (hbound : 0 ≤ bound)
    (htolerance : 0 ≤ tolerance) :
    (entryEdge bound tolerance hbound htolerance).1.1.1.1 =
      negativeValue bound := rfl

@[simp] theorem entryEdge_charge
    (bound tolerance : ℝ) (hbound : 0 ≤ bound)
    (htolerance : 0 ≤ tolerance) :
    (quittingFloorFreeRobustChargedRelation reward tolerance bound).charge
      (entryEdge bound tolerance hbound htolerance) = 1 := by
  change quittingRootAbsorptionMass
    (quittingRootOfSimplex
      (entryEdge bound tolerance hbound htolerance).1.1.2) = 1
  rw [entryEdge_root, quittingRootOfSimplex_simplexOfRoot]
  exact absorptionMass_eq_one

theorem entryEdge_source_violates_punishmentFloor
    (bound tolerance : ℝ) (hbound : 0 ≤ bound)
    (htolerance : 0 ≤ tolerance) (hstrict : tolerance < bound)
    (who : Fin 4) :
    (entryEdge bound tolerance hbound htolerance).1.1.1.1 who <
      quittingPunishmentValue reward who - tolerance := by
  rw [punishmentValue_eq_zero]
  rw [entryEdge_source]
  simp only [negativeValue]
  linarith

/-- Once the entry row reaches zero, the same two-sure-quitter root is an
exact charge-one self-loop, so arbitrarily many later rows can add charge. -/
def chargedLoopEdge (bound tolerance : ℝ) (hbound : 0 ≤ bound)
    (htolerance : 0 ≤ tolerance) :
    QuittingRobustChargedEdge reward tolerance bound := by
  let state : QuittingRobustChargedState (Fin 4) bound :=
    ⟨zeroValue, fun who ↦ by
      simp only [zeroValue, abs_zero]
      exact hbound⟩
  let data : QuittingRobustChargedEdgeData (Fin 4) bound :=
    ((state, quittingSimplexOfRoot root), state)
  refine ⟨data, ?_⟩
  intro who
  dsimp only [data, state, IsQuittingFloorFreeRobustEdge,
    quittingRobustChargedEdgeResidual, quittingRobustChargedEdgeAbsorption,
    quittingRobustChargedEdgeRegret]
  rw [quittingRootOfSimplex_simplexOfRoot,
    coordinateNashDefect_eq_zero, absorptionMass_eq_one]
  have hsuccessor := congrFun (successor_eq_zero zeroValue) who
  simp only [zeroValue] at hsuccessor
  rw [hsuccessor]
  simp only [zeroValue, sub_zero, abs_zero]
  constructor <;> simpa using htolerance

@[simp] theorem chargedLoopEdge_source_eq_target
    (bound tolerance : ℝ) (hbound : 0 ≤ bound)
    (htolerance : 0 ≤ tolerance) :
    (chargedLoopEdge bound tolerance hbound htolerance).1.1.1 =
      (chargedLoopEdge bound tolerance hbound htolerance).1.2 := rfl

@[simp] theorem chargedLoopEdge_charge
    (bound tolerance : ℝ) (hbound : 0 ≤ bound)
    (htolerance : 0 ≤ tolerance) :
    (quittingFloorFreeRobustChargedRelation reward tolerance bound).charge
      (chargedLoopEdge bound tolerance hbound htolerance) = 1 := by
  change quittingRootAbsorptionMass
    (quittingRootOfSimplex
      (chargedLoopEdge bound tolerance hbound htolerance).1.1.2) = 1
  change quittingRootAbsorptionMass
    (quittingRootOfSimplex (quittingSimplexOfRoot root)) = 1
  rw [quittingRootOfSimplex_simplexOfRoot]
  exact absorptionMass_eq_one

/-- The charge-one self-loop, regarded as a closed charged path. -/
def chargedLoopPath (bound tolerance : ℝ) (hbound : 0 ≤ bound)
    (htolerance : 0 ≤ tolerance) :
    (quittingFloorFreeRobustChargedRelation reward tolerance bound).Path
      ((quittingFloorFreeRobustChargedRelation reward tolerance bound).src
        (chargedLoopEdge bound tolerance hbound htolerance))
      ((quittingFloorFreeRobustChargedRelation reward tolerance bound).src
        (chargedLoopEdge bound tolerance hbound htolerance)) :=
  (ChargedRelation.Path.single
    (R := quittingFloorFreeRobustChargedRelation reward tolerance bound)
    (chargedLoopEdge bound tolerance hbound htolerance)).castTgt
      (chargedLoopEdge_source_eq_target bound tolerance hbound htolerance).symm

/-- The literal family of arbitrarily long charge-accumulating loop paths. -/
def repeatedChargedLoopPath (count : ℕ) (bound tolerance : ℝ)
    (hbound : 0 ≤ bound) (htolerance : 0 ≤ tolerance) :=
  (chargedLoopPath bound tolerance hbound htolerance).iterate count

@[simp] theorem repeatedChargedLoopPath_chargeSum
    (count : ℕ) (bound tolerance : ℝ) (hbound : 0 ≤ bound)
    (htolerance : 0 ≤ tolerance) :
    (repeatedChargedLoopPath count bound tolerance hbound htolerance).chargeSum =
      count := by
  rw [repeatedChargedLoopPath, ChargedRelation.Path.chargeSum_iterate]
  have hloop :
      (chargedLoopPath bound tolerance hbound htolerance).chargeSum = 1 := by
    calc
      _ = (ChargedRelation.Path.single
          (R := quittingFloorFreeRobustChargedRelation reward tolerance bound)
          (chargedLoopEdge bound tolerance hbound htolerance)).chargeSum := by
        apply ChargedRelation.Path.chargeSum_castTgt
      _ = (quittingFloorFreeRobustChargedRelation reward tolerance bound).charge
          (chargedLoopEdge bound tolerance hbound htolerance) :=
        ChargedRelation.Path.chargeSum_single _
      _ = 1 := chargedLoopEdge_charge bound tolerance hbound htolerance
  rw [hloop]
  norm_num

@[simp] theorem repeatedChargedLoopPath_length
    (count : ℕ) (bound tolerance : ℝ) (hbound : 0 ≤ bound)
    (htolerance : 0 ≤ tolerance) :
    (repeatedChargedLoopPath count bound tolerance hbound htolerance).length =
      count := by
  change ((chargedLoopPath bound tolerance hbound htolerance).iterate count).length =
    count
  have hloop :
      (chargedLoopPath bound tolerance hbound htolerance).length = 1 := by
    unfold chargedLoopPath
    rw [ChargedRelation.Path.length_castTgt]
    rfl
  induction count with
  | zero => simp [ChargedRelation.Path.iterate]
  | succ count ih =>
      simp only [ChargedRelation.Path.iterate,
        ChargedRelation.Path.length_append, ih]
      rw [hloop]
      omega

theorem entryEdge_target_eq_chargedLoopEdge_source
    (bound tolerance : ℝ) (hbound : 0 ≤ bound)
    (htolerance : 0 ≤ tolerance) :
    (quittingFloorFreeRobustChargedRelation reward tolerance bound).tgt
        (entryEdge bound tolerance hbound htolerance) =
      (quittingFloorFreeRobustChargedRelation reward tolerance bound).src
        (chargedLoopEdge bound tolerance hbound htolerance) := by
  apply Subtype.ext
  rfl

/-- The literal entry row followed by any requested number of charge-one
loops. This includes the below-floor initial endpoint. -/
def entryThenRepeatedLoopsPath (count : ℕ) (bound tolerance : ℝ)
    (hbound : 0 ≤ bound) (htolerance : 0 ≤ tolerance) :=
  (ChargedRelation.Path.single
    (R := quittingFloorFreeRobustChargedRelation reward tolerance bound)
    (entryEdge bound tolerance hbound htolerance)).append
      ((repeatedChargedLoopPath count bound tolerance hbound htolerance).castSrc
        (entryEdge_target_eq_chargedLoopEdge_source
          bound tolerance hbound htolerance).symm)

@[simp] theorem entryThenRepeatedLoopsPath_chargeSum
    (count : ℕ) (bound tolerance : ℝ) (hbound : 0 ≤ bound)
    (htolerance : 0 ≤ tolerance) :
    (entryThenRepeatedLoopsPath count bound tolerance hbound htolerance).chargeSum =
      count + 1 := by
  rw [entryThenRepeatedLoopsPath, ChargedRelation.Path.chargeSum_append,
    ChargedRelation.Path.chargeSum_single,
    ChargedRelation.Path.chargeSum_castSrc,
    repeatedChargedLoopPath_chargeSum, entryEdge_charge]
  ring

@[simp] theorem entryThenRepeatedLoopsPath_length
    (count : ℕ) (bound tolerance : ℝ) (hbound : 0 ≤ bound)
    (htolerance : 0 ≤ tolerance) :
    (entryThenRepeatedLoopsPath count bound tolerance hbound htolerance).length =
      count + 1 := by
  rw [entryThenRepeatedLoopsPath, ChargedRelation.Path.length_append,
    ChargedRelation.Path.length_castSrc,
    repeatedChargedLoopPath_length]
  have hsingle :
      (ChargedRelation.Path.single
        (R := quittingFloorFreeRobustChargedRelation reward tolerance bound)
        (entryEdge bound tolerance hbound htolerance)).length = 1 := rfl
  rw [hsingle]
  omega

end ZeroRewardEntryFloor

end GameTheory

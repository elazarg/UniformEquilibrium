import UniformEquilibrium.Quitting.Projective.RobustChargedRelation
import UniformEquilibrium.Quitting.Paths.SureExitSet
import UniformEquilibrium.Quitting.Bellman.Finite.BellmanTelescope
import UniformEquilibrium.Quitting.Classification.AbnormalPlayers

/-! # A normal four-player table with an exact positive-charge cycle -/

noncomputable section

namespace GameTheory.ThreeOwnerRobustCycle

open Math.ChargedPathBudget Math.Probability QuittingSureSetOwnerRepair

def reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun terminal who ↦
    if who = 0 then
      if 0 ∈ terminal.1 then 1 + if 2 ∈ terminal.1 then 1 else 0
      else 3 * if 2 ∈ terminal.1 then 1 else 0
    else if who = 1 then
      if 1 ∈ terminal.1 then if 0 ∈ terminal.1 then 1 else 0
      else 3 * (if 0 ∈ terminal.1 then 1 else 0) - 1
    else if who = 2 then
      if 2 ∈ terminal.1 then if 1 ∈ terminal.1 then 1 else 0
      else 3 * (if 1 ∈ terminal.1 then 1 else 0) - 1
    else if 3 ∈ terminal.1 then 0 else 1

def u0 : Payoff (Fin 4) := ![1, 1, 0, 1]
def u1 : Payoff (Fin 4) := ![1, 0, 1, 1]
def u2 : Payoff (Fin 4) := ![2, 0, 0, 1]

theorem reward_abs_le_three
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (who : Fin 4) :
    |reward terminal who| ≤ 3 := by
  fin_cases who <;> simp [reward] <;> split_ifs <;> norm_num

theorem singletonSelfReward (who : Fin 4) :
    reward (quittingSingletonTerminal who) who = ![1, 0, 0, 0] who := by
  fin_cases who <;> simp [reward, quittingSingletonTerminal]

theorem isNormal (who : Fin 4) : IsQuittingNormalPlayer reward who := by
  unfold IsQuittingNormalPlayer
  have hbound := quittingPunishmentValue_le_max_solo reward who
  rw [quittingSetReward_singleton_eq_soloReward] at hbound
  have hnonneg : 0 ≤ quittingSoloReward reward who who := by
    fin_cases who <;>
      simp [quittingSoloReward, reward]
  calc
    quittingPunishmentValue reward who ≤
        max (quittingSoloReward reward who who) 0 := hbound
    _ = quittingSoloReward reward who who := max_eq_left hnonneg
    _ = quittingSoloSelfPayoff reward who := by
      rfl

theorem singletonSelfReward_le_u0 (who : Fin 4) :
    reward (quittingSingletonTerminal who) who ≤ u0 who := by
  rw [singletonSelfReward]
  fin_cases who <;> norm_num [u0]

theorem singletonSelfReward_le_u1 (who : Fin 4) :
    reward (quittingSingletonTerminal who) who ≤ u1 who := by
  rw [singletonSelfReward]
  fin_cases who <;> norm_num [u1]

theorem singletonSelfReward_le_u2 (who : Fin 4) :
    reward (quittingSingletonTerminal who) who ≤ u2 who := by
  rw [singletonSelfReward]
  fin_cases who <;> norm_num [u2]

def halfRoot (owner : Fin 4) : Fin 4 → PMF Bool :=
  quittingSureSetOwnerRoot ∅ owner (1 / 2) (by norm_num) (by norm_num)

@[simp] theorem halfRoot_absorptionMass (owner : Fin 4) :
    quittingRootAbsorptionMass (halfRoot owner) = 1 / 2 := by
  unfold halfRoot
  rw [quittingRootAbsorptionMass,
    stationaryContinueMass_sureSetOwnerRoot_empty]
  norm_num

theorem halfRoot_successor (tail : Payoff (Fin 4)) (owner who : Fin 4) :
    quittingRootSuccessorPayoff reward tail (halfRoot owner) who =
      (1 / 2) * reward (quittingSingletonTerminal owner) who +
        (1 / 2) * tail who := by
  rw [quittingRootSuccessorPayoff,
    quittingRootExpectedPayoff_eq_absorbingContribution_add]
  unfold halfRoot
  rw [quittingRootAbsorbingContribution_sureSetOwnerRoot reward (by simp)]
  rw [stationaryContinueMass_sureSetOwnerRoot_empty]
  simp only [quittingSureSetOwnerValue, quittingSetReward_empty,
    Finset.insert_empty, quittingSetReward_singleton_eq_soloReward]
  unfold quittingSoloReward quittingSingletonTerminal
  ring

theorem halfRoot_quitPayoff (tail : Payoff (Fin 4)) (owner who : Fin 4) :
    quittingRootQuitPayoff reward tail (halfRoot owner) who =
      if who = owner then quittingSetReward reward {owner} owner
      else quittingSureSetOwnerValue reward {who} owner (1 / 2) who := by
  rw [quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
    reward (fun _ ↦ halfRoot owner) who tail 0]
  change quittingStationaryFixedOpponentsQuitValue reward
    (halfRoot owner) who = _
  unfold halfRoot
  by_cases hwho : who = owner
  · subst who
    rw [fixedOpponentsQuitValue_sureSetOwnerRoot_owner]
    simp
  · rw [fixedOpponentsQuitValue_sureSetOwnerRoot_other]
    · simp [hwho]
    · simp
    · exact hwho

theorem halfRoot_continuePayoff (tail : Payoff (Fin 4)) (owner who : Fin 4) :
    quittingRootContinuePayoff reward tail (halfRoot owner) who =
      if who = owner then tail owner
      else (1 / 2) * reward (quittingSingletonTerminal owner) who +
        (1 / 2) * tail who := by
  rw [quittingRootContinuePayoff_eq_fixedOpponents
    reward (fun _ ↦ halfRoot owner) who tail 0]
  change quittingStationaryFixedOpponentsContinueReward reward
      (halfRoot owner) who +
    quittingStationaryFixedOpponentsContinueMass (halfRoot owner) who *
      tail who = _
  unfold halfRoot
  by_cases hwho : who = owner
  · subst who
    simp only [if_pos]
    unfold quittingStationaryFixedOpponentsContinueReward
      quittingFixedOpponentsContinueReward
      quittingStationaryFixedOpponentsContinueMass
      quittingFixedOpponentsContinueMass
    rw [update_sureSetOwnerRoot_owner_false]
    · rw [quittingRootAbsorbingContribution_pureSetRoot]
      have hempty : quittingPureSetRoot (∅ : Finset (Fin 4)) =
          (quittingAllContinueRoot : Fin 4 → PMF Bool) := by
        funext player
        simp [quittingPureSetRoot, quittingAllContinueRoot,
          quittingSetAction]
      rw [hempty, quittingStationaryContinueMass_allContinueRoot]
      simp [quittingSetReward]
    · simp
  · rw [fixedOpponentsContinueReward_sureSetOwnerRoot_other]
    · unfold quittingStationaryFixedOpponentsContinueMass
        quittingFixedOpponentsContinueMass
      rw [update_sureSetOwnerRoot_other_false]
      · simp only [Finset.erase_empty]
        rw [stationaryContinueMass_sureSetOwnerRoot_empty]
        simp only [quittingSureSetOwnerValue_empty]
        rw [quittingSetReward_singleton_eq_soloReward]
        unfold quittingSoloReward quittingSingletonTerminal
        simp only [if_neg hwho]
        ring
      · exact hwho
    · simp
    · exact hwho

@[simp] theorem successor_q0_u1 :
    quittingRootSuccessorPayoff reward u1 (halfRoot 0) = u0 := by
  funext who
  rw [halfRoot_successor]
  fin_cases who <;>
    simp [reward, u0, u1, quittingSingletonTerminal] <;> norm_num

@[simp] theorem successor_q2_u0 :
    quittingRootSuccessorPayoff reward u0 (halfRoot 2) = u2 := by
  funext who
  rw [halfRoot_successor]
  fin_cases who <;>
    simp [reward, u0, u2, quittingSingletonTerminal] <;> norm_num

@[simp] theorem successor_q1_u2 :
    quittingRootSuccessorPayoff reward u2 (halfRoot 1) = u1 := by
  funext who
  rw [halfRoot_successor]
  fin_cases who <;>
    simp [reward, u1, u2, quittingSingletonTerminal] <;> norm_num

theorem continue_sub_quit_q0_u1 (who : Fin 4) :
    quittingRootContinuePayoff reward u1 (halfRoot 0) who -
        quittingRootQuitPayoff reward u1 (halfRoot 0) who =
      ![0, 1 / 2, 0, 1] who := by
  rw [halfRoot_continuePayoff, halfRoot_quitPayoff]
  fin_cases who <;>
    simp [reward, u1, quittingSureSetOwnerValue,
      quittingSetReward, quittingSingletonTerminal] <;> norm_num

theorem continue_sub_quit_q2_u0 (who : Fin 4) :
    quittingRootContinuePayoff reward u0 (halfRoot 2) who -
        quittingRootQuitPayoff reward u0 (halfRoot 2) who =
      ![1 / 2, 0, 0, 1] who := by
  rw [halfRoot_continuePayoff, halfRoot_quitPayoff]
  fin_cases who <;>
    simp [reward, u0, quittingSureSetOwnerValue,
      quittingSetReward, quittingSingletonTerminal] <;> norm_num

theorem continue_sub_quit_q1_u2 (who : Fin 4) :
    quittingRootContinuePayoff reward u2 (halfRoot 1) who -
        quittingRootQuitPayoff reward u2 (halfRoot 1) who =
      ![0, 0, 1 / 2, 1] who := by
  rw [halfRoot_continuePayoff, halfRoot_quitPayoff]
  fin_cases who <;>
    simp [reward, u2, quittingSureSetOwnerValue,
      quittingSetReward, quittingSingletonTerminal] <;> norm_num

@[simp] theorem coordinateNashDefect_q0_u1 (who : Fin 4) :
    quittingRootCoordinateNashDefect reward u1 (halfRoot 0) who = 0 := by
  rw [quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart]
  have hendpoint := continue_sub_quit_q0_u1 who
  unfold quittingRootEndpointDifference
  rw [show quittingRootQuitPayoff reward u1 (halfRoot 0) who -
      quittingRootContinuePayoff reward u1 (halfRoot 0) who =
        -![0, 1 / 2, 0, 1] who by linarith]
  fin_cases who <;> simp [halfRoot, quittingSureSetOwnerRoot]

@[simp] theorem coordinateNashDefect_q2_u0 (who : Fin 4) :
    quittingRootCoordinateNashDefect reward u0 (halfRoot 2) who = 0 := by
  rw [quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart]
  have hendpoint := continue_sub_quit_q2_u0 who
  unfold quittingRootEndpointDifference
  rw [show quittingRootQuitPayoff reward u0 (halfRoot 2) who -
      quittingRootContinuePayoff reward u0 (halfRoot 2) who =
        -![1 / 2, 0, 0, 1] who by linarith]
  fin_cases who <;> simp [halfRoot, quittingSureSetOwnerRoot]

@[simp] theorem coordinateNashDefect_q1_u2 (who : Fin 4) :
    quittingRootCoordinateNashDefect reward u2 (halfRoot 1) who = 0 := by
  rw [quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart]
  have hendpoint := continue_sub_quit_q1_u2 who
  unfold quittingRootEndpointDifference
  rw [show quittingRootQuitPayoff reward u2 (halfRoot 1) who -
      quittingRootContinuePayoff reward u2 (halfRoot 1) who =
        -![0, 0, 1 / 2, 1] who by linarith]
  fin_cases who <;> simp [halfRoot, quittingSureSetOwnerRoot]

def state0 (bound : ℝ) (hbound : 3 ≤ bound) :
    QuittingRobustChargedState (Fin 4) bound :=
  ⟨u0, fun who ↦ by
    fin_cases who <;> simp [u0] <;> linarith⟩

def state1 (bound : ℝ) (hbound : 3 ≤ bound) :
    QuittingRobustChargedState (Fin 4) bound :=
  ⟨u1, fun who ↦ by
    fin_cases who <;> simp [u1] <;> linarith⟩

def state2 (bound : ℝ) (hbound : 3 ≤ bound) :
    QuittingRobustChargedState (Fin 4) bound :=
  ⟨u2, fun who ↦ by
    fin_cases who <;> simp [u2] <;> linarith⟩

def exactHalfEdge (tolerance bound : ℝ) (htolerance : 0 ≤ tolerance)
    (source target : QuittingRobustChargedState (Fin 4) bound)
    (owner : Fin 4)
    (hsuccessor :
      quittingRootSuccessorPayoff reward source.1 (halfRoot owner) = target.1)
    (hdefect : ∀ who,
      quittingRootCoordinateNashDefect reward source.1
        (halfRoot owner) who = 0) :
    QuittingRobustChargedEdge reward tolerance bound := by
  let data : QuittingRobustChargedEdgeData (Fin 4) bound :=
    ((source, quittingSimplexOfRoot (halfRoot owner)), target)
  refine ⟨data, ?_⟩
  intro who
  dsimp only [data, IsQuittingFloorFreeRobustEdge,
    quittingRobustChargedEdgeResidual, quittingRobustChargedEdgeAbsorption,
    quittingRobustChargedEdgeRegret]
  rw [quittingRootOfSimplex_simplexOfRoot, hdefect,
    halfRoot_absorptionMass]
  rw [congrFun hsuccessor who]
  simp only [sub_self, abs_zero]
  constructor <;> nlinarith

def edge0 (tolerance bound : ℝ) (htolerance : 0 ≤ tolerance)
    (hbound : 3 ≤ bound) :
    QuittingRobustChargedEdge reward tolerance bound :=
  exactHalfEdge tolerance bound htolerance (state1 bound hbound)
    (state0 bound hbound) 0 successor_q0_u1 coordinateNashDefect_q0_u1

def edge2 (tolerance bound : ℝ) (htolerance : 0 ≤ tolerance)
    (hbound : 3 ≤ bound) :
    QuittingRobustChargedEdge reward tolerance bound :=
  exactHalfEdge tolerance bound htolerance (state0 bound hbound)
    (state2 bound hbound) 2 successor_q2_u0 coordinateNashDefect_q2_u0

def edge1 (tolerance bound : ℝ) (htolerance : 0 ≤ tolerance)
    (hbound : 3 ≤ bound) :
    QuittingRobustChargedEdge reward tolerance bound :=
  exactHalfEdge tolerance bound htolerance (state2 bound hbound)
    (state1 bound hbound) 1 successor_q1_u2 coordinateNashDefect_q1_u2

@[simp] theorem edge0_source (tolerance bound : ℝ)
    (htolerance : 0 ≤ tolerance) (hbound : 3 ≤ bound) :
    (quittingFloorFreeRobustChargedRelation reward tolerance bound).src
      (edge0 tolerance bound htolerance hbound) = state1 bound hbound := rfl

@[simp] theorem edge0_target (tolerance bound : ℝ)
    (htolerance : 0 ≤ tolerance) (hbound : 3 ≤ bound) :
    (quittingFloorFreeRobustChargedRelation reward tolerance bound).tgt
      (edge0 tolerance bound htolerance hbound) = state0 bound hbound := rfl

@[simp] theorem edge2_source (tolerance bound : ℝ)
    (htolerance : 0 ≤ tolerance) (hbound : 3 ≤ bound) :
    (quittingFloorFreeRobustChargedRelation reward tolerance bound).src
      (edge2 tolerance bound htolerance hbound) = state0 bound hbound := rfl

@[simp] theorem edge2_target (tolerance bound : ℝ)
    (htolerance : 0 ≤ tolerance) (hbound : 3 ≤ bound) :
    (quittingFloorFreeRobustChargedRelation reward tolerance bound).tgt
      (edge2 tolerance bound htolerance hbound) = state2 bound hbound := rfl

@[simp] theorem edge1_source (tolerance bound : ℝ)
    (htolerance : 0 ≤ tolerance) (hbound : 3 ≤ bound) :
    (quittingFloorFreeRobustChargedRelation reward tolerance bound).src
      (edge1 tolerance bound htolerance hbound) = state2 bound hbound := rfl

@[simp] theorem edge1_target (tolerance bound : ℝ)
    (htolerance : 0 ≤ tolerance) (hbound : 3 ≤ bound) :
    (quittingFloorFreeRobustChargedRelation reward tolerance bound).tgt
      (edge1 tolerance bound htolerance hbound) = state1 bound hbound := rfl

@[simp] theorem edge0_root (tolerance bound : ℝ)
    (htolerance : 0 ≤ tolerance) (hbound : 3 ≤ bound) :
    (edge0 tolerance bound htolerance hbound).1.1.2 =
      quittingSimplexOfRoot (halfRoot 0) := rfl

@[simp] theorem edge2_root (tolerance bound : ℝ)
    (htolerance : 0 ≤ tolerance) (hbound : 3 ≤ bound) :
    (edge2 tolerance bound htolerance hbound).1.1.2 =
      quittingSimplexOfRoot (halfRoot 2) := rfl

@[simp] theorem edge1_root (tolerance bound : ℝ)
    (htolerance : 0 ≤ tolerance) (hbound : 3 ≤ bound) :
    (edge1 tolerance bound htolerance hbound).1.1.2 =
      quittingSimplexOfRoot (halfRoot 1) := rfl

@[simp] theorem exactHalfEdge_charge (tolerance bound : ℝ)
    (htolerance : 0 ≤ tolerance)
    (source target : QuittingRobustChargedState (Fin 4) bound)
    (owner : Fin 4) (hsuccessor) (hdefect) :
    (quittingFloorFreeRobustChargedRelation reward tolerance bound).charge
      (exactHalfEdge tolerance bound htolerance source target owner
        hsuccessor hdefect) = 1 / 2 := by
  change quittingRootAbsorptionMass
    (quittingRootOfSimplex (quittingSimplexOfRoot (halfRoot owner))) = 1 / 2
  rw [quittingRootOfSimplex_simplexOfRoot, halfRoot_absorptionMass]

@[simp] theorem edge0_charge (tolerance bound : ℝ)
    (htolerance : 0 ≤ tolerance) (hbound : 3 ≤ bound) :
    (quittingFloorFreeRobustChargedRelation reward tolerance bound).charge
      (edge0 tolerance bound htolerance hbound) = 1 / 2 := by
  apply exactHalfEdge_charge

@[simp] theorem edge2_charge (tolerance bound : ℝ)
    (htolerance : 0 ≤ tolerance) (hbound : 3 ≤ bound) :
    (quittingFloorFreeRobustChargedRelation reward tolerance bound).charge
      (edge2 tolerance bound htolerance hbound) = 1 / 2 := by
  apply exactHalfEdge_charge

@[simp] theorem edge1_charge (tolerance bound : ℝ)
    (htolerance : 0 ≤ tolerance) (hbound : 3 ≤ bound) :
    (quittingFloorFreeRobustChargedRelation reward tolerance bound).charge
      (edge1 tolerance bound htolerance hbound) = 1 / 2 := by
  apply exactHalfEdge_charge

/-- The three exact robust edges form a positive-charge cycle, so no
single-valued potential can decrease by every edge's charge. -/
theorem no_potential (tolerance bound : ℝ) (htolerance : 0 ≤ tolerance)
    (hbound : 3 ≤ bound) :
    ¬∃ potential : QuittingRobustChargedState (Fin 4) bound → ℝ,
      (quittingFloorFreeRobustChargedRelation reward tolerance bound).IsPotential
        potential := by
  rintro ⟨potential, hpotential⟩
  have h0 := hpotential (edge0 tolerance bound htolerance hbound)
  have h2 := hpotential (edge2 tolerance bound htolerance hbound)
  have h1 := hpotential (edge1 tolerance bound htolerance hbound)
  simp only [edge0_source, edge0_target, edge2_source, edge2_target,
    edge1_source, edge1_target, edge0_charge, edge2_charge,
    edge1_charge] at h0 h2 h1
  linarith

end GameTheory.ThreeOwnerRobustCycle

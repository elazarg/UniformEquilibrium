import UniformEquilibrium.Quitting.Projective.RobustChargedPath
import UniformEquilibrium.Quitting.Projective.FloorFreeForwardPacketInputRemoval

/-! # Exact conversion between robust paths and floor-free finite packets -/

noncomputable section

namespace GameTheory

open Math.ChargedPathBudget Math.Probability

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {tolerance bound chargeTarget : ℝ}

/-- Every literal robust relation path is a floor-free weighted packet. The
packet target is the path's exact total charge, not merely a lower request. -/
def quittingRobustChargedPathToFloorFreePacket
    {source target}
    (path : (quittingFloorFreeRobustChargedRelation reward tolerance bound).Path
      source target) :
    QuittingFloorFreeAbsorptionWeightedForwardPacket reward
      (quittingForwardPacketCoordinateBox bound) tolerance path.chargeSum := {
  roots := fun time ↦
    quittingRootOfSimplex (quittingRobustChargedPathRoot path time)
  value := fun time ↦ (quittingRobustChargedPathValue path time).1
  horizon := path.length
  value_mem := by
    intro time _htime
    exact (quittingRobustChargedPathValue path time).2
  bellman := by
    intro time htime who
    exact (quittingRobustChargedPath_step path htime who).1
  regret := by
    intro time htime who
    exact (quittingRobustChargedPath_step path htime who).2
  chargeTarget_le := by
    rw [quittingRobustChargedPath_chargeSum_eq]
}

@[simp] theorem quittingRobustChargedPathToFloorFreePacket_horizon {source target}
    (path : (quittingFloorFreeRobustChargedRelation reward tolerance bound).Path
      source target) :
    (quittingRobustChargedPathToFloorFreePacket path).horizon =
      path.length := rfl

@[simp] theorem quittingRobustChargedPathToFloorFreePacket_value {source target}
    (path : (quittingFloorFreeRobustChargedRelation reward tolerance bound).Path
      source target) (time : ℕ) :
    (quittingRobustChargedPathToFloorFreePacket path).value time =
      (quittingRobustChargedPathValue path time).1 := rfl

@[simp] theorem quittingRobustChargedPathToFloorFreePacket_roots {source target}
    (path : (quittingFloorFreeRobustChargedRelation reward tolerance bound).Path
      source target) (time : ℕ) :
    (quittingRobustChargedPathToFloorFreePacket path).roots time =
      quittingRootOfSimplex (quittingRobustChargedPathRoot path time) := rfl

theorem quittingRobustChargedPathToFloorFreePacket_charge_eq {source target}
    (path : (quittingFloorFreeRobustChargedRelation reward tolerance bound).Path
      source target) :
    ∑ time ∈ Finset.range
        (quittingRobustChargedPathToFloorFreePacket path).horizon,
        quittingRootAbsorptionMass
          ((quittingRobustChargedPathToFloorFreePacket path).roots time) =
      path.chargeSum := by
  exact (quittingRobustChargedPath_chargeSum_eq path).symm

/-- Clamp arbitrary dates to a packet's horizon and retain the box proof. -/
def QuittingFloorFreeAbsorptionWeightedForwardPacket.robustStateAt
    (packet : QuittingFloorFreeAbsorptionWeightedForwardPacket reward
      (quittingForwardPacketCoordinateBox bound) tolerance chargeTarget)
    (time : ℕ) : QuittingRobustChargedState (Fin 4) bound :=
  ⟨packet.value (min time packet.horizon),
    packet.value_mem _ (Nat.min_le_right _ _)⟩

@[simp] theorem QuittingFloorFreeAbsorptionWeightedForwardPacket.robustStateAt_val
    (packet : QuittingFloorFreeAbsorptionWeightedForwardPacket reward
      (quittingForwardPacketCoordinateBox bound) tolerance chargeTarget)
    {time : ℕ} (htime : time ≤ packet.horizon) :
    (packet.robustStateAt time).1 = packet.value time := by
  simp [robustStateAt, Nat.min_eq_left htime]

/-- The literal robust edge at one live packet date. -/
def QuittingFloorFreeAbsorptionWeightedForwardPacket.robustEdgeAt
    (packet : QuittingFloorFreeAbsorptionWeightedForwardPacket reward
      (quittingForwardPacketCoordinateBox bound) tolerance chargeTarget)
    (time : ℕ) (htime : time < packet.horizon) :
    QuittingRobustChargedEdge reward tolerance bound := by
  let data : QuittingRobustChargedEdgeData (Fin 4) bound :=
    ((packet.robustStateAt time, quittingSimplexOfRoot (packet.roots time)),
      packet.robustStateAt (time + 1))
  refine ⟨data, ?_⟩
  intro who
  change |(packet.robustStateAt (time + 1)).1 who -
      quittingRootSuccessorPayoff reward (packet.robustStateAt time).1
        (quittingRootOfSimplex (quittingSimplexOfRoot (packet.roots time))) who| ≤
      tolerance * quittingRootAbsorptionMass
        (quittingRootOfSimplex (quittingSimplexOfRoot (packet.roots time))) ∧
    quittingRootCoordinateNashDefect reward (packet.robustStateAt time).1
        (quittingRootOfSimplex (quittingSimplexOfRoot (packet.roots time))) who ≤
      tolerance * quittingRootAbsorptionMass
        (quittingRootOfSimplex (quittingSimplexOfRoot (packet.roots time)))
  rw [packet.robustStateAt_val htime.le,
    packet.robustStateAt_val (Nat.succ_le_iff.mpr htime),
    quittingRootOfSimplex_simplexOfRoot]
  exact ⟨packet.bellman time htime who, packet.regret time htime who⟩

@[simp] theorem QuittingFloorFreeAbsorptionWeightedForwardPacket.robustEdgeAt_source
    (packet : QuittingFloorFreeAbsorptionWeightedForwardPacket reward
      (quittingForwardPacketCoordinateBox bound) tolerance chargeTarget)
    (time : ℕ) (htime : time < packet.horizon) :
    (quittingFloorFreeRobustChargedRelation reward tolerance bound).src
        (packet.robustEdgeAt time htime) = packet.robustStateAt time := rfl

@[simp] theorem QuittingFloorFreeAbsorptionWeightedForwardPacket.robustEdgeAt_target
    (packet : QuittingFloorFreeAbsorptionWeightedForwardPacket reward
      (quittingForwardPacketCoordinateBox bound) tolerance chargeTarget)
    (time : ℕ) (htime : time < packet.horizon) :
    (quittingFloorFreeRobustChargedRelation reward tolerance bound).tgt
        (packet.robustEdgeAt time htime) = packet.robustStateAt (time + 1) := rfl

@[simp] theorem QuittingFloorFreeAbsorptionWeightedForwardPacket.robustEdgeAt_root
    (packet : QuittingFloorFreeAbsorptionWeightedForwardPacket reward
      (quittingForwardPacketCoordinateBox bound) tolerance chargeTarget)
    (time : ℕ) (htime : time < packet.horizon) :
    (packet.robustEdgeAt time htime).1.1.2 =
      quittingSimplexOfRoot (packet.roots time) := rfl

@[simp] theorem QuittingFloorFreeAbsorptionWeightedForwardPacket.robustEdgeAt_charge
    (packet : QuittingFloorFreeAbsorptionWeightedForwardPacket reward
      (quittingForwardPacketCoordinateBox bound) tolerance chargeTarget)
    (time : ℕ) (htime : time < packet.horizon) :
    (quittingFloorFreeRobustChargedRelation reward tolerance bound).charge
        (packet.robustEdgeAt time htime) =
      quittingRootAbsorptionMass (packet.roots time) := by
  simp only [quittingFloorFreeRobustChargedRelation, robustEdgeAt_root,
    quittingRootOfSimplex_simplexOfRoot]

/-- The literal subpath of `length` packet rows beginning at `start`. -/
def QuittingFloorFreeAbsorptionWeightedForwardPacket.robustPathFrom
    (packet : QuittingFloorFreeAbsorptionWeightedForwardPacket reward
      (quittingForwardPacketCoordinateBox bound) tolerance chargeTarget)
    (start : ℕ) : (length : ℕ) → start + length ≤ packet.horizon →
    (quittingFloorFreeRobustChargedRelation reward tolerance bound).Path
      (packet.robustStateAt start) (packet.robustStateAt (start + length))
  | 0, _horizon => .nil (packet.robustStateAt start)
  | length + 1, hhorizon => by
      have hstart : start < packet.horizon := by omega
      have hrest : start + 1 + length ≤ packet.horizon := by omega
      let edge := packet.robustEdgeAt start hstart
      let rest := packet.robustPathFrom (start + 1) length hrest
      have htarget : packet.robustStateAt (start + 1 + length) =
          packet.robustStateAt (start + (length + 1)) := by
        congr 1
        omega
      have hsource : packet.robustStateAt (start + 1) =
          (quittingFloorFreeRobustChargedRelation reward tolerance bound).tgt edge :=
        (packet.robustEdgeAt_target start hstart).symm
      let joined :
          (quittingFloorFreeRobustChargedRelation reward tolerance bound).Path
            ((quittingFloorFreeRobustChargedRelation
              reward tolerance bound).src edge)
            (packet.robustStateAt (start + (length + 1))) :=
        .cons edge ((rest.castTgt htarget).castSrc hsource)
      have hinitial :
          (quittingFloorFreeRobustChargedRelation reward tolerance bound).src edge =
            packet.robustStateAt start :=
        packet.robustEdgeAt_source start hstart
      exact joined.castSrc hinitial

/-- The full robust relation path encoded by a floor-free weighted packet. -/
def QuittingFloorFreeAbsorptionWeightedForwardPacket.robustPath
    (packet : QuittingFloorFreeAbsorptionWeightedForwardPacket reward
      (quittingForwardPacketCoordinateBox bound) tolerance chargeTarget) :
    (quittingFloorFreeRobustChargedRelation reward tolerance bound).Path
      (packet.robustStateAt 0) (packet.robustStateAt packet.horizon) := by
  exact (packet.robustPathFrom 0 packet.horizon (by omega)).castTgt (by
    congr 1
    omega)

@[simp] theorem QuittingFloorFreeAbsorptionWeightedForwardPacket.robustPathFrom_length
    (packet : QuittingFloorFreeAbsorptionWeightedForwardPacket reward
      (quittingForwardPacketCoordinateBox bound) tolerance chargeTarget)
    (start length : ℕ) (hhorizon : start + length ≤ packet.horizon) :
    (packet.robustPathFrom start length hhorizon).length = length := by
  induction length generalizing start with
  | zero => rfl
  | succ length ih =>
      simp only [robustPathFrom]
      rw [Math.ChargedPathBudget.ChargedRelation.Path.length_castSrc,
        Math.ChargedPathBudget.ChargedRelation.Path.length_cons,
        Math.ChargedPathBudget.ChargedRelation.Path.length_castSrc,
        Math.ChargedPathBudget.ChargedRelation.Path.length_castTgt, ih]

@[simp] theorem QuittingFloorFreeAbsorptionWeightedForwardPacket.robustPath_length
    (packet : QuittingFloorFreeAbsorptionWeightedForwardPacket reward
      (quittingForwardPacketCoordinateBox bound) tolerance chargeTarget) :
    packet.robustPath.length = packet.horizon := by
  unfold robustPath
  rw [Math.ChargedPathBudget.ChargedRelation.Path.length_castTgt,
    packet.robustPathFrom_length]

theorem QuittingFloorFreeAbsorptionWeightedForwardPacket.robustPathFrom_value
    (packet : QuittingFloorFreeAbsorptionWeightedForwardPacket reward
      (quittingForwardPacketCoordinateBox bound) tolerance chargeTarget)
    (start length : ℕ) (hhorizon : start + length ≤ packet.horizon)
    {time : ℕ} (htime : time ≤ length) :
    quittingRobustChargedPathValue
        (packet.robustPathFrom start length hhorizon) time =
      packet.robustStateAt (start + time) := by
  induction length generalizing start time with
  | zero =>
      have hzero : time = 0 := by omega
      subst time
      rfl
  | succ length ih =>
      cases time with
      | zero =>
          simp only [robustPathFrom, quittingRobustChargedPathValue_castSrc,
            quittingRobustChargedPathValue]
          exact packet.robustEdgeAt_source start (by omega)
      | succ time =>
          have htimeRest : time ≤ length := by omega
          simp only [robustPathFrom, quittingRobustChargedPathValue_castSrc,
            quittingRobustChargedPathValue,
            quittingRobustChargedPathValue_castTgt]
          have hvalue := ih (start + 1) (by omega) htimeRest
          convert hvalue using 1
          congr 1
          omega

theorem QuittingFloorFreeAbsorptionWeightedForwardPacket.robustPathFrom_root
    (packet : QuittingFloorFreeAbsorptionWeightedForwardPacket reward
      (quittingForwardPacketCoordinateBox bound) tolerance chargeTarget)
    (start length : ℕ) (hhorizon : start + length ≤ packet.horizon)
    {time : ℕ} (htime : time < length) :
    quittingRobustChargedPathRoot
        (packet.robustPathFrom start length hhorizon) time =
      quittingSimplexOfRoot (packet.roots (start + time)) := by
  induction length generalizing start time with
  | zero => omega
  | succ length ih =>
      cases time with
      | zero =>
          simp only [robustPathFrom, quittingRobustChargedPathRoot_castSrc,
            quittingRobustChargedPathRoot]
          exact packet.robustEdgeAt_root start (by omega)
      | succ time =>
          have htimeRest : time < length := by omega
          simp only [robustPathFrom, quittingRobustChargedPathRoot_castSrc,
            quittingRobustChargedPathRoot,
            quittingRobustChargedPathRoot_castTgt]
          have hroot := ih (start + 1) (by omega) htimeRest
          convert hroot using 1
          congr 2
          omega

/-- The path conversion preserves every packet value through the endpoint. -/
theorem QuittingFloorFreeAbsorptionWeightedForwardPacket.robustPath_value_eq
    (packet : QuittingFloorFreeAbsorptionWeightedForwardPacket reward
      (quittingForwardPacketCoordinateBox bound) tolerance chargeTarget)
    {time : ℕ} (htime : time ≤ packet.horizon) :
    (quittingRobustChargedPathValue packet.robustPath time).1 =
      packet.value time := by
  unfold robustPath
  rw [quittingRobustChargedPathValue_castTgt,
    packet.robustPathFrom_value 0 packet.horizon (by omega) htime,
    packet.robustStateAt_val (show 0 + time ≤ packet.horizon by
      simpa only [zero_add] using htime)]
  simp only [zero_add]

/-- The path conversion preserves every live packet root literally in simplex
coordinates. -/
theorem QuittingFloorFreeAbsorptionWeightedForwardPacket.robustPath_root_eq
    (packet : QuittingFloorFreeAbsorptionWeightedForwardPacket reward
      (quittingForwardPacketCoordinateBox bound) tolerance chargeTarget)
    {time : ℕ} (htime : time < packet.horizon) :
    quittingRobustChargedPathRoot packet.robustPath time =
      quittingSimplexOfRoot (packet.roots time) := by
  unfold robustPath
  rw [quittingRobustChargedPathRoot_castTgt,
    packet.robustPathFrom_root 0 packet.horizon (by omega) htime]
  simp only [zero_add]

theorem QuittingFloorFreeAbsorptionWeightedForwardPacket.robustPathFrom_charge_eq
    (packet : QuittingFloorFreeAbsorptionWeightedForwardPacket reward
      (quittingForwardPacketCoordinateBox bound) tolerance chargeTarget)
    (start length : ℕ) (hhorizon : start + length ≤ packet.horizon) :
    (packet.robustPathFrom start length hhorizon).chargeSum =
      ∑ time ∈ Finset.range length,
        quittingRootAbsorptionMass (packet.roots (start + time)) := by
  induction length generalizing start with
  | zero => rfl
  | succ length ih =>
      simp only [robustPathFrom]
      rw [Math.ChargedPathBudget.ChargedRelation.Path.chargeSum_castSrc,
        Math.ChargedPathBudget.ChargedRelation.Path.chargeSum_cons,
        Math.ChargedPathBudget.ChargedRelation.Path.chargeSum_castSrc,
        Math.ChargedPathBudget.ChargedRelation.Path.chargeSum_castTgt,
        packet.robustEdgeAt_charge, ih, Finset.sum_range_succ']
      have hshift :
          (∑ time ∈ Finset.range length,
            quittingRootAbsorptionMass (packet.roots (start + 1 + time))) =
          ∑ time ∈ Finset.range length,
            quittingRootAbsorptionMass (packet.roots (start + (time + 1))) := by
        apply Finset.sum_congr rfl
        intro time _htime
        congr 2
        omega
      rw [hshift]
      exact add_comm _ _

theorem QuittingFloorFreeAbsorptionWeightedForwardPacket.robustPath_charge_eq
    (packet : QuittingFloorFreeAbsorptionWeightedForwardPacket reward
      (quittingForwardPacketCoordinateBox bound) tolerance chargeTarget) :
    packet.robustPath.chargeSum =
      ∑ time ∈ Finset.range packet.horizon,
        quittingRootAbsorptionMass (packet.roots time) := by
  unfold robustPath
  rw [Math.ChargedPathBudget.ChargedRelation.Path.chargeSum_castTgt,
    packet.robustPathFrom_charge_eq]
  simp only [zero_add]

end GameTheory

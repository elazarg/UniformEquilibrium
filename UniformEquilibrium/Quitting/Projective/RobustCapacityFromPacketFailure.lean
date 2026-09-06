import UniformEquilibrium.Quitting.Projective.RobustChargedRelationPacketAdapter
import UniformEquilibrium.Quitting.Projective.FloorFreeForwardPacketInputRemoval
import UniformEquilibrium.Quitting.Projective.AbsorptionWeightedForwardPacketProducer

/-! # Finite robust capacity forced by failure of floor-free packet production -/

noncomputable section

namespace GameTheory

open Math.ChargedPathBudget Math.Probability

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {oldTolerance newTolerance bound chargeTarget : ℝ}
variable {carrier : Set (Payoff (Fin 4))}

/-- Enlarging the tolerance preserves a floor-free weighted packet, literally
preserving its root sequence, values, horizon, and charge target. -/
def QuittingFloorFreeAbsorptionWeightedForwardPacket.weakenTolerance
    (packet : QuittingFloorFreeAbsorptionWeightedForwardPacket reward
      carrier oldTolerance chargeTarget)
    (hle : oldTolerance ≤ newTolerance) :
    QuittingFloorFreeAbsorptionWeightedForwardPacket reward
      carrier newTolerance chargeTarget := {
  roots := packet.roots
  value := packet.value
  horizon := packet.horizon
  value_mem := packet.value_mem
  bellman := by
    intro time htime who
    exact (packet.bellman time htime who).trans
      (mul_le_mul_of_nonneg_right hle
        (quittingRootAbsorptionMass_nonneg (packet.roots time)))
  regret := by
    intro time htime who
    exact (packet.regret time htime who).trans
      (mul_le_mul_of_nonneg_right hle
        (quittingRootAbsorptionMass_nonneg (packet.roots time)))
  chargeTarget_le := packet.chargeTarget_le }

@[simp] theorem QuittingFloorFreeAbsorptionWeightedForwardPacket.weakenTolerance_roots
    (packet : QuittingFloorFreeAbsorptionWeightedForwardPacket reward
      carrier oldTolerance chargeTarget)
    (hle : oldTolerance ≤ newTolerance) (time : ℕ) :
    (packet.weakenTolerance hle).roots time = packet.roots time := rfl

@[simp] theorem QuittingFloorFreeAbsorptionWeightedForwardPacket.weakenTolerance_value
    (packet : QuittingFloorFreeAbsorptionWeightedForwardPacket reward
      carrier oldTolerance chargeTarget)
    (hle : oldTolerance ≤ newTolerance) (time : ℕ) :
    (packet.weakenTolerance hle).value time = packet.value time := rfl

@[simp] theorem QuittingFloorFreeAbsorptionWeightedForwardPacket.weakenTolerance_horizon
    (packet : QuittingFloorFreeAbsorptionWeightedForwardPacket reward
      carrier oldTolerance chargeTarget)
    (hle : oldTolerance ≤ newTolerance) :
    (packet.weakenTolerance hle).horizon = packet.horizon := rfl

/-- A robust path whose charge reaches a requested target produces a packet at
that requested target. -/
def quittingRobustChargedPathToFloorFreePacketAtLeast
    {source target}
    (path : (quittingFloorFreeRobustChargedRelation reward oldTolerance bound).Path
      source target) {requested : ℝ} (hrequested : requested ≤ path.chargeSum) :
    QuittingFloorFreeAbsorptionWeightedForwardPacket reward
      (quittingForwardPacketCoordinateBox bound) oldTolerance requested := by
  let packet := quittingRobustChargedPathToFloorFreePacket path
  exact {
    roots := packet.roots
    value := packet.value
    horizon := packet.horizon
    value_mem := packet.value_mem
    bellman := packet.bellman
    regret := packet.regret
    chargeTarget_le := hrequested.trans packet.chargeTarget_le }

/-- Failure to produce a packet at one charge target strictly bounds the
charge of every robust path at that tolerance and box. -/
theorem quittingFloorFreeRobustChargedPath_chargeSum_lt_of_noPacket
    (chargeBound : ℝ)
    (hnoPacket : ¬ Nonempty
      (QuittingFloorFreeAbsorptionWeightedForwardPacket reward
        (quittingForwardPacketCoordinateBox bound) oldTolerance chargeBound))
    {source target}
    (path : (quittingFloorFreeRobustChargedRelation reward oldTolerance bound).Path
      source target) :
    path.chargeSum < chargeBound := by
  by_contra hnot
  exact hnoPacket ⟨quittingRobustChargedPathToFloorFreePacketAtLeast
    path (le_of_not_gt hnot)⟩

/-- Failure to produce a packet at one charge target gives an explicit upper
bound for every robust path charge at that tolerance and box. -/
theorem quittingFloorFreeRobustChargedRelation_hasFiniteBudget_of_noPacket
    (chargeBound : ℝ)
    (hnoPacket : ¬ Nonempty
      (QuittingFloorFreeAbsorptionWeightedForwardPacket reward
        (quittingForwardPacketCoordinateBox bound) oldTolerance chargeBound)) :
    (quittingFloorFreeRobustChargedRelation reward oldTolerance bound).HasFiniteBudget := by
  refine ⟨chargeBound, ?_⟩
  rintro pathCharge ⟨source, target, path, rfl⟩
  exact (quittingFloorFreeRobustChargedPath_chargeSum_lt_of_noPacket
    chargeBound hnoPacket path).le

/-- If the all-tolerance floor-free producer fails in a supplied box, then a
strictly positive rational tolerance at most one has finite robust capacity in
that same box. -/
theorem exists_positiveRationalTolerance_hasFiniteRobustBudget_of_not_floorFree
    (hfailure :
      ¬ HasFloorFreeAbsorptionWeightedFiniteForwardPackets reward bound) :
    ∃ tolerance : ℚ, 0 < (tolerance : ℝ) ∧ (tolerance : ℝ) ≤ 1 ∧
      (quittingFloorFreeRobustChargedRelation reward
        (tolerance : ℝ) bound).HasFiniteBudget := by
  rw [HasFloorFreeAbsorptionWeightedFiniteForwardPackets] at hfailure
  push Not at hfailure
  obtain ⟨failedTolerance, hfailedTolerance, chargeBound,
    _hchargeBound, hnoPacket⟩ := hfailure
  have hupper : 0 < min 1 failedTolerance :=
    lt_min zero_lt_one hfailedTolerance
  obtain ⟨tolerance, htolerance, htoleranceUpper⟩ := exists_rat_btwn hupper
  refine ⟨tolerance, htolerance, ?_, ?_⟩
  · exact le_trans htoleranceUpper.le (min_le_left _ _)
  · apply quittingFloorFreeRobustChargedRelation_hasFiniteBudget_of_noPacket
      chargeBound
    intro packet
    exact hnoPacket.false (packet.some.weakenTolerance
      (le_trans htoleranceUpper.le (min_le_right _ _)))

/-- In a normal four-player quitting game with rewards bounded by a positive
`M`, failure of uniform-payoff existence forces finite robust capacity in the
literal outer smoothing box `M + 3`, at some positive rational tolerance no
larger than one. -/
theorem exists_positiveRationalTolerance_hasFiniteRobustBudget_of_noUniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnormal : ∀ player, IsQuittingNormalPlayer reward player)
    (hnoUniform : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ tolerance : ℚ, 0 < (tolerance : ℝ) ∧ (tolerance : ℝ) ≤ 1 ∧
      (quittingFloorFreeRobustChargedRelation reward
        (tolerance : ℝ) (M + 3)).HasFiniteBudget := by
  apply exists_positiveRationalTolerance_hasFiniteRobustBudget_of_not_floorFree
  intro hfloorFree
  have hweighted :
      HasAbsorptionWeightedFiniteForwardPackets reward (M + 3) :=
    hasAbsorptionWeightedFiniteForwardPackets_of_floorFree
      reward hM hreward hnormal hfloorFree
  apply hnoUniform
  exact quittingGame_exists_uniformEquilibriumPayoff_of_absorptionWeightedPackets
    reward (M + 3) (by linarith)
      (fun terminal player ↦ (hreward terminal player).trans (by linarith))
      hweighted

end GameTheory

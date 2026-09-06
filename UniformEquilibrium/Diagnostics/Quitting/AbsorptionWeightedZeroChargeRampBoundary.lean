import UniformEquilibrium.Quitting.Projective.AbsorptionWeightedForwardPacketRepair
import UniformEquilibrium.Quitting.Root.TerminalDebtPrefix
import UniformEquilibrium.Quitting.Punishment.ContinueFloor

/-! # Zero-charge boundary for absorption-weighted Bellman residuals -/

noncomputable section

namespace GameTheory.AbsorptionWeightedZeroChargeRampBoundary

open Math.Probability
open QuittingSureSetOwnerRepair

/-- The zero Fin4 quitting reward table. -/
def reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) := fun _ _ ↦ 0

/-- A linear payoff annotation over a positive finite horizon. -/
def rampValue (horizon time : ℕ) : Payoff (Fin 4) :=
  fun _ ↦ (time : ℝ) / horizon

/-- Exact forward evaluation from the ramp's zero initial annotation under
the same all-Continue roots. -/
def exactValue : ℕ → Payoff (Fin 4)
  | 0 => 0
  | time + 1 => quittingRootSuccessorPayoff reward (exactValue time)
      (quittingAllContinueRoot : Fin 4 → PMF Bool)

@[simp] theorem exactValue_eq_zero (time : ℕ) : exactValue time = 0 := by
  induction time with
  | zero => rfl
  | succ time ih =>
      simp only [exactValue, ih]
      exact quittingRootSuccessorPayoff_allContinueRoot_eq reward 0

@[simp] theorem punishmentValue_eq_zero (player : Fin 4) :
    quittingPunishmentValue reward player = 0 := by
  apply le_antisymm
  · refine (quittingPunishmentValue_le_max_solo reward player).trans ?_
    simp [quittingSetReward, reward]
  · refine (show 0 ≤ quittingContinueFloor reward player from ?_).trans
      (quittingContinueFloor_le_quittingPunishmentValue reward player)
    unfold quittingContinueFloor quittingBlockContinueFloor
    apply Math.Finset.le_insertMin le_rfl
    intro terminal _
    simp [reward]

@[simp] theorem allContinue_absorptionMass :
    quittingRootAbsorptionMass
      (quittingAllContinueRoot : Fin 4 → PMF Bool) = 0 := by
  simp [quittingRootAbsorptionMass,
    quittingStationaryContinueMass_allContinueRoot]

@[simp] theorem successor_rampValue
    (horizon time : ℕ) :
    quittingRootSuccessorPayoff reward (rampValue horizon time)
      (quittingAllContinueRoot : Fin 4 → PMF Bool) =
        rampValue horizon time :=
  quittingRootSuccessorPayoff_allContinueRoot_eq _ _

/-- Every local Bellman residual of the ramp is exactly `1 / horizon`. -/
theorem local_bellman_residual_eq_inv
    {horizon : ℕ} (hhorizon : 0 < horizon) (time : ℕ) (player : Fin 4) :
    |rampValue horizon (time + 1) player -
        quittingRootSuccessorPayoff reward (rampValue horizon time)
          (quittingAllContinueRoot : Fin 4 → PMF Bool) player| =
      1 / (horizon : ℝ) := by
  rw [successor_rampValue]
  simp only [rampValue]
  have hreal : 0 < (horizon : ℝ) := Nat.cast_pos.mpr hhorizon
  have heq : ((time + 1 : ℕ) : ℝ) / horizon - (time : ℝ) / horizon =
      1 / (horizon : ℝ) := by
    rw [Nat.cast_add, Nat.cast_one]
    ring
  rw [heq, abs_of_pos (one_div_pos.mpr hreal)]

/-- At every displayed nonnegative ramp value the all-Continue row has zero
ordinary mixed-root regret. -/
theorem coordinateNashDefect_eq_zero
    {horizon : ℕ} (time : ℕ) (player : Fin 4) :
    quittingRootCoordinateNashDefect reward (rampValue horizon time)
      (quittingAllContinueRoot : Fin 4 → PMF Bool) player = 0 := by
  have hnonneg : 0 ≤ (time : ℝ) / (horizon : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart,
    quittingRootEndpointDifference_allContinueRoot]
  simp [quittingAllContinueRoot, reward, rampValue]
  exact hnonneg

/-- Every displayed ramp annotation through the horizon lies in the unit
coordinate box. -/
theorem rampValue_mem_unitBox
    {horizon time : ℕ} (hhorizon : 0 < horizon) (htime : time ≤ horizon) :
    rampValue horizon time ∈ quittingForwardPacketCoordinateBox 1 := by
  intro player
  have hn : 0 ≤ (time : ℝ) / (horizon : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  simp only [rampValue, abs_of_nonneg hn]
  exact (div_le_one (Nat.cast_pos.mpr hhorizon)).2 (Nat.cast_le.mpr htime)

/-- The ramp starts at zero and ends one unit away from exact all-Continue
recomputation, despite every row having zero absorption charge. -/
theorem endpoint_error_one_and_zero_charge
    {horizon : ℕ} (hhorizon : 0 < horizon) (player : Fin 4) :
    rampValue horizon 0 player = 0 ∧
    rampValue horizon horizon player = 1 ∧
    |rampValue horizon horizon player - exactValue horizon player| = 1 ∧
    (∑ _time ∈ Finset.range horizon,
      quittingRootAbsorptionMass
        (quittingAllContinueRoot : Fin 4 → PMF Bool)) = 0 := by
  have hne : (horizon : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hhorizon)
  simp [rampValue, hne]

/-- Thus no positive-horizon ramp row satisfies an absorption-weighted
Bellman bound, although its ordinary regret and absorption charge are zero. -/
theorem ramp_residual_not_absorptionWeighted
    {horizon : ℕ} (hhorizon : 0 < horizon) (time : ℕ)
    (player : Fin 4) (tolerance : ℝ) :
    quittingRootCoordinateNashDefect reward (rampValue horizon time)
        (quittingAllContinueRoot : Fin 4 → PMF Bool) player = 0 ∧
      tolerance * quittingRootAbsorptionMass
        (quittingAllContinueRoot : Fin 4 → PMF Bool) = 0 ∧
      ¬ |rampValue horizon (time + 1) player -
          quittingRootSuccessorPayoff reward (rampValue horizon time)
            (quittingAllContinueRoot : Fin 4 → PMF Bool) player| ≤
        tolerance * quittingRootAbsorptionMass
          (quittingAllContinueRoot : Fin 4 → PMF Bool) := by
  refine ⟨coordinateNashDefect_eq_zero time player, by simp, ?_⟩
  rw [local_bellman_residual_eq_inv hhorizon, allContinue_absorptionMass, mul_zero]
  exact not_le.mpr (one_div_pos.mpr (Nat.cast_pos.mpr hhorizon))

end GameTheory.AbsorptionWeightedZeroChargeRampBoundary

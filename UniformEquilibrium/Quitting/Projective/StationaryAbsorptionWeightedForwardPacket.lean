import UniformEquilibrium.Quitting.Stationary.UpwardTranslation
import UniformEquilibrium.Quitting.Projective.AbsorptionWeightedForwardPacketProducer
import UniformEquilibrium.Quitting.Classification.ExistenceBranches

/-! # Stationary sources of absorption-weighted finite forward packets

A stationary approximate equilibrium with positive absorption generates
arbitrary finite charge by repetition. The source root and its literal
translated payoff are selected before the requested charge.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability

/-- A constant repetition of one stationary root and its literal
translated payoff is an absorption-weighted finite forward packet. -/
def quittingStationaryAbsorptionWeightedForwardPacket
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (root : Fin 4 → PMF Bool) (rewardBound error tolerance chargeTarget : ℝ)
    (horizon : ℕ) (herror : 0 ≤ error) (herrorMax : error ≤ 1)
    (htolerance : 2 * error ≤ tolerance)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) error (quittingStationaryProfile reward root))
    (hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound)
    (hcharge : chargeTarget ≤ horizon * quittingRootAbsorptionMass root) :
    QuittingAbsorptionWeightedForwardPacket reward
      (quittingForwardPacketCoordinateBox (rewardBound + 2)) tolerance chargeTarget := {
  roots := fun _ ↦ root
  value := fun _ ↦ quittingPayoffUpwardTranslate
    (quittingStationaryPayoffVector reward root) error
  horizon := horizon
  value_mem := by
    intro _time _htime player
    exact abs_stationaryUpwardTranslate_le_rewardBound_add_two
      reward root hreward herror herrorMax player
  bellman := by
    intro _time _htime player
    rw [quittingStationaryUpwardTranslate_sub_successor_eq]
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) herror)
      (quittingRootAbsorptionMass_nonneg root))]
    exact mul_le_mul_of_nonneg_right (by nlinarith [htolerance])
      (quittingRootAbsorptionMass_nonneg root)
  regret := by
    intro _time _htime player
    exact (quittingRootCoordinateNashDefect_stationaryUpwardTranslate_le
      reward root herror hnash player).trans
        (mul_le_mul_of_nonneg_right htolerance
          (quittingRootAbsorptionMass_nonneg root))
  rational := by
    intro target _time _htime
    have hfloor := punishmentValue_add_le_stationaryUpwardTranslate
      reward root hnash target
    nlinarith [herror, htolerance]
  chargeTarget_le := by
    simpa using hcharge }

@[simp] theorem quittingStationaryAbsorptionWeightedForwardPacket_roots
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (root : Fin 4 → PMF Bool) (rewardBound error tolerance chargeTarget : ℝ)
    (horizon : ℕ) (herror : 0 ≤ error) (herrorMax : error ≤ 1)
    (htolerance : 2 * error ≤ tolerance)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) error (quittingStationaryProfile reward root))
    (hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound)
    (hcharge : chargeTarget ≤ horizon * quittingRootAbsorptionMass root)
    (time : ℕ) :
    (quittingStationaryAbsorptionWeightedForwardPacket reward root rewardBound error
      tolerance chargeTarget horizon herror herrorMax htolerance hnash
      hreward hcharge).roots time = root := rfl

@[simp] theorem quittingStationaryAbsorptionWeightedForwardPacket_value
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (root : Fin 4 → PMF Bool) (rewardBound error tolerance chargeTarget : ℝ)
    (horizon : ℕ) (herror : 0 ≤ error) (herrorMax : error ≤ 1)
    (htolerance : 2 * error ≤ tolerance)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) error (quittingStationaryProfile reward root))
    (hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound)
    (hcharge : chargeTarget ≤ horizon * quittingRootAbsorptionMass root)
    (time : ℕ) :
    (quittingStationaryAbsorptionWeightedForwardPacket reward root rewardBound error
      tolerance chargeTarget horizon herror herrorMax htolerance hnash
      hreward hcharge).value time = quittingPayoffUpwardTranslate
        (quittingStationaryPayoffVector reward root) error := rfl

@[simp] theorem quittingStationaryAbsorptionWeightedForwardPacket_charge
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (root : Fin 4 → PMF Bool) (rewardBound error tolerance chargeTarget : ℝ)
    (horizon : ℕ) (herror : 0 ≤ error) (herrorMax : error ≤ 1)
    (htolerance : 2 * error ≤ tolerance)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) error (quittingStationaryProfile reward root))
    (hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound)
    (hcharge : chargeTarget ≤ horizon * quittingRootAbsorptionMass root) :
    ∑ time ∈ Finset.range
        (quittingStationaryAbsorptionWeightedForwardPacket reward root rewardBound error
          tolerance chargeTarget horizon herror herrorMax htolerance hnash
          hreward hcharge).horizon,
      quittingRootAbsorptionMass
        ((quittingStationaryAbsorptionWeightedForwardPacket reward root rewardBound error
          tolerance chargeTarget horizon herror herrorMax htolerance hnash
          hreward hcharge).roots time) =
      horizon * quittingRootAbsorptionMass root := by
  change ∑ _time ∈ Finset.range horizon, quittingRootAbsorptionMass root =
    horizon * quittingRootAbsorptionMass root
  simp

/-- Repeating a fixed positive-absorption stationary root realizes every
requested finite charge; the horizon is the only field selected from the
charge target. -/
theorem exists_quittingStationaryAbsorptionWeightedForwardPacket
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (root : Fin 4 → PMF Bool) (rewardBound error tolerance chargeTarget : ℝ)
    (herror : 0 ≤ error) (herrorMax : error ≤ 1)
    (htolerance : 2 * error ≤ tolerance)
    (habsorption : 0 < quittingRootAbsorptionMass root)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) error (quittingStationaryProfile reward root))
    (hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound) :
    ∃ packet : QuittingAbsorptionWeightedForwardPacket reward
        (quittingForwardPacketCoordinateBox (rewardBound + 2)) tolerance chargeTarget,
      (∀ time, packet.roots time = root) ∧
        ∀ time, packet.value time = quittingPayoffUpwardTranslate
          (quittingStationaryPayoffVector reward root) error := by
  obtain ⟨horizon, hhorizon⟩ :=
    exists_nat_ge (chargeTarget / quittingRootAbsorptionMass root)
  have hcharge : chargeTarget ≤ horizon * quittingRootAbsorptionMass root :=
    (div_le_iff₀ habsorption).mp hhorizon
  let packet := quittingStationaryAbsorptionWeightedForwardPacket reward root
    rewardBound error tolerance chargeTarget horizon herror herrorMax htolerance
    hnash hreward hcharge
  exact ⟨packet, fun _time ↦ rfl, fun _time ↦ rfl⟩

/-- At each requested tolerance, branch S.1 selects one positive-absorption
root and literal stationary annotation that generate packets for every later
charge request. This exposes the source-before-charge quantifier order. -/
theorem exists_stationaryAbsorbingRoot_generating_weightedPackets
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (rewardBound : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound)
    (hstationary : QuittingStationaryεEquilibriumExistence reward)
    (hpositive : ∃ who, 0 < reward (quittingSingletonTerminal who) who)
    (tolerance : ℝ) (htolerance : 0 < tolerance) :
    ∃ error root, 0 < error ∧ error ≤ 1 ∧ 2 * error ≤ tolerance ∧
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) error
        (quittingStationaryProfile reward root) ∧
      0 < quittingRootAbsorptionMass root ∧
      ∀ chargeTarget,
        ∃ packet : QuittingAbsorptionWeightedForwardPacket reward
            (quittingForwardPacketCoordinateBox (rewardBound + 2))
            tolerance chargeTarget,
          (∀ time, packet.roots time = root) ∧
            ∀ time, packet.value time = quittingPayoffUpwardTranslate
              (quittingStationaryPayoffVector reward root) error := by
  obtain ⟨who, hsingleton⟩ := hpositive
  let error := min 1 (min (tolerance / 2)
    (reward (quittingSingletonTerminal who) who / 2))
  have herror : 0 < error := by
    dsimp only [error]
    apply lt_min (by norm_num)
    exact lt_min (div_pos htolerance (by norm_num))
      (div_pos hsingleton (by norm_num))
  have herrorMax : error ≤ 1 := min_le_left _ _
  have htwo : 2 * error ≤ tolerance := by
    have hle : error ≤ tolerance / 2 := by
      dsimp only [error]
      exact (min_le_right 1 _).trans (min_le_left _ _)
    linarith
  have herrorSingleton : error < reward (quittingSingletonTerminal who) who := by
    have hle : error ≤ reward (quittingSingletonTerminal who) who / 2 := by
      dsimp only [error]
      exact (min_le_right 1 _).trans (min_le_right _ _)
    linarith
  obtain ⟨root, hnash⟩ := hstationary error herror
  have habsorption := quittingRootAbsorptionMass_pos_of_stationaryNash_of_singleton
    reward root herror.le who herrorSingleton hnash
  refine ⟨error, root, herror, herrorMax, htwo, hnash, habsorption, ?_⟩
  intro chargeTarget
  exact exists_quittingStationaryAbsorptionWeightedForwardPacket reward root
    rewardBound error tolerance chargeTarget herror.le herrorMax htwo
    habsorption hnash hreward

/-- Branch S.1 plus one positive singleton payoff produces weighted packets
in the fixed reward box enlarged by two. -/
theorem hasAbsorptionWeightedFiniteForwardPackets_of_stationary
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (rewardBound : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound)
    (hstationary : QuittingStationaryεEquilibriumExistence reward)
    (hpositive : ∃ who, 0 < reward (quittingSingletonTerminal who) who) :
    HasAbsorptionWeightedFiniteForwardPackets reward (rewardBound + 2) := by
  intro tolerance htolerance
  obtain ⟨_error, _root, _herror, _herrorMax, _htwo, _hnash,
      _habsorption, hpackets⟩ :=
    exists_stationaryAbsorbingRoot_generating_weightedPackets reward rewardBound
      hreward hstationary hpositive tolerance htolerance
  intro chargeTarget _hcharge
  obtain ⟨packet, _hroots, _hvalue⟩ := hpackets chargeTarget
  exact ⟨packet⟩

end GameTheory


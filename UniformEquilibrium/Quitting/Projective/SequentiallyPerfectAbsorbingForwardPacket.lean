import UniformEquilibrium.Quitting.Classification.Existence.SequentiallyPerfectAbsorbingForwardSource
import UniformEquilibrium.Quitting.Projective.FloorFreeForwardPacketInputRemoval

/-! # Sequentially perfect sources of finite forward packets

One source sequence is chosen before every charge request. Its finite reversed
prefixes give floor-free packets in the reward box. The existing normal
burn-in conversion then supplies full exact forward packets in the same box.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability StochasticGame QuittingLCPClassification

/-- Reverse one literal S.3 prefix into a floor-free exact finite forward
packet. -/
def quittingSequentialReverseFloorFreePacket
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (roots : ℕ → Fin 4 → PMF Bool) (rewardBound sourceError supportError : ℝ)
    (chargeTarget : ℝ) (horizon : ℕ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound)
    (herror : 2 * sourceError ≤ supportError)
    (hperfect : ∀ time, QuittingRowεPerfect reward
      (quittingRootSequenceTailVector reward roots (time + 1))
      (roots time) sourceError)
    (hcharge : chargeTarget ≤ ∑ time ∈ Finset.range horizon,
      quittingRootAbsorptionMass (roots time)) :
    QuittingFloorFreeFiniteForwardPacket reward
      (quittingForwardPacketCoordinateBox rewardBound) supportError chargeTarget := {
  roots := quittingReversedRootPrefix roots horizon
  value := quittingReversedRootSequenceValue reward roots horizon
  horizon := horizon
  value_mem := by
    intro time _htime player
    exact abs_quittingRootSequenceTailVector_le reward roots hreward
      (horizon - time) player
  policy := fun _time htime ↦
    quittingReversedRootSequenceValue_policy reward roots htime
  support := by
    intro time htime
    have hnext : horizon - time = (horizon - 1 - time) + 1 := by omega
    have hsource := supportApproxNash_of_quittingRowεPerfect
      (hperfect (horizon - 1 - time))
    simpa only [quittingReversedRootSequenceValue,
      quittingReversedRootPrefix, hnext] using hsource.mono herror
  chargeTarget_le := by
    rw [sum_absorptionMass_quittingReversedRootPrefix]
    exact hcharge }

/-- For each support accuracy, branch S.3 selects one literal root sequence
before the charge target; reversed prefixes of that same sequence provide
every later floor-free packet. -/
theorem exists_sequentiallyPerfectSource_generating_floorFreePackets
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (rewardBound : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound)
    (hS3 : QuittingSequentiallyεPerfectAbsorbingExistence reward)
    (hpositive : ∃ who, 0 < reward (quittingSingletonTerminal who) who)
    (supportError : ℝ) (hsupportError : 0 < supportError) :
    ∃ sourceError roots,
      0 < sourceError ∧ 2 * sourceError ≤ supportError ∧
      (∀ time, QuittingRowεPerfect reward
        (quittingRootSequenceTailVector reward roots (time + 1))
        (roots time) sourceError) ∧
      IsCompletelyAbsorbing roots ∧
      QuittingRootSequenceTerminatesAfterEveryRestart roots ∧
      ∀ chargeTarget,
        ∃ horizon, ∃ packet : QuittingFloorFreeFiniteForwardPacket reward
            (quittingForwardPacketCoordinateBox rewardBound)
            supportError chargeTarget,
          packet.horizon = horizon ∧
          (∀ time, packet.roots time =
            quittingReversedRootPrefix roots horizon time) ∧
          (∀ time, packet.value time =
            quittingReversedRootSequenceValue reward roots horizon time) ∧
          (∑ time ∈ Finset.range packet.horizon,
            quittingRootAbsorptionMass (packet.roots time)) =
              ∑ time ∈ Finset.range horizon,
                quittingRootAbsorptionMass (roots time) := by
  obtain ⟨who, hsingleton⟩ := hpositive
  let sourceError := min (supportError / 2)
    (reward (quittingSingletonTerminal who) who / 2)
  have hsourceError : 0 < sourceError := by
    dsimp only [sourceError]
    exact lt_min (div_pos hsupportError (by norm_num))
      (div_pos hsingleton (by norm_num))
  have htwice : 2 * sourceError ≤ supportError := by
    have hle : sourceError ≤ supportError / 2 := by
      dsimp only [sourceError]
      exact min_le_left _ _
    linarith
  have hsourceSingleton :
      sourceError < reward (quittingSingletonTerminal who) who := by
    have hle : sourceError ≤
        reward (quittingSingletonTerminal who) who / 2 := by
      dsimp only [sourceError]
      exact min_le_right _ _
    linarith
  obtain ⟨roots, habsorbing, hperfect⟩ := hS3 sourceError hsourceError
  have hterminates :=
    quittingRootSequenceTerminatesAfterEveryRestart_of_rowPerfect_of_singleton
      reward roots who hsourceSingleton hperfect
  have hdiverges :=
    not_summable_quittingRootAbsorptionMass_of_terminatesAfterEveryRestart
      roots hterminates
  refine ⟨sourceError, roots, hsourceError, htwice, hperfect, habsorbing,
    hterminates, ?_⟩
  intro chargeTarget
  obtain ⟨horizon, hcharge⟩ :=
    exists_horizon_chargeTarget_le_sum_absorptionMass
      roots hdiverges chargeTarget
  let packet := quittingSequentialReverseFloorFreePacket reward roots
    rewardBound sourceError supportError chargeTarget horizon hreward htwice
    hperfect hcharge
  refine ⟨horizon, packet, rfl, fun _time ↦ rfl, fun _time ↦ rfl, ?_⟩
  exact sum_absorptionMass_quittingReversedRootPrefix roots horizon

/-- Branch S.3 and a positive singleton produce literal floor-free exact
packets in the original reward box. -/
theorem hasFloorFreeExactFiniteForwardPackets_of_sequentiallyPerfect
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (rewardBound : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound)
    (hS3 : QuittingSequentiallyεPerfectAbsorbingExistence reward)
    (hpositive : ∃ who, 0 < reward (quittingSingletonTerminal who) who) :
    HasFloorFreeExactFiniteForwardPackets reward rewardBound := by
  intro supportError hsupportError
  obtain ⟨_sourceError, _roots, _hsourceError, _htwice, _hperfect,
      _habsorbing, _hterminates, hpackets⟩ :=
    exists_sequentiallyPerfectSource_generating_floorFreePackets reward
      rewardBound hreward hS3 hpositive supportError hsupportError
  intro chargeTarget _hchargeTarget
  obtain ⟨_horizon, packet, _hhorizon, _hroots, _hvalue, _hcharge⟩ :=
    hpackets chargeTarget
  exact ⟨packet⟩

/-- Under all-player normality, the checked fixed burn-in removes an initial
segment of the reversed S.3 prefix and supplies the punishment floors without
changing the reward box. No claim is made that the final horizon is unchanged. -/
theorem hasExactFiniteForwardPackets_of_normal_of_sequentiallyPerfect
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (rewardBound : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound)
    (hnormal : ∀ player, IsQuittingNormalPlayer reward player)
    (hS3 : QuittingSequentiallyεPerfectAbsorbingExistence reward)
    (hpositive : ∃ who, 0 < reward (quittingSingletonTerminal who) who) :
    HasExactFiniteForwardPackets reward rewardBound := by
  obtain ⟨who, hsingleton⟩ := hpositive
  have hrewardBound : 0 < rewardBound := by
    have hle := hreward (quittingSingletonTerminal who) who
    linarith [le_abs_self (reward (quittingSingletonTerminal who) who)]
  apply hasExactFiniteForwardPackets_of_floorFree reward hrewardBound
    hreward hnormal
  exact hasFloorFreeExactFiniteForwardPackets_of_sequentiallyPerfect
    reward rewardBound hreward hS3 ⟨who, hsingleton⟩

end GameTheory


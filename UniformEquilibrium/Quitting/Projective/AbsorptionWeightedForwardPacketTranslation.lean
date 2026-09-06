import UniformEquilibrium.Quitting.Projective.AbsorptionWeightedForwardPacketProducer
import UniformEquilibrium.Quitting.Projective.FiniteForwardPacketRewardBoxReduction
import UniformEquilibrium.Quitting.Root.UpwardTranslation

/-! # Upward translation from exact to absorption-weighted packets -/

noncomputable section

namespace GameTheory

open Math.Probability

/-- Common upward translation converts one exact support packet into a
weighted packet in the fixed enlarged coordinate box. -/
def QuittingFiniteForwardPacket.upwardTranslate
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {B δ chargeTarget : ℝ}
    (packet : QuittingFiniteForwardPacket reward
      (quittingForwardPacketCoordinateBox B) δ chargeTarget)
    (hδ : 0 < δ) (hδmax : δ ≤ 1) :
    QuittingAbsorptionWeightedForwardPacket reward
      (quittingForwardPacketCoordinateBox (B + 2)) (3 * δ) chargeTarget := {
  roots := packet.roots
  value := fun time ↦ quittingPayoffUpwardTranslate (packet.value time) δ
  horizon := packet.horizon
  value_mem := by
    intro time htime player
    have hbound := packet.value_mem time htime player
    dsimp only [quittingPayoffUpwardTranslate]
    rw [abs_le] at hbound ⊢
    constructor <;> nlinarith
  bellman := by
    intro time htime player
    rw [quittingPayoffUpwardTranslate_sub_successor_eq reward
      (packet.value time) (packet.value (time + 1)) (packet.roots time) player δ
      (congrFun (packet.policy time htime) player)]
    have ha := quittingRootAbsorptionMass_nonneg (packet.roots time)
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hδ.le) ha)]
    nlinarith
  regret := by
    intro time htime player
    exact coordinateNashDefect_upwardTranslate_le_absorption
      reward (packet.value time) (packet.roots time) player hδ
        (packet.support time htime)
  rational := by
    intro target time htime
    have hfloor := packet.rational target time htime
    dsimp only [quittingPayoffUpwardTranslate]
    nlinarith
  chargeTarget_le := packet.chargeTarget_le }

private def QuittingAbsorptionWeightedForwardPacket.weakenTolerance
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {carrier : Set (Payoff (Fin 4))} {oldTolerance newTolerance chargeTarget : ℝ}
    (packet : QuittingAbsorptionWeightedForwardPacket reward carrier
      oldTolerance chargeTarget) (hle : oldTolerance ≤ newTolerance) :
    QuittingAbsorptionWeightedForwardPacket reward carrier
      newTolerance chargeTarget := {
  roots := packet.roots
  value := packet.value
  horizon := packet.horizon
  value_mem := packet.value_mem
  bellman := fun time htime player ↦
    (packet.bellman time htime player).trans
      (mul_le_mul_of_nonneg_right hle
        (quittingRootAbsorptionMass_nonneg _))
  regret := fun time htime player ↦
    (packet.regret time htime player).trans
      (mul_le_mul_of_nonneg_right hle
        (quittingRootAbsorptionMass_nonneg _))
  rational := fun target time htime ↦ by
    have := packet.rational target time htime
    linarith
  chargeTarget_le := packet.chargeTarget_le }

/-- Exact packets in one fixed box yield weighted packets in the single
enlarged box with radius `B+2`, independently of tolerance and charge. -/
theorem hasAbsorptionWeightedFiniteForwardPackets_of_exact
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (B : ℝ) (hexact : HasExactFiniteForwardPackets reward B) :
    HasAbsorptionWeightedFiniteForwardPackets reward (B + 2) := by
  intro tolerance htolerance chargeTarget hcharge
  let δ := min 1 (tolerance / 3)
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos htolerance (by norm_num))
  have hδmax : δ ≤ 1 := min_le_left _ _
  have hthree : 3 * δ ≤ tolerance := by
    have := min_le_right 1 (tolerance / 3)
    dsimp only [δ]
    linarith
  obtain ⟨packet⟩ := hexact δ hδ chargeTarget hcharge
  exact ⟨(packet.upwardTranslate hδ hδmax).weakenTolerance hthree⟩

/-- Under one reward bound, existence of exact finite packets in some fixed
box is equivalent to existence of absorption-weighted packets in some fixed
box.  The box is selected before either accuracy or requested charge. -/
theorem exists_exactFiniteForwardPacketBox_iff_exists_absorptionWeightedBox
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (rewardBound : ℝ) (hbound : 0 < rewardBound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound) :
    (∃ B, rewardBound ≤ B ∧ HasExactFiniteForwardPackets reward B) ↔
      ∃ B, rewardBound ≤ B ∧
        HasAbsorptionWeightedFiniteForwardPackets reward B := by
  constructor
  · rintro ⟨B, hB, hexact⟩
    refine ⟨B + 2, by linarith,
      hasAbsorptionWeightedFiniteForwardPackets_of_exact reward B hexact⟩
  · rintro ⟨B, hB, hweighted⟩
    have hBpos : 0 < B := hbound.trans_le hB
    exact ⟨B, hB, hasExactFiniteForwardPackets_of_absorptionWeighted
      reward B hBpos (fun terminal player ↦
        (hreward terminal player).trans hB) hweighted⟩

/-- Exact packets in the supplied reward box exist at every accuracy and
charge iff absorption-weighted packets exist in some one box fixed before
accuracy and charge. -/
theorem hasExactFiniteForwardPackets_rewardBox_iff_exists_absorptionWeightedBox
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (rewardBound : ℝ) (hbound : 0 < rewardBound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound) :
    HasExactFiniteForwardPackets reward rewardBound ↔
      ∃ B, rewardBound ≤ B ∧
        HasAbsorptionWeightedFiniteForwardPackets reward B := by
  constructor
  · intro hexact
    exact (exists_exactFiniteForwardPacketBox_iff_exists_absorptionWeightedBox
      reward rewardBound hbound hreward).mp ⟨rewardBound, le_rfl, hexact⟩
  · intro hweighted
    obtain ⟨B, hB, hexact⟩ :=
      (exists_exactFiniteForwardPacketBox_iff_exists_absorptionWeightedBox
        reward rewardBound hbound hreward).mpr hweighted
    exact hasExactFiniteForwardPackets_rewardBox_of_box reward hB hreward hexact

end GameTheory

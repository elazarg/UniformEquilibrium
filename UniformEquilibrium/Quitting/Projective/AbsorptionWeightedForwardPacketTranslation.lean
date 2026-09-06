import UniformEquilibrium.Quitting.Projective.AbsorptionWeightedForwardPacketProducer
import UniformEquilibrium.Quitting.Projective.FiniteForwardPacketRewardBoxReduction
import UniformEquilibrium.Quitting.Root.TerminalDebtPrefix

/-! # Upward translation from exact to absorption-weighted packets -/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Common upward translation of a payoff annotation. -/
def quittingPayoffUpwardTranslate (tail : Payoff ι) (δ : ℝ) : Payoff ι :=
  fun who ↦ tail who + 2 * δ

private theorem endpointDifference_upwardTranslate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) (δ : ℝ) :
    quittingRootEndpointDifference reward (quittingPayoffUpwardTranslate tail δ)
        root who =
      quittingRootEndpointDifference reward tail root who -
        2 * δ * quittingRootOpponentContinueMass root who := by
  unfold quittingRootEndpointDifference
  rw [quittingRootQuitPayoff_continuation_invariant reward
    (quittingPayoffUpwardTranslate tail δ) tail root who]
  have hcongr : quittingRootContinuePayoff reward
      (quittingPayoffUpwardTranslate tail δ) root who =
      quittingRootContinuePayoff reward
        (Function.update tail who (tail who + 2 * δ)) root who := by
    apply quittingRootExpectedPayoff_continuation_congr
    simp [quittingPayoffUpwardTranslate]
  rw [hcongr, quittingRootContinuePayoff_update_add]
  ring

/-- Upward translation turns support-local δ-Nash into ordinary mixed-root
regret bounded by three times δ times row absorption. -/
theorem coordinateNashDefect_upwardTranslate_le_absorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) {δ : ℝ}
    (hδ : 0 < δ)
    (hsupport : IsQuittingRootSupportApproxNash reward tail δ root) :
    quittingRootCoordinateNashDefect reward
        (quittingPayoffUpwardTranslate tail δ) root who ≤
      3 * δ * quittingRootAbsorptionMass root := by
  rw [quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart]
  rw [endpointDifference_upwardTranslate]
  let difference := quittingRootEndpointDifference reward tail root who
  let opponentMass := quittingRootOpponentContinueMass root who
  let quitProbability := (root who true).toReal
  let continueProbability := (root who false).toReal
  have hq0 : 0 ≤ quitProbability := ENNReal.toReal_nonneg
  have hc0 : 0 ≤ continueProbability := ENNReal.toReal_nonneg
  have hm0 : 0 ≤ opponentMass := quittingRootOpponentContinueMass_nonneg root who
  have hm1 : opponentMass ≤ 1 := quittingRootOpponentContinueMass_le_one root who
  have hqAbs : quitProbability ≤ quittingRootAbsorptionMass root :=
    quittingQuitProbability_le_absorptionMass root who
  by_cases hshift : 0 ≤ difference - 2 * δ * opponentMass
  · rw [max_eq_left hshift, max_eq_right (by linarith : -(difference -
        2 * δ * opponentMass) ≤ 0), mul_zero, add_zero]
    change continueProbability * (difference - 2 * δ * opponentMass) ≤ _
    by_cases hzeroShift : difference - 2 * δ * opponentMass = 0
    · rw [hzeroShift, mul_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) hδ.le)
        (quittingRootAbsorptionMass_nonneg root)
    by_cases hc : continueProbability = 0
    · rw [hc, zero_mul]
      exact mul_nonneg (mul_nonneg (by norm_num) hδ.le)
        (quittingRootAbsorptionMass_nonneg root)
    · have hcpos : 0 < continueProbability :=
        lt_of_le_of_ne hc0 (Ne.symm hc)
      have hold : difference ≤ δ := (hsupport who).2 hcpos
      have hmhalf : opponentMass < 1 / 2 := by
        have hshiftPos : 0 < difference - 2 * δ * opponentMass :=
          lt_of_le_of_ne hshift (Ne.symm hzeroShift)
        nlinarith
      have haHalf : 1 / 2 < quittingRootAbsorptionMass root := by
        dsimp only [opponentMass] at hmhalf
        rw [quittingRootOpponentContinueMass_eq_one_sub_absorptionMass] at hmhalf
        have hopponent := quittingRootOpponentAbsorptionMass_le_absorptionMass root who
        linarith
      have hc1 : continueProbability ≤ 1 := by
        linarith [quittingRoot_continueProbability_add_quitProbability root who]
      nlinarith
  · have hshift' : difference - 2 * δ * opponentMass ≤ 0 := le_of_not_ge hshift
    rw [max_eq_right hshift', max_eq_left (by linarith :
      0 ≤ -(difference - 2 * δ * opponentMass))]
    change continueProbability * 0 +
      quitProbability * (-(difference - 2 * δ * opponentMass)) ≤ _
    rw [mul_zero, zero_add]
    by_cases hq : quitProbability = 0
    · rw [hq, zero_mul]
      exact mul_nonneg (mul_nonneg (by norm_num) hδ.le)
        (quittingRootAbsorptionMass_nonneg root)
    · have hqpos : 0 < quitProbability := lt_of_le_of_ne hq0 (Ne.symm hq)
      have hold : -δ ≤ difference := (hsupport who).1 hqpos
      have hgap : -(difference - 2 * δ * opponentMass) ≤ 3 * δ := by
        nlinarith
      calc
        quitProbability * (-(difference - 2 * δ * opponentMass)) ≤
            quitProbability * (3 * δ) :=
          mul_le_mul_of_nonneg_left hgap hq0
        _ ≤ quittingRootAbsorptionMass root * (3 * δ) :=
          mul_le_mul_of_nonneg_right hqAbs (by positivity)
        _ = _ := by ring

omit [DecidableEq ι] in
/-- Translating every payoff coordinate upward by `2 * δ` creates exactly
`2 * δ` times the current absorption mass as the Bellman residual. -/
theorem quittingPayoffUpwardTranslate_sub_successor_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current next : Payoff ι) (root : ι → PMF Bool) (who : ι) (δ : ℝ)
    (hpolicy : next who = quittingRootSuccessorPayoff reward current root who) :
    quittingPayoffUpwardTranslate next δ who -
        quittingRootSuccessorPayoff reward
          (quittingPayoffUpwardTranslate current δ) root who =
      2 * δ * quittingRootAbsorptionMass root := by
  have htail := quittingRootSuccessorPayoff_sub_eq_continueMass_mul
    reward (quittingPayoffUpwardTranslate current δ) current root who
  dsimp only [quittingPayoffUpwardTranslate] at hpolicy htail ⊢
  have hc := quittingStationaryContinueMass_nonneg root
  have hc1 := quittingStationaryContinueMass_le_one root
  unfold quittingRootAbsorptionMass
  nlinarith

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

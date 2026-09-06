import UniformEquilibrium.Quitting.Projective.AbsorptionWeightedForwardPacketProducer
import UniformEquilibrium.Quitting.Root.BoundedEndpoint
import MathUE.DivergentChargeRecurrence

/-! # Reduction of exact finite forward packets to the reward box -/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Coordinatewise projection onto the symmetric interval `[-bound, bound]`. -/
def quittingPayoffClip (bound : ℝ) (value : Payoff ι) : Payoff ι :=
  fun player ↦ max (-bound) (min bound (value player))

omit [Fintype ι] [DecidableEq ι] in
theorem abs_quittingPayoffClip_le {bound : ℝ} (hbound : 0 ≤ bound)
    (value : Payoff ι) (player : ι) :
    |quittingPayoffClip bound value player| ≤ bound := by
  simp only [quittingPayoffClip]
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

omit [Fintype ι] [DecidableEq ι] in
theorem abs_quittingPayoffClip_sub_le {small large : ℝ}
    (hsmall : 0 ≤ small) (hlarge : small ≤ large)
    (value : Payoff ι) (hvalue : ∀ player, |value player| ≤ large)
    (player : ι) :
    |quittingPayoffClip small value player - value player| ≤ large - small := by
  have hv := hvalue player
  rw [abs_le] at hv ⊢
  simp only [quittingPayoffClip, min_def, max_def]
  split <;> split <;> constructor <;> linarith

omit [DecidableEq ι] in
/-- One exact Bellman step contracts coordinate excess above a reward box by
the root's all-Continue mass. -/
theorem abs_quittingRootSuccessorPayoff_le_rewardBox_add_continue_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (player : ι)
    {bound excess : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (htail : |tail player| ≤ bound + excess) :
    |quittingRootSuccessorPayoff reward tail root player| ≤
      bound + quittingStationaryContinueMass root * excess := by
  unfold quittingRootSuccessorPayoff
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add]
  calc
    |quittingRootAbsorbingContribution reward root player +
        quittingStationaryContinueMass root * tail player| ≤
        |quittingRootAbsorbingContribution reward root player| +
          |quittingStationaryContinueMass root * tail player| := abs_add_le _ _
    _ ≤ bound * quittingRootAbsorptionMass root +
          quittingStationaryContinueMass root * (bound + excess) := by
      apply add_le_add
      · exact abs_quittingRootAbsorbingContribution_le reward root player bound hreward
      · rw [abs_mul, abs_of_nonneg (quittingStationaryContinueMass_nonneg root)]
        exact mul_le_mul_of_nonneg_left htail
          (quittingStationaryContinueMass_nonneg root)
    _ = bound + quittingStationaryContinueMass root * excess := by
      unfold quittingRootAbsorptionMass
      ring

/-- Along an exact packet, excess over the reward box contracts by the
product of the preceding all-Continue masses. -/
theorem QuittingFiniteForwardPacket.abs_value_le_rewardBox_add_survival_excess
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {large supportError chargeTarget : ℝ}
    (packet : QuittingFiniteForwardPacket reward
      (quittingForwardPacketCoordinateBox large) supportError chargeTarget)
    {bound : ℝ} (hlarge : bound ≤ large)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (time : ℕ) (htime : time ≤ packet.horizon) (player : Fin 4) :
    |packet.value time player| ≤ bound + (large - bound) *
      ∏ offset ∈ Finset.range time,
        quittingStationaryContinueMass (packet.roots offset) := by
  induction time with
  | zero =>
      have hvalue := packet.value_mem 0 (Nat.zero_le _) player
      have hexcess : 0 ≤ large - bound := sub_nonneg.mpr hlarge
      simp only [Finset.prod_range_zero]
      nlinarith
  | succ time ih =>
      have hlt : time < packet.horizon := Nat.lt_of_succ_le htime
      rw [congrFun (packet.policy time hlt) player, Finset.prod_range_succ]
      have hstep := abs_quittingRootSuccessorPayoff_le_rewardBox_add_continue_mul
        reward (packet.value time) (packet.roots time) player hreward
          (ih (Nat.le_of_lt hlt))
      have hc := quittingStationaryContinueMass_nonneg (packet.roots time)
      nlinarith

/-- The survival product of a finite packet is controlled by its accumulated
absorption charge through the elementary reciprocal bound. -/
theorem quittingFiniteForwardPacket_survival_mul_one_add_charge_le_one
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {carrier : Set (Payoff (Fin 4))} {supportError chargeTarget : ℝ}
    (packet : QuittingFiniteForwardPacket reward carrier supportError chargeTarget)
    (time : ℕ) :
    (∏ offset ∈ Finset.range time,
        quittingStationaryContinueMass (packet.roots offset)) *
      (1 + ∑ offset ∈ Finset.range time,
        quittingRootAbsorptionMass (packet.roots offset)) ≤ 1 := by
  convert Math.prod_one_sub_mul_one_add_sum_range_le_one
      (fun offset ↦ quittingRootAbsorptionMass (packet.roots offset))
      (fun offset ↦ quittingRootAbsorptionMass_nonneg (packet.roots offset))
      (fun offset ↦ by
        unfold quittingRootAbsorptionMass
        linarith [quittingStationaryContinueMass_nonneg (packet.roots offset)])
      0 time using 1
  all_goals simp only [quittingRootAbsorptionMass, zero_add, sub_sub_cancel]

/-- Exact forward recomputation of a retained suffix from one clipped boundary
value. -/
def QuittingFiniteForwardPacket.clippedSuffixValue
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {carrier : Set (Payoff (Fin 4))} {supportError chargeTarget : ℝ}
    (packet : QuittingFiniteForwardPacket reward carrier supportError chargeTarget)
    (bound : ℝ) (cut : ℕ) : ℕ → Payoff (Fin 4)
  | 0 => quittingPayoffClip bound (packet.value cut)
  | time + 1 => quittingRootSuccessorPayoff reward
      (packet.clippedSuffixValue bound cut time) (packet.roots (cut + time))

@[simp] theorem QuittingFiniteForwardPacket.clippedSuffixValue_zero
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {carrier : Set (Payoff (Fin 4))} {supportError chargeTarget : ℝ}
    (packet : QuittingFiniteForwardPacket reward carrier supportError chargeTarget)
    (bound : ℝ) (cut : ℕ) :
    packet.clippedSuffixValue bound cut 0 =
      quittingPayoffClip bound (packet.value cut) := rfl

@[simp] theorem QuittingFiniteForwardPacket.clippedSuffixValue_succ
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {carrier : Set (Payoff (Fin 4))} {supportError chargeTarget : ℝ}
    (packet : QuittingFiniteForwardPacket reward carrier supportError chargeTarget)
    (bound : ℝ) (cut time : ℕ) :
    packet.clippedSuffixValue bound cut (time + 1) =
      quittingRootSuccessorPayoff reward
        (packet.clippedSuffixValue bound cut time) (packet.roots (cut + time)) := rfl

/-- Recomputed suffix values remain in the reward box. -/
theorem QuittingFiniteForwardPacket.clippedSuffixValue_mem
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {carrier : Set (Payoff (Fin 4))} {supportError chargeTarget : ℝ}
    (packet : QuittingFiniteForwardPacket reward carrier supportError chargeTarget)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (cut time : ℕ) :
    packet.clippedSuffixValue bound cut time ∈
      quittingForwardPacketCoordinateBox bound := by
  induction time with
  | zero => exact fun player ↦ abs_quittingPayoffClip_le hbound _ player
  | succ time ih =>
      intro player
      rw [packet.clippedSuffixValue_succ]
      simpa using abs_quittingRootSuccessorPayoff_le_rewardBox_add_continue_mul
        reward (packet.clippedSuffixValue bound cut time)
          (packet.roots (cut + time)) player (excess := 0) hreward (by simpa using ih player)

/-- Recomputing a suffix from a nearby boundary value never amplifies its
coordinate error. -/
theorem QuittingFiniteForwardPacket.abs_clippedSuffixValue_sub_original_le
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {carrier : Set (Payoff (Fin 4))} {supportError chargeTarget error : ℝ}
    (packet : QuittingFiniteForwardPacket reward carrier supportError chargeTarget)
    {bound : ℝ} {cut time : ℕ} (hcut : cut + time ≤ packet.horizon)
    (hboundary : ∀ player,
      |quittingPayoffClip bound (packet.value cut) player -
        packet.value cut player| ≤ error)
    (player : Fin 4) :
    |packet.clippedSuffixValue bound cut time player -
        packet.value (cut + time) player| ≤ error := by
  induction time with
  | zero => simpa using hboundary player
  | succ time ih =>
      have hrow : cut + time < packet.horizon := by omega
      rw [packet.clippedSuffixValue_succ]
      rw [show cut + (time + 1) = cut + time + 1 by omega,
        congrFun (packet.policy (cut + time) hrow) player]
      have hexact := quittingRootSuccessorPayoff_sub_eq_continueMass_mul
        reward (packet.clippedSuffixValue bound cut time)
          (packet.value (cut + time)) (packet.roots (cut + time)) player
      rw [hexact, abs_mul,
        abs_of_nonneg (quittingStationaryContinueMass_nonneg _)]
      calc
        quittingStationaryContinueMass (packet.roots (cut + time)) *
            |packet.clippedSuffixValue bound cut time player -
              packet.value (cut + time) player| ≤
            1 * |packet.clippedSuffixValue bound cut time player -
              packet.value (cut + time) player| :=
          mul_le_mul_of_nonneg_right
            (quittingStationaryContinueMass_le_one _) (abs_nonneg _)
        _ ≤ error := by simpa using ih (by omega)

/-- Clip at a selected charge crossing, retain the roots after the crossing,
and recompute an exact packet in the reward box. -/
def QuittingFiniteForwardPacket.clipSuffix
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {carrier : Set (Payoff (Fin 4))} {oldError oldCharge requested bound error : ℝ}
    (packet : QuittingFiniteForwardPacket reward carrier oldError oldCharge)
    (cut : ℕ) (hcut : cut ≤ packet.horizon)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hboundary : ∀ player,
      |quittingPayoffClip bound (packet.value cut) player -
        packet.value cut player| ≤ error)
    (hsuffixCharge : requested ≤ ∑ time ∈ Finset.Ico cut packet.horizon,
      quittingRootAbsorptionMass (packet.roots time)) :
    QuittingFiniteForwardPacket reward
      (quittingForwardPacketCoordinateBox bound) (oldError + error) requested := {
  roots := fun time => packet.roots (cut + time)
  value := packet.clippedSuffixValue bound cut
  horizon := packet.horizon - cut
  value_mem := fun time _ => packet.clippedSuffixValue_mem
    ((abs_nonneg _).trans (hreward ⟨{0}, by simp⟩ 0)) hreward cut time
  policy := fun _ _ => rfl
  support := by
    intro time htime
    have horiginal := packet.support (cut + time) (by omega)
    exact isQuittingRootSupportApproxNash_of_tail_close reward
      (packet.roots (cut + time)) (packet.value (cut + time))
      (packet.clippedSuffixValue bound cut time) horiginal
        (fun player => packet.abs_clippedSuffixValue_sub_original_le
          (time := time) (by omega) hboundary player)
  rational := by
    intro target time htime
    have horiginal := packet.rational target (cut + time) (by omega)
    have hclose := packet.abs_clippedSuffixValue_sub_original_le
      (time := time) (by omega) hboundary target
    rw [abs_le] at hclose
    linarith
  chargeTarget_le := by
    simpa only [Finset.sum_Ico_eq_sum_range] using hsuffixCharge }

/-- Exact packets in any fixed bounding box reduce to exact packets in the
reward box itself.  This proof requests the original packet with the explicit
rational charge overhead `(large - rewardBound) / (supportError / 2) + 1`;
it does not assert the sharper logarithmic overhead. -/
theorem hasExactFiniteForwardPackets_rewardBox_of_box
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {rewardBound large : ℝ} (hlarge : rewardBound ≤ large)
    (hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound)
    (hexact : HasExactFiniteForwardPackets reward large) :
    HasExactFiniteForwardPackets reward rewardBound := by
  have hrewardBound : 0 ≤ rewardBound :=
    (abs_nonneg _).trans (hreward ⟨{0}, by simp⟩ 0)
  intro supportError herror requested hrequested
  let halfError := supportError / 2
  let excess := large - rewardBound
  let threshold := excess / halfError
  have hhalf : 0 < halfError := div_pos herror (by norm_num)
  have hexcess : 0 ≤ excess := sub_nonneg.mpr hlarge
  have hthreshold : 0 ≤ threshold := div_nonneg hexcess hhalf.le
  have htotalTarget : 0 ≤ requested + threshold + 1 := by positivity
  obtain ⟨packet⟩ := hexact halfError hhalf
    (requested + threshold + 1) htotalTarget
  obtain ⟨cut, hcut, hcrossed, hprefixUpper, hsuffix⟩ :=
    Math.exists_firstFiniteChargeCrossing
      (fun time ↦ quittingRootAbsorptionMass (packet.roots time))
      (fun time ↦ by
        unfold quittingRootAbsorptionMass
        linarith [quittingStationaryContinueMass_nonneg (packet.roots time)])
      hthreshold hrequested packet.chargeTarget_le
  let survival := ∏ time ∈ Finset.range cut,
    quittingStationaryContinueMass (packet.roots time)
  let prefixCharge := ∑ time ∈ Finset.range cut,
    quittingRootAbsorptionMass (packet.roots time)
  have hsurvival0 : 0 ≤ survival := Finset.prod_nonneg fun time _ ↦
    quittingStationaryContinueMass_nonneg (packet.roots time)
  have hproduct : survival * (1 + prefixCharge) ≤ 1 :=
    quittingFiniteForwardPacket_survival_mul_one_add_charge_le_one packet cut
  have hexcessLe : excess ≤ halfError * prefixCharge := by
    have := mul_le_mul_of_nonneg_left hcrossed hhalf.le
    dsimp only [threshold] at this
    field_simp [ne_of_gt hhalf] at this
    simpa [mul_comm] using this
  have hsurvivalExcess : excess * survival ≤ halfError := by
    have hprefix0 : 0 ≤ prefixCharge := Finset.sum_nonneg fun time _ ↦
      quittingRootAbsorptionMass_nonneg (packet.roots time)
    have hmul := mul_le_mul_of_nonneg_right hexcessLe hsurvival0
    nlinarith
  have hvalueBound (player : Fin 4) :
      |packet.value cut player| ≤ rewardBound + excess * survival := by
    simpa only [excess, survival] using
      packet.abs_value_le_rewardBox_add_survival_excess hlarge hreward cut hcut player
  have hboundary (player : Fin 4) :
      |quittingPayoffClip rewardBound (packet.value cut) player -
          packet.value cut player| ≤ halfError := by
    exact (abs_quittingPayoffClip_sub_le hrewardBound
      (le_add_of_nonneg_right (mul_nonneg hexcess hsurvival0))
      (packet.value cut) hvalueBound player).trans (by
        simpa using hsurvivalExcess)
  have hsum : halfError + halfError = supportError := by
    dsimp only [halfError]
    ring
  rw [← hsum]
  exact ⟨packet.clipSuffix cut hcut hreward hboundary hsuffix⟩

end GameTheory

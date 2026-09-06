import UniformEquilibrium.Quitting.Projective.AbsorptionWeightedForwardPacket
import UniformEquilibrium.Quitting.Root.AbsorptionWeightedRootPurification
import UniformEquilibrium.Quitting.Root.EndpointOpponentStability
import UniformEquilibrium.Quitting.Projective.FiniteForwardProjectiveLasso
import UniformEquilibrium.Quitting.Projective.Lasso

/-! # Exact finite repair of absorption-weighted forward packets -/

noncomputable section

namespace GameTheory

open Math.Probability

/-- The coordinate box used by the exact repaired packet. -/
def quittingForwardPacketCoordinateBox (B : ℝ) : Set (Payoff (Fin 4)) :=
  {value | ∀ player, |value player| ≤ B}

private theorem abs_quittingRootSuccessorPayoff_le_bound
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (tail : Payoff (Fin 4)) (root : Fin 4 → PMF Bool) (player : Fin 4)
    {B : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ B)
    (htail : ∀ who, |tail who| ≤ B) :
    |quittingRootSuccessorPayoff reward tail root player| ≤ B := by
  unfold quittingRootSuccessorPayoff quittingRootExpectedPayoff
  apply abs_expect_le_of_abs_le
  intro action
  exact abs_quittingRootPayoff_le reward tail hreward htail action player

/-- Purify every packet row using its original annotation and threshold `Bρ`. -/
def QuittingAbsorptionWeightedForwardPacket.purifiedRoots
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {carrier : Set (Payoff (Fin 4))} {tolerance chargeTarget : ℝ}
    (packet : QuittingAbsorptionWeightedForwardPacket reward carrier
      tolerance chargeTarget) (B ρ : ℝ) (time : ℕ) : Fin 4 → PMF Bool :=
  quittingSupportPurifiedRoot reward (packet.value time) (B * ρ) (packet.roots time)

/-- Recompute the repaired annotations exactly forward, retaining the original
first annotation. -/
def QuittingAbsorptionWeightedForwardPacket.repairedValue
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {carrier : Set (Payoff (Fin 4))} {tolerance chargeTarget : ℝ}
    (packet : QuittingAbsorptionWeightedForwardPacket reward carrier
      tolerance chargeTarget) (B ρ : ℝ) : ℕ → Payoff (Fin 4)
  | 0 => packet.value 0
  | time + 1 => quittingRootSuccessorPayoff reward
      (packet.repairedValue B ρ time) (packet.purifiedRoots B ρ time)

@[simp] theorem QuittingAbsorptionWeightedForwardPacket.repairedValue_zero
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {carrier : Set (Payoff (Fin 4))} {tolerance chargeTarget B ρ : ℝ}
    (packet : QuittingAbsorptionWeightedForwardPacket reward carrier
      tolerance chargeTarget) :
    packet.repairedValue B ρ 0 = packet.value 0 := rfl

theorem QuittingAbsorptionWeightedForwardPacket.repairedValue_succ
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {carrier : Set (Payoff (Fin 4))} {tolerance chargeTarget B ρ : ℝ}
    (packet : QuittingAbsorptionWeightedForwardPacket reward carrier
      tolerance chargeTarget) (time : ℕ) :
    packet.repairedValue B ρ (time + 1) =
      quittingRootSuccessorPayoff reward
        (packet.repairedValue B ρ time)
        (packet.purifiedRoots B ρ time) := rfl

/-- The local recurrence behind the length-independent repair bound. -/
theorem absorptionWeightedRepair_oneStep_error_le
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (oldValue repairedValue nextValue : Payoff (Fin 4))
    (root : Fin 4 → PMF Bool) {B ρ e : ℝ}
    (hB : 0 < B) (hρ : 0 < ρ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ B)
    (hold : ∀ player, |oldValue player| ≤ B)
    (hcurrent : ∀ player, |repairedValue player - oldValue player| ≤ e)
    (hbellman : ∀ player,
      |nextValue player - quittingRootSuccessorPayoff reward oldValue root player| ≤
        B * ρ ^ 2 * quittingRootAbsorptionMass root)
    (hregret : ∀ player,
      quittingRootCoordinateNashDefect reward oldValue root player ≤
        B * ρ ^ 2 * quittingRootAbsorptionMass root) :
    ∀ player,
      |quittingRootSuccessorPayoff reward repairedValue
          (quittingSupportPurifiedRoot reward oldValue (B * ρ) root) player -
        nextValue player| ≤
      quittingStationaryContinueMass
          (quittingSupportPurifiedRoot reward oldValue (B * ρ) root) * e +
        B * (ρ ^ 2 + 8 * ρ) * quittingRootAbsorptionMass root := by
  let purified := quittingSupportPurifiedRoot reward oldValue (B * ρ) root
  have hclose := supportPurifiedRoot_coordinate_close_of_weighted_regret
    reward oldValue root hB hρ hregret
  intro player
  have htail := quittingRootSuccessorPayoff_sub_eq_continueMass_mul
    reward repairedValue oldValue purified player
  have htailAbs :
      |quittingRootSuccessorPayoff reward repairedValue purified player -
        quittingRootSuccessorPayoff reward oldValue purified player| ≤
        quittingStationaryContinueMass purified * e := by
    rw [htail, abs_mul, abs_of_nonneg (quittingStationaryContinueMass_nonneg purified)]
    exact mul_le_mul_of_nonneg_left (hcurrent player)
      (quittingStationaryContinueMass_nonneg purified)
  have hroot := abs_quittingRootSuccessorPayoff_sub_of_quitProbability_close
    reward oldValue purified root player hreward hold hclose
  have htriangle := abs_sub_le
    (quittingRootSuccessorPayoff reward repairedValue purified player)
    (quittingRootSuccessorPayoff reward oldValue purified player)
    (quittingRootSuccessorPayoff reward oldValue root player)
  have htriangle' := abs_sub_le
    (quittingRootSuccessorPayoff reward repairedValue purified player)
    (quittingRootSuccessorPayoff reward oldValue root player)
    (nextValue player)
  have ha := quittingRootAbsorptionMass_nonneg root
  have hρ0 := hρ.le
  have hroot' :
      |quittingRootSuccessorPayoff reward oldValue purified player -
        quittingRootSuccessorPayoff reward oldValue root player| ≤
        8 * B * ρ * quittingRootAbsorptionMass root := by
    have hcard : (Fintype.card (Fin 4) : ℝ) = 4 := by norm_num
    rw [hcard] at hroot
    convert hroot using 1
    ring_nf
  calc
    _ ≤ |quittingRootSuccessorPayoff reward repairedValue purified player -
          quittingRootSuccessorPayoff reward oldValue purified player| +
        |quittingRootSuccessorPayoff reward oldValue purified player -
          quittingRootSuccessorPayoff reward oldValue root player| +
        |quittingRootSuccessorPayoff reward oldValue root player - nextValue player| := by
      exact htriangle'.trans (add_le_add htriangle le_rfl)
    _ ≤ quittingStationaryContinueMass purified * e +
        8 * B * ρ * quittingRootAbsorptionMass root +
        B * ρ ^ 2 * quittingRootAbsorptionMass root := by
      exact add_le_add (add_le_add htailAbs hroot') (by simpa [abs_sub_comm] using hbellman player)
    _ = _ := by ring

/-- Exact forward recomputation remains uniformly within `17Bρ` of every
used annotation, independently of packet length. -/
theorem QuittingAbsorptionWeightedForwardPacket.repairedValue_close
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {carrier : Set (Payoff (Fin 4))} {chargeTarget B ρ : ℝ}
    (packet : QuittingAbsorptionWeightedForwardPacket reward carrier
      (B * ρ ^ 2) chargeTarget)
    (hB : 0 < B) (hρ : 0 < ρ) (hρmax : ρ ≤ 1 / 8)
    (hreward : ∀ terminal player, |reward terminal player| ≤ B)
    (hcarrier : ∀ value ∈ carrier, ∀ player, |value player| ≤ B) :
    ∀ time, time ≤ packet.horizon → ∀ player,
      |packet.repairedValue B ρ time player - packet.value time player| ≤
        17 * B * ρ := by
  intro time htime
  induction time with
  | zero =>
      intro player
      simpa using mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 17) hB.le) hρ.le
  | succ time ih =>
      have htimeLt : time < packet.horizon := by omega
      have hcurrent := ih (Nat.le_of_succ_le htime)
      have honeStep := absorptionWeightedRepair_oneStep_error_le
        reward (packet.value time) (packet.repairedValue B ρ time)
          (packet.value (time + 1)) (packet.roots time) hB hρ hreward
          (hcarrier _ (packet.value_mem time (Nat.le_of_succ_le htime)))
          hcurrent (packet.bellman time htimeLt) (packet.regret time htimeLt)
      intro player
      rw [packet.repairedValue_succ]
      refine (honeStep player).trans ?_
      have hhalf := finFour_half_absorption_le_supportPurifiedRoot
        reward (packet.value time) (packet.roots time) hB hρ hρmax
          (packet.regret time htimeLt)
      have ha := quittingRootAbsorptionMass_nonneg (packet.roots time)
      have hcontinue := quittingStationaryContinueMass_nonneg
        (packet.purifiedRoots B ρ time)
      change quittingRootAbsorptionMass (packet.roots time) / 2 ≤
        quittingRootAbsorptionMass (packet.purifiedRoots B ρ time) at hhalf
      have hscale := mul_le_mul_of_nonneg_left hhalf
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 17) hB.le) hρ.le)
      dsimp only [QuittingAbsorptionWeightedForwardPacket.purifiedRoots]
        at hscale hcontinue
      unfold quittingRootAbsorptionMass at hhalf
      unfold quittingRootAbsorptionMass at hscale
      have hfactor : ρ ^ 2 + 8 * ρ ≤ 17 * ρ / 2 := by nlinarith
      have hlocal := mul_le_mul_of_nonneg_left hfactor
        (mul_nonneg hB.le ha)
      unfold quittingRootAbsorptionMass at hlocal
      rw [quittingRootAbsorptionMass]
      calc
        _ ≤ quittingStationaryContinueMass
              (quittingSupportPurifiedRoot reward (packet.value time)
                (B * ρ) (packet.roots time)) * (17 * B * ρ) +
            17 * B * ρ *
              ((1 - quittingStationaryContinueMass (packet.roots time)) / 2) := by
          nlinarith
        _ ≤ 17 * B * ρ := by nlinarith

/-- Exact recomputation stays in the same coordinate box. -/
theorem QuittingAbsorptionWeightedForwardPacket.repairedValue_mem_coordinateBox
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {carrier : Set (Payoff (Fin 4))} {tolerance chargeTarget B ρ : ℝ}
    (packet : QuittingAbsorptionWeightedForwardPacket reward carrier
      tolerance chargeTarget)
    (hreward : ∀ terminal player, |reward terminal player| ≤ B)
    (hcarrier : ∀ value ∈ carrier, ∀ player, |value player| ≤ B) :
    ∀ time, time ≤ packet.horizon →
      packet.repairedValue B ρ time ∈ quittingForwardPacketCoordinateBox B := by
  intro time htime
  induction time with
  | zero =>
      exact hcarrier _ (packet.value_mem 0 (Nat.zero_le _))
  | succ time ih =>
      intro player
      rw [packet.repairedValue_succ]
      exact abs_quittingRootSuccessorPayoff_le_bound reward
        (packet.repairedValue B ρ time) (packet.purifiedRoots B ρ time)
        player hreward (ih (Nat.le_of_succ_le htime))

/-- Weighted error at scale B times rho squared becomes an exact forward
packet with error 32 times B times rho, while retaining half the charge. -/
def QuittingAbsorptionWeightedForwardPacket.repair
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {carrier : Set (Payoff (Fin 4))} {chargeTarget B ρ : ℝ}
    (packet : QuittingAbsorptionWeightedForwardPacket reward carrier
      (B * ρ ^ 2) chargeTarget)
    (hB : 0 < B) (hρ : 0 < ρ) (hρmax : ρ ≤ 1 / 8)
    (hreward : ∀ terminal player, |reward terminal player| ≤ B)
    (hcarrier : ∀ value ∈ carrier, ∀ player, |value player| ≤ B) :
    QuittingFiniteForwardPacket reward (quittingForwardPacketCoordinateBox B)
      (32 * B * ρ) (chargeTarget / 2) := {
  roots := packet.purifiedRoots B ρ
  value := packet.repairedValue B ρ
  horizon := packet.horizon
  value_mem := packet.repairedValue_mem_coordinateBox hreward hcarrier
  policy := fun time _ ↦ packet.repairedValue_succ time
  support := by
    intro time htime
    have horiginal :=
      finFour_isSupportApproxNash_supportPurifiedRoot_of_weighted_regret
        reward (packet.value time) (packet.roots time) hB hρ hreward
          (hcarrier _ (packet.value_mem time htime.le))
          (packet.regret time htime)
    have htransfer := isQuittingRootSupportApproxNash_of_tail_close
      reward (packet.purifiedRoots B ρ time) (packet.value time)
        (packet.repairedValue B ρ time) horiginal
        (packet.repairedValue_close hB hρ hρmax hreward hcarrier time htime.le)
    exact fun player ↦ by
      have h := htransfer player
      constructor
      · intro hplayed
        have := h.1 hplayed
        nlinarith [mul_pos hB hρ]
      · intro hplayed
        have := h.2 hplayed
        nlinarith [mul_pos hB hρ]
  rational := by
    intro target time htime
    have hfloor := packet.rational target time htime
    have hclose := packet.repairedValue_close
      hB hρ hρmax hreward hcarrier time htime target
    rw [abs_le] at hclose
    nlinarith [mul_pos hB hρ]
  chargeTarget_le := by
    have hrow : ∀ time ∈ Finset.range packet.horizon,
        quittingRootAbsorptionMass (packet.roots time) / 2 ≤
          quittingRootAbsorptionMass (packet.purifiedRoots B ρ time) := by
      intro time htime
      exact finFour_half_absorption_le_supportPurifiedRoot reward
        (packet.value time) (packet.roots time) hB hρ hρmax
          (packet.regret time (Finset.mem_range.mp htime))
    have hsum := Finset.sum_le_sum hrow
    calc
      chargeTarget / 2 ≤
          (∑ time ∈ Finset.range packet.horizon,
            quittingRootAbsorptionMass (packet.roots time)) / 2 :=
        div_le_div_of_nonneg_right packet.chargeTarget_le (by norm_num)
      _ = ∑ time ∈ Finset.range packet.horizon,
          quittingRootAbsorptionMass (packet.roots time) / 2 := by
        rw [Finset.sum_div]
      _ ≤ _ := hsum }

/-- Every used root of the repaired packet differs coordinatewise from its
input root by at most rho times the input row absorption. -/
theorem QuittingAbsorptionWeightedForwardPacket.repair_root_coordinate_close
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {carrier : Set (Payoff (Fin 4))} {chargeTarget B ρ : ℝ}
    (packet : QuittingAbsorptionWeightedForwardPacket reward carrier
      (B * ρ ^ 2) chargeTarget)
    (hB : 0 < B) (hρ : 0 < ρ) (hρmax : ρ ≤ 1 / 8)
    (hreward : ∀ terminal player, |reward terminal player| ≤ B)
    (hcarrier : ∀ value ∈ carrier, ∀ player, |value player| ≤ B)
    (time : ℕ) (htime : time < packet.horizon) (player : Fin 4) :
    |((packet.repair hB hρ hρmax hreward hcarrier).roots time player true).toReal -
        (packet.roots time player true).toReal| ≤
      ρ * quittingRootAbsorptionMass (packet.roots time) := by
  exact supportPurifiedRoot_coordinate_close_of_weighted_regret
    reward (packet.value time) (packet.roots time) hB hρ
      (packet.regret time htime) player

@[simp] theorem QuittingAbsorptionWeightedForwardPacket.repair_horizon
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {carrier : Set (Payoff (Fin 4))} {chargeTarget B ρ : ℝ}
    (packet : QuittingAbsorptionWeightedForwardPacket reward carrier
      (B * ρ ^ 2) chargeTarget)
    (hB : 0 < B) (hρ : 0 < ρ) (hρmax : ρ ≤ 1 / 8)
    (hreward : ∀ terminal player, |reward terminal player| ≤ B)
    (hcarrier : ∀ value ∈ carrier, ∀ player, |value player| ≤ B) :
    (packet.repair hB hρ hρmax hreward hcarrier).horizon = packet.horizon := rfl

@[simp] theorem QuittingAbsorptionWeightedForwardPacket.repair_value_zero
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {carrier : Set (Payoff (Fin 4))} {chargeTarget B ρ : ℝ}
    (packet : QuittingAbsorptionWeightedForwardPacket reward carrier
      (B * ρ ^ 2) chargeTarget)
    (hB : 0 < B) (hρ : 0 < ρ) (hρmax : ρ ≤ 1 / 8)
    (hreward : ∀ terminal player, |reward terminal player| ≤ B)
    (hcarrier : ∀ value ∈ carrier, ∀ player, |value player| ≤ B) :
    (packet.repair hB hρ hρmax hreward hcarrier).value 0 = packet.value 0 := rfl

/-- The repaired packet value is within `17 * B * ρ` of
the input annotation at every displayed time. -/
theorem QuittingAbsorptionWeightedForwardPacket.repair_value_close
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {carrier : Set (Payoff (Fin 4))} {chargeTarget B ρ : ℝ}
    (packet : QuittingAbsorptionWeightedForwardPacket reward carrier
      (B * ρ ^ 2) chargeTarget)
    (hB : 0 < B) (hρ : 0 < ρ) (hρmax : ρ ≤ 1 / 8)
    (hreward : ∀ terminal player, |reward terminal player| ≤ B)
    (hcarrier : ∀ value ∈ carrier, ∀ player, |value player| ≤ B)
    (time : ℕ) (htime : time ≤ packet.horizon) (player : Fin 4) :
    |(packet.repair hB hρ hρmax hreward hcarrier).value time player -
        packet.value time player| ≤ 17 * B * ρ := by
  exact packet.repairedValue_close hB hρ hρmax hreward hcarrier
    time htime player

/-- Repair retains at least half of the full displayed absorption charge,
not merely half of a requested lower bound. -/
theorem QuittingAbsorptionWeightedForwardPacket.half_total_charge_le_repair_total_charge
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {carrier : Set (Payoff (Fin 4))} {chargeTarget B ρ : ℝ}
    (packet : QuittingAbsorptionWeightedForwardPacket reward carrier
      (B * ρ ^ 2) chargeTarget)
    (hB : 0 < B) (hρ : 0 < ρ) (hρmax : ρ ≤ 1 / 8)
    (hreward : ∀ terminal player, |reward terminal player| ≤ B)
    (hcarrier : ∀ value ∈ carrier, ∀ player, |value player| ≤ B) :
    (∑ time ∈ Finset.range packet.horizon,
        quittingRootAbsorptionMass (packet.roots time)) / 2 ≤
      ∑ time ∈ Finset.range
          (packet.repair hB hρ hρmax hreward hcarrier).horizon,
        quittingRootAbsorptionMass
          ((packet.repair hB hρ hρmax hreward hcarrier).roots time) := by
  rw [packet.repair_horizon hB hρ hρmax hreward hcarrier, Finset.sum_div]
  apply Finset.sum_le_sum
  intro time htime
  exact finFour_half_absorption_le_supportPurifiedRoot reward
    (packet.value time) (packet.roots time) hB hρ hρmax
      (packet.regret time (Finset.mem_range.mp htime))

end GameTheory

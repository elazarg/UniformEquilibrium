/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.FiniteEndpointErrorPunishmentFloor
import UniformEquilibrium.Quitting.Paths.SupportWitnessClockCollapse
import UniformEquilibrium.Quitting.Projective.AbsorptionWeightedForwardPacketProducer

/-! # Floor-free finite forward packets -/

noncomputable section

namespace GameTheory

open Math.Probability

/-- An exact finite forward packet with only its punishment-floor field
removed. -/
structure QuittingFloorFreeFiniteForwardPacket
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (carrier : Set (Payoff (Fin 4)))
    (supportError chargeTarget : ℝ) where
  roots : ℕ → Fin 4 → PMF Bool
  value : ℕ → Payoff (Fin 4)
  horizon : ℕ
  value_mem : ∀ time, time ≤ horizon → value time ∈ carrier
  policy : ∀ time, time < horizon →
    value (time + 1) = quittingRootSuccessorPayoff reward
      (value time) (roots time)
  support : ∀ time, time < horizon →
    IsQuittingRootSupportApproxNash reward
      (value time) supportError (roots time)
  chargeTarget_le : chargeTarget ≤
    ∑ time ∈ Finset.range horizon,
      quittingRootAbsorptionMass (roots time)

/-- An absorption-weighted finite forward packet with only its
punishment-floor field removed. -/
structure QuittingFloorFreeAbsorptionWeightedForwardPacket
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (carrier : Set (Payoff (Fin 4)))
    (tolerance chargeTarget : ℝ) where
  roots : ℕ → Fin 4 → PMF Bool
  value : ℕ → Payoff (Fin 4)
  horizon : ℕ
  value_mem : ∀ time, time ≤ horizon → value time ∈ carrier
  bellman : ∀ time, time < horizon → ∀ player,
    |value (time + 1) player -
        quittingRootSuccessorPayoff reward
          (value time) (roots time) player| ≤
      tolerance * quittingRootAbsorptionMass (roots time)
  regret : ∀ time, time < horizon → ∀ player,
    quittingRootCoordinateNashDefect reward
        (value time) (roots time) player ≤
      tolerance * quittingRootAbsorptionMass (roots time)
  chargeTarget_le : chargeTarget ≤
    ∑ time ∈ Finset.range horizon,
      quittingRootAbsorptionMass (roots time)

/-- Exact floor-free packets of every positive accuracy and nonnegative
charge in one box fixed before both parameters. -/
def HasFloorFreeExactFiniteForwardPackets
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (B : ℝ) : Prop :=
  ∀ supportError, 0 < supportError → ∀ chargeTarget, 0 ≤ chargeTarget →
    Nonempty (QuittingFloorFreeFiniteForwardPacket reward
      (quittingForwardPacketCoordinateBox B) supportError chargeTarget)

/-- Weighted floor-free packets of every positive tolerance and nonnegative
charge in one box fixed before both parameters. -/
def HasFloorFreeAbsorptionWeightedFiniteForwardPackets
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (B : ℝ) : Prop :=
  ∀ tolerance, 0 < tolerance → ∀ chargeTarget, 0 ≤ chargeTarget →
    Nonempty (QuittingFloorFreeAbsorptionWeightedForwardPacket reward
      (quittingForwardPacketCoordinateBox B) tolerance chargeTarget)

/-- Forget the punishment floors of an exact packet. -/
def QuittingFiniteForwardPacket.forgetPunishmentFloor
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {carrier : Set (Payoff (Fin 4))} {supportError chargeTarget : ℝ}
    (packet : QuittingFiniteForwardPacket reward carrier supportError chargeTarget) :
    QuittingFloorFreeFiniteForwardPacket reward carrier
      supportError chargeTarget := {
  roots := packet.roots
  value := packet.value
  horizon := packet.horizon
  value_mem := packet.value_mem
  policy := packet.policy
  support := packet.support
  chargeTarget_le := packet.chargeTarget_le }

/-- Forget the punishment floors of a weighted packet. -/
def QuittingAbsorptionWeightedForwardPacket.forgetPunishmentFloor
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {carrier : Set (Payoff (Fin 4))} {tolerance chargeTarget : ℝ}
    (packet : QuittingAbsorptionWeightedForwardPacket reward carrier
      tolerance chargeTarget) :
    QuittingFloorFreeAbsorptionWeightedForwardPacket reward carrier
      tolerance chargeTarget := {
  roots := packet.roots
  value := packet.value
  horizon := packet.horizon
  value_mem := packet.value_mem
  bellman := packet.bellman
  regret := packet.regret
  chargeTarget_le := packet.chargeTarget_le }

/-- Delete initial construction rows from an exact floor-free packet once
the retained endpoint floors and suffix charge have been proved. -/
def QuittingFloorFreeFiniteForwardPacket.dropInitialRows
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {carrier : Set (Payoff (Fin 4))}
    {oldError newError oldCharge requested : ℝ}
    (packet : QuittingFloorFreeFiniteForwardPacket reward carrier
      oldError oldCharge)
    (cut : ℕ) (hcut : cut ≤ packet.horizon) (herror : oldError ≤ newError)
    (hfloor : ∀ time, cut ≤ time → time ≤ packet.horizon → ∀ player,
      quittingPunishmentValue reward player - newError ≤
        packet.value time player)
    (hcharge : requested ≤
      ∑ time ∈ Finset.Ico cut packet.horizon,
        quittingRootAbsorptionMass (packet.roots time)) :
    QuittingFiniteForwardPacket reward carrier newError requested := {
  roots := fun time => packet.roots (cut + time)
  value := fun time => packet.value (cut + time)
  horizon := packet.horizon - cut
  value_mem := fun time htime => packet.value_mem _ (by omega)
  policy := by
    intro time htime
    simpa only [Nat.add_assoc] using packet.policy (cut + time) (by omega)
  support := by
    intro time htime player
    obtain ⟨hquit, hcontinue⟩ := packet.support (cut + time) (by omega) player
    exact ⟨fun hplayed => by linarith [hquit hplayed],
      fun hplayed => by linarith [hcontinue hplayed]⟩
  rational := fun player time htime => hfloor _ (by omega) (by omega) player
  chargeTarget_le := by
    simpa only [Finset.sum_Ico_eq_sum_range] using hcharge }

/-- Delete initial construction rows from a weighted floor-free packet once
the retained endpoint floors and suffix charge have been proved. -/
def QuittingFloorFreeAbsorptionWeightedForwardPacket.dropInitialRows
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {carrier : Set (Payoff (Fin 4))}
    {oldTolerance newTolerance oldCharge requested : ℝ}
    (packet : QuittingFloorFreeAbsorptionWeightedForwardPacket reward carrier
      oldTolerance oldCharge)
    (cut : ℕ) (hcut : cut ≤ packet.horizon)
    (htolerance : oldTolerance ≤ newTolerance)
    (hfloor : ∀ time, cut ≤ time → time ≤ packet.horizon → ∀ player,
      quittingPunishmentValue reward player - newTolerance ≤
        packet.value time player)
    (hcharge : requested ≤
      ∑ time ∈ Finset.Ico cut packet.horizon,
        quittingRootAbsorptionMass (packet.roots time)) :
    QuittingAbsorptionWeightedForwardPacket reward carrier
      newTolerance requested := {
  roots := fun time => packet.roots (cut + time)
  value := fun time => packet.value (cut + time)
  horizon := packet.horizon - cut
  value_mem := fun time htime => packet.value_mem _ (by omega)
  bellman := by
    intro time htime player
    exact (packet.bellman (cut + time) (by omega) player).trans
      (mul_le_mul_of_nonneg_right htolerance
        (quittingRootAbsorptionMass_nonneg _))
  regret := by
    intro time htime player
    exact (packet.regret (cut + time) (by omega) player).trans
      (mul_le_mul_of_nonneg_right htolerance
        (quittingRootAbsorptionMass_nonneg _))
  rational := fun player time htime => hfloor _ (by omega) (by omega) player
  chargeTarget_le := by
    simpa only [Finset.sum_Ico_eq_sum_range] using hcharge }

private theorem burnIn_le_horizon_and_requested_le_suffixCharge
    (roots : ℕ → Fin 4 → PMF Bool) {L horizon : ℕ} {requested : ℝ}
    (hrequested : 0 ≤ requested)
    (htotal : requested + (L : ℝ) ≤
      ∑ time ∈ Finset.range horizon,
        quittingRootAbsorptionMass (roots time)) :
    L ≤ horizon ∧ requested ≤
      ∑ time ∈ Finset.Ico L horizon,
        quittingRootAbsorptionMass (roots time) := by
  have htotalUpper :
      (∑ time ∈ Finset.range horizon,
          quittingRootAbsorptionMass (roots time)) ≤ (horizon : ℝ) := by
    calc
      (∑ time ∈ Finset.range horizon,
          quittingRootAbsorptionMass (roots time)) ≤
          ∑ _time ∈ Finset.range horizon, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro time _
        unfold quittingRootAbsorptionMass
        linarith [quittingStationaryContinueMass_nonneg (roots time)]
      _ = (horizon : ℝ) := by simp
  have hcut : L ≤ horizon := by
    by_contra hnot
    have hlt : (horizon : ℝ) < (L : ℝ) := by
      exact_mod_cast Nat.lt_of_not_ge hnot
    linarith
  have hprefix :
      (∑ time ∈ Finset.range L,
          quittingRootAbsorptionMass (roots time)) ≤ (L : ℝ) := by
    calc
      (∑ time ∈ Finset.range L,
          quittingRootAbsorptionMass (roots time)) ≤
          ∑ _time ∈ Finset.range L, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro time _
        unfold quittingRootAbsorptionMass
        linarith [quittingStationaryContinueMass_nonneg (roots time)]
      _ = (L : ℝ) := by simp
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun time => quittingRootAbsorptionMass (roots time)) hcut
  constructor
  · exact hcut
  · linarith

/-- A fixed burn-in length turns one exact floor-free packet with `L` units
of extra requested charge into a floor-bearing packet in the same box. -/
def QuittingFloorFreeFiniteForwardPacket.toFiniteForwardPacket
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {M B oldError newError requested : ℝ} {L : ℕ}
    (packet : QuittingFloorFreeFiniteForwardPacket reward
      (quittingForwardPacketCoordinateBox B) oldError
      (requested + (L : ℝ)))
    (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnormal : ∀ player, IsQuittingNormalPlayer reward player)
    (hnewError : 0 < newError)
    (holdError0 : 0 ≤ oldError)
    (hburnError : oldError ≤
      min (newError / 2) (newError ^ 2 / (8 * M)))
    (hburn : M + B < (L : ℝ) * (newError ^ 2 / (8 * M)))
    (hrequested : 0 ≤ requested) :
    QuittingFiniteForwardPacket reward
      (quittingForwardPacketCoordinateBox B) newError requested := by
  have holdError : oldError ≤ newError := by
    have := hburnError.trans (min_le_left _ _)
    linarith
  obtain ⟨hcut, hsuffix⟩ :=
    burnIn_le_horizon_and_requested_le_suffixCharge
      packet.roots hrequested packet.chargeTarget_le
  have hquit : ∀ time, time < packet.horizon → ∀ player,
      quittingRootQuitPayoff reward
          (packet.value time) (packet.roots time) player ≤
        packet.value (time + 1) player + oldError := by
    intro time htime player
    have hendpoint := isQuittingRootEndpointNash_of_supportApproxNash
      reward (packet.value time) (packet.roots time) holdError0
        (packet.support time htime)
    have hnash := (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
      reward (packet.value time) oldError (packet.roots time)).mp hendpoint
    have hle := quittingRootQuitPayoff_le_successor_add_of_isεNash
      reward (packet.value time) oldError (packet.roots time) player hnash
    rw [← congrFun (packet.policy time htime) player] at hle
    exact hle
  have hcontinue : ∀ time, time < packet.horizon → ∀ player,
      quittingRootContinuePayoff reward
          (packet.value time) (packet.roots time) player ≤
        packet.value (time + 1) player + oldError := by
    intro time htime player
    have hendpoint := isQuittingRootEndpointNash_of_supportApproxNash
      reward (packet.value time) (packet.roots time) holdError0
        (packet.support time htime)
    have hnash := (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
      reward (packet.value time) oldError (packet.roots time)).mp hendpoint
    have hle := quittingRootContinuePayoff_le_successor_add_of_isεNash
      reward (packet.value time) oldError (packet.roots time) player hnash
    rw [← congrFun (packet.policy time htime) player] at hle
    exact hle
  have hfloor :=
    quittingPunishmentFloor_le_of_finite_endpointErrors_after_burnIn
      reward packet.value packet.roots hM hreward hnormal hnewError
        hburnError hburn
          (fun player => neg_le_of_abs_le
            (packet.value_mem 0 (Nat.zero_le packet.horizon) player))
          hquit hcontinue
  exact packet.dropInitialRows L hcut holdError hfloor hsuffix

/-- A fixed burn-in length turns one weighted floor-free packet with `L`
units of extra requested charge into a floor-bearing packet in the same box. -/
def QuittingFloorFreeAbsorptionWeightedForwardPacket.toWeightedForwardPacket
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {M B oldTolerance newTolerance requested : ℝ} {L : ℕ}
    (packet : QuittingFloorFreeAbsorptionWeightedForwardPacket reward
      (quittingForwardPacketCoordinateBox B) oldTolerance
      (requested + (L : ℝ)))
    (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnormal : ∀ player, IsQuittingNormalPlayer reward player)
    (hnewTolerance : 0 < newTolerance)
    (holdTolerance0 : 0 ≤ oldTolerance)
    (hburnTolerance : 2 * oldTolerance ≤
      min (newTolerance / 2) (newTolerance ^ 2 / (8 * M)))
    (hburn : M + B < (L : ℝ) * (newTolerance ^ 2 / (8 * M)))
    (hrequested : 0 ≤ requested) :
    QuittingAbsorptionWeightedForwardPacket reward
      (quittingForwardPacketCoordinateBox B) newTolerance requested := by
  have holdTolerance : oldTolerance ≤ newTolerance := by
    have := hburnTolerance.trans (min_le_left _ _)
    linarith
  obtain ⟨hcut, hsuffix⟩ :=
    burnIn_le_horizon_and_requested_le_suffixCharge
      packet.roots hrequested packet.chargeTarget_le
  have hquit : ∀ time, time < packet.horizon → ∀ player,
      quittingRootQuitPayoff reward
          (packet.value time) (packet.roots time) player ≤
        packet.value (time + 1) player + 2 * oldTolerance := by
    intro time htime player
    let absorption := quittingRootAbsorptionMass (packet.roots time)
    have habsorption1 : absorption ≤ 1 := by
      dsimp only [absorption]
      unfold quittingRootAbsorptionMass
      linarith [quittingStationaryContinueMass_nonneg (packet.roots time)]
    have hbellman := packet.bellman time htime player
    have hsuccessor :
        quittingRootSuccessorPayoff reward
            (packet.value time) (packet.roots time) player ≤
          packet.value (time + 1) player + oldTolerance * absorption := by
      have hlower := neg_le_of_abs_le hbellman
      dsimp only [absorption] at hlower ⊢
      linarith
    have hregret := packet.regret time htime player
    have hendpoint := le_max_left
      (quittingRootQuitPayoff reward
        (packet.value time) (packet.roots time) player)
      (quittingRootContinuePayoff reward
        (packet.value time) (packet.roots time) player)
    unfold quittingRootCoordinateNashDefect at hregret
    have hscaled : oldTolerance * absorption ≤ oldTolerance :=
      mul_le_of_le_one_right holdTolerance0 habsorption1
    nlinarith
  have hcontinue : ∀ time, time < packet.horizon → ∀ player,
      quittingRootContinuePayoff reward
          (packet.value time) (packet.roots time) player ≤
        packet.value (time + 1) player + 2 * oldTolerance := by
    intro time htime player
    let absorption := quittingRootAbsorptionMass (packet.roots time)
    have habsorption1 : absorption ≤ 1 := by
      dsimp only [absorption]
      unfold quittingRootAbsorptionMass
      linarith [quittingStationaryContinueMass_nonneg (packet.roots time)]
    have hbellman := packet.bellman time htime player
    have hsuccessor :
        quittingRootSuccessorPayoff reward
            (packet.value time) (packet.roots time) player ≤
          packet.value (time + 1) player + oldTolerance * absorption := by
      have hlower := neg_le_of_abs_le hbellman
      dsimp only [absorption] at hlower ⊢
      linarith
    have hregret := packet.regret time htime player
    have hendpoint := le_max_right
      (quittingRootQuitPayoff reward
        (packet.value time) (packet.roots time) player)
      (quittingRootContinuePayoff reward
        (packet.value time) (packet.roots time) player)
    unfold quittingRootCoordinateNashDefect at hregret
    have hscaled : oldTolerance * absorption ≤ oldTolerance :=
      mul_le_of_le_one_right holdTolerance0 habsorption1
    nlinarith
  have hfloor :=
    quittingPunishmentFloor_le_of_finite_endpointErrors_after_burnIn
      reward packet.value packet.roots hM hreward hnormal hnewTolerance
        hburnTolerance hburn
          (fun player => neg_le_of_abs_le
            (packet.value_mem 0 (Nat.zero_le packet.horizon) player))
          hquit hcontinue
  exact packet.dropInitialRows L hcut holdTolerance hfloor hsuffix

/-- The exact suffix constructor exposes its retained horizon, roots, and
values literally. -/
theorem QuittingFloorFreeFiniteForwardPacket.dropInitialRows_spec
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {carrier : Set (Payoff (Fin 4))}
    {oldError newError oldCharge requested : ℝ}
    (packet : QuittingFloorFreeFiniteForwardPacket reward carrier
      oldError oldCharge)
    (cut : ℕ) (hcut : cut ≤ packet.horizon) (herror : oldError ≤ newError)
    (hfloor : ∀ time, cut ≤ time → time ≤ packet.horizon → ∀ player,
      quittingPunishmentValue reward player - newError ≤
        packet.value time player)
    (hcharge : requested ≤
      ∑ time ∈ Finset.Ico cut packet.horizon,
        quittingRootAbsorptionMass (packet.roots time)) :
    (packet.dropInitialRows cut hcut herror hfloor hcharge).horizon =
        packet.horizon - cut ∧
      (∀ time, (packet.dropInitialRows cut hcut herror hfloor hcharge).roots time =
        packet.roots (cut + time)) ∧
      ∀ time, (packet.dropInitialRows cut hcut herror hfloor hcharge).value time =
        packet.value (cut + time) := by
  exact ⟨rfl, fun _ => rfl, fun _ => rfl⟩

/-- The weighted suffix constructor exposes its retained horizon, roots, and
values literally. -/
theorem QuittingFloorFreeAbsorptionWeightedForwardPacket.dropInitialRows_spec
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {carrier : Set (Payoff (Fin 4))}
    {oldTolerance newTolerance oldCharge requested : ℝ}
    (packet : QuittingFloorFreeAbsorptionWeightedForwardPacket reward carrier
      oldTolerance oldCharge)
    (cut : ℕ) (hcut : cut ≤ packet.horizon)
    (htolerance : oldTolerance ≤ newTolerance)
    (hfloor : ∀ time, cut ≤ time → time ≤ packet.horizon → ∀ player,
      quittingPunishmentValue reward player - newTolerance ≤
        packet.value time player)
    (hcharge : requested ≤
      ∑ time ∈ Finset.Ico cut packet.horizon,
        quittingRootAbsorptionMass (packet.roots time)) :
    (packet.dropInitialRows cut hcut htolerance hfloor hcharge).horizon =
        packet.horizon - cut ∧
      (∀ time,
        (packet.dropInitialRows cut hcut htolerance hfloor hcharge).roots time =
          packet.roots (cut + time)) ∧
      ∀ time,
        (packet.dropInitialRows cut hcut htolerance hfloor hcharge).value time =
          packet.value (cut + time) := by
  exact ⟨rfl, fun _ => rfl, fun _ => rfl⟩

/-- A floor-bearing exact producer remains a producer after its floor fields
are forgotten. -/
theorem hasFloorFreeExactFiniteForwardPackets_of_exact
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (B : ℝ) (hexact : HasExactFiniteForwardPackets reward B) :
    HasFloorFreeExactFiniteForwardPackets reward B := by
  intro supportError herror chargeTarget hcharge
  obtain ⟨packet⟩ := hexact supportError herror chargeTarget hcharge
  exact ⟨packet.forgetPunishmentFloor⟩

/-- Under normality, a floor-free exact producer supplies the omitted floors
after a fixed burn-in without enlarging its box. -/
theorem hasExactFiniteForwardPackets_of_floorFree
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {M B : ℝ} (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnormal : ∀ player, IsQuittingNormalPlayer reward player)
    (hfloorFree : HasFloorFreeExactFiniteForwardPackets reward B) :
    HasExactFiniteForwardPackets reward B := by
  intro supportError herror
  let κ := supportError ^ 2 / (8 * M)
  have hκ : 0 < κ := by
    dsimp only [κ]
    positivity
  obtain ⟨L, hL⟩ := exists_nat_gt ((M + B) / κ)
  have hburn : M + B < (L : ℝ) * κ :=
    (div_lt_iff₀ hκ).mp hL
  let oldError := min (supportError / 2) κ
  have holdError : 0 < oldError := by
    exact lt_min (by positivity) hκ
  have hburnError : oldError ≤
      min (supportError / 2) (supportError ^ 2 / (8 * M)) := by
    dsimp only [oldError, κ]
    exact le_rfl
  intro requested hrequested
  obtain ⟨packet⟩ := hfloorFree oldError holdError
    (requested + (L : ℝ)) (by positivity)
  exact ⟨packet.toFiniteForwardPacket hM hreward hnormal herror
    holdError.le hburnError (by simpa only [κ] using hburn)
      hrequested⟩

/-- In a normal game, exact floor-free and floor-bearing production are
equivalent in each supplied coordinate box. -/
theorem hasFloorFreeExactFiniteForwardPackets_iff_exact
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {M B : ℝ} (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnormal : ∀ player, IsQuittingNormalPlayer reward player) :
    HasFloorFreeExactFiniteForwardPackets reward B ↔
      HasExactFiniteForwardPackets reward B := by
  constructor
  · exact hasExactFiniteForwardPackets_of_floorFree
      reward hM hreward hnormal
  · exact hasFloorFreeExactFiniteForwardPackets_of_exact reward B

/-- A floor-bearing weighted producer remains a producer after its floor
fields are forgotten. -/
theorem hasFloorFreeAbsorptionWeightedFiniteForwardPackets_of_weighted
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (B : ℝ) (hweighted : HasAbsorptionWeightedFiniteForwardPackets reward B) :
    HasFloorFreeAbsorptionWeightedFiniteForwardPackets reward B := by
  intro tolerance htolerance chargeTarget hcharge
  obtain ⟨packet⟩ := hweighted tolerance htolerance chargeTarget hcharge
  exact ⟨packet.forgetPunishmentFloor⟩

/-- Under normality, a floor-free weighted producer supplies the omitted
floors after a fixed burn-in without enlarging its box. -/
theorem hasAbsorptionWeightedFiniteForwardPackets_of_floorFree
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {M B : ℝ} (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnormal : ∀ player, IsQuittingNormalPlayer reward player)
    (hfloorFree :
      HasFloorFreeAbsorptionWeightedFiniteForwardPackets reward B) :
    HasAbsorptionWeightedFiniteForwardPackets reward B := by
  intro tolerance htolerance
  let κ := tolerance ^ 2 / (8 * M)
  have hκ : 0 < κ := by
    dsimp only [κ]
    positivity
  obtain ⟨L, hL⟩ := exists_nat_gt ((M + B) / κ)
  have hburn : M + B < (L : ℝ) * κ :=
    (div_lt_iff₀ hκ).mp hL
  let oldTolerance :=
    min (tolerance / 4) (tolerance ^ 2 / (16 * M))
  have holdTolerance : 0 < oldTolerance := by
    exact lt_min (by positivity) (by positivity)
  have holdQuarter : oldTolerance ≤ tolerance / 4 :=
    min_le_left _ _
  have holdSquare : oldTolerance ≤ tolerance ^ 2 / (16 * M) :=
    min_le_right _ _
  have hburnTolerance : 2 * oldTolerance ≤
      min (tolerance / 2) (tolerance ^ 2 / (8 * M)) := by
    apply le_min
    · linarith
    · have hdouble :
          2 * (tolerance ^ 2 / (16 * M)) =
            tolerance ^ 2 / (8 * M) := by
        field_simp
        ring
      linarith
  intro requested hrequested
  obtain ⟨packet⟩ := hfloorFree oldTolerance holdTolerance
    (requested + (L : ℝ)) (by positivity)
  exact ⟨packet.toWeightedForwardPacket hM hreward hnormal htolerance
    holdTolerance.le hburnTolerance
      (by simpa only [κ] using hburn) hrequested⟩

/-- In a normal game, weighted floor-free and floor-bearing production are
equivalent in each supplied coordinate box. -/
theorem hasFloorFreeAbsorptionWeightedFiniteForwardPackets_iff_weighted
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {M B : ℝ} (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnormal : ∀ player, IsQuittingNormalPlayer reward player) :
    HasFloorFreeAbsorptionWeightedFiniteForwardPackets reward B ↔
      HasAbsorptionWeightedFiniteForwardPackets reward B := by
  constructor
  · exact hasAbsorptionWeightedFiniteForwardPackets_of_floorFree
      reward hM hreward hnormal
  · exact hasFloorFreeAbsorptionWeightedFiniteForwardPackets_of_weighted
      reward B

end GameTheory

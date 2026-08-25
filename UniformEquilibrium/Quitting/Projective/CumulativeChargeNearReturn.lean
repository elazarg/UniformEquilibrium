/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import MathUE.DivergentChargeRecurrence
import UniformEquilibrium.Quitting.Projective.PunishmentFloorNearReturn

/-!
# Cumulative-charge payoff near-returns

A returned exact punishment-floor block need not contain one uniformly
charged edge.  It is enough that the sum of its one-stage absorption charges
stay uniformly positive.  The elementary survival product bound turns that
sum into a uniform lower bound on the block's weighted absorption, which is
the denominator required by the reversed-forward single-seam compiler.
-/

noncomputable section

namespace GameTheory

open Math.Probability
open QuittingPunishmentFloorAdmissibleChargedRelation

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

/-- A cumulative absorption floor implies a lower bound
`chargeFloor / (1 + chargeFloor)` on the weighted absorption of the reversed
finite block. -/
theorem cumulativeChargeRatio_le_reversedForwardWeightedAbsorption
    (cert : QuittingPunishmentFloorFinitePrefix reward)
    (chargeFloor : ℝ) (hchargeFloor : 0 < chargeFloor)
    (hcharge : chargeFloor ≤ cert.charge) :
    chargeFloor / (1 + chargeFloor) ≤
      quittingCyclicWeightedAbsorption
        (quittingReversedForwardCycle cert.roots 0 (cert.horizon - 1)) := by
  let q : ℕ → ℝ := fun time =>
    quittingRootAbsorptionMass (cert.roots time)
  have hq0 : ∀ time, 0 ≤ q time := fun time =>
    quittingRootAbsorptionMass_nonneg (cert.roots time)
  have hq1 : ∀ time, q time ≤ 1 := by
    intro time
    unfold q quittingRootAbsorptionMass
    linarith [quittingStationaryContinueMass_nonneg (cert.roots time)]
  have hhorizon : 0 < cert.horizon := by
    by_contra hnot
    have hzero : cert.horizon = 0 := Nat.eq_zero_of_not_pos hnot
    unfold QuittingPunishmentFloorFinitePrefix.charge at hcharge
    rw [hzero] at hcharge
    simp at hcharge
    linarith
  have hlength : cert.horizon - 1 + 1 = cert.horizon := by omega
  have hproduct := Math.prod_one_sub_mul_one_add_sum_range_le_one
    q hq0 hq1 0 cert.horizon
  have hsum : (∑ offset ∈ Finset.range cert.horizon,
      q (0 + offset)) = cert.charge := by
    simp only [zero_add, q, QuittingPunishmentFloorFinitePrefix.charge]
  rw [hsum] at hproduct
  have hprodNonneg : 0 ≤ ∏ offset ∈ Finset.range cert.horizon,
      (1 - q (0 + offset)) := by
    apply Finset.prod_nonneg
    intro offset _
    linarith [hq1 (0 + offset)]
  have hdenom : 0 < 1 + chargeFloor := by linarith
  have hscaled :
      (∏ offset ∈ Finset.range cert.horizon,
          (1 - q (0 + offset))) * (1 + chargeFloor) ≤ 1 := by
    calc
      (∏ offset ∈ Finset.range cert.horizon,
          (1 - q (0 + offset))) * (1 + chargeFloor) ≤
        (∏ offset ∈ Finset.range cert.horizon,
          (1 - q (0 + offset))) * (1 + cert.charge) := by
            apply mul_le_mul_of_nonneg_left _ hprodNonneg
            linarith
      _ ≤ 1 := by simpa only [zero_add, q] using hproduct
  have hprodLe : (∏ offset ∈ Finset.range cert.horizon,
      (1 - q (0 + offset))) ≤ 1 / (1 + chargeFloor) := by
    exact (le_div_iff₀ hdenom).2 (by simpa [one_div] using hscaled)
  have hratio : chargeFloor / (1 + chargeFloor) =
      1 - 1 / (1 + chargeFloor) := by
    field_simp
    ring
  have hprodLe' : (∏ offset ∈ Finset.range cert.horizon,
      (1 - quittingRootAbsorptionMass (cert.roots offset))) ≤
        1 / (1 + chargeFloor) := by
    simpa only [zero_add, q] using hprodLe
  rw [quittingCyclicWeightedAbsorption_reversedForwardCycle, hlength]
  simp only [zero_add]
  rw [hratio]
  linarith [hprodLe']

/-- One exact floor prefix with a positive cumulative charge and a sufficiently
small endpoint payoff seam gives a single-seam projective lasso. -/
theorem exists_singleSeamProjectiveLasso_of_floorPrefix_cumulativePayoffNearReturn
    (cert : QuittingPunishmentFloorFinitePrefix reward)
    (chargeFloor seamError error : ℝ)
    (hchargeFloor : 0 < chargeFloor)
    (hcharge : chargeFloor ≤ cert.charge)
    (hseamError : 0 ≤ seamError)
    (hseamScale : seamError ≤
      error * (chargeFloor / (1 + chargeFloor)))
    (hclose : ∀ who,
      |cert.value 0 who - cert.value cert.horizon who| ≤ seamError) :
    ∃ K : ℕ,
      Nonempty (QuittingFiniteSingleSeamProjectiveLasso reward K error) := by
  have hratio : 0 < chargeFloor / (1 + chargeFloor) := by
    apply div_pos hchargeFloor
    linarith
  have herror : 0 ≤ error := by
    by_contra hnot
    have hnegative : error * (chargeFloor / (1 + chargeFloor)) < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge hnot) hratio
    linarith
  have hhorizon : 0 < cert.horizon := by
    by_contra hnot
    have hzero : cert.horizon = 0 := Nat.eq_zero_of_not_pos hnot
    unfold QuittingPunishmentFloorFinitePrefix.charge at hcharge
    rw [hzero] at hcharge
    simp at hcharge
    linarith
  let n := cert.horizon - 1
  have hlength : n + 1 = cert.horizon := by
    dsimp only [n]
    omega
  let supportError := error - seamError
  have hratioLeOne : chargeFloor / (1 + chargeFloor) ≤ 1 := by
    have hdenom : 0 < 1 + chargeFloor := by linarith
    apply (div_le_one hdenom).2
    linarith
  have hseamLeError : seamError ≤ error := by
    calc
      seamError ≤ error * (chargeFloor / (1 + chargeFloor)) := hseamScale
      _ ≤ error * 1 := mul_le_mul_of_nonneg_left hratioLeOne herror
      _ = error := mul_one error
  have hsupportError : 0 ≤ supportError := by
    dsimp only [supportError]
    linarith
  have hpolicy : ∀ time,
      0 ≤ time → time < 0 + n + 1 →
      cert.value (time + 1) = quittingRootSuccessorPayoff reward
        (cert.value time) (cert.roots time) := by
    intro time _ htime
    exact cert.policy time (by simpa only [zero_add, hlength] using htime)
  have hsupport : ∀ time,
      0 ≤ time → time < 0 + n + 1 →
      IsQuittingRootSupportApproxNash reward
        (cert.value time) supportError (cert.roots time) := by
    intro time _ htime
    have hexact := isQuittingRootSupportApproxNash_zero_of_isZeroNash
      reward (cert.value time) (cert.roots time)
      (cert.exactNash time (by simpa only [zero_add, hlength] using htime))
    intro who
    constructor
    · intro hquit
      linarith [((hexact who).1 hquit)]
    · intro hcontinue
      linarith [((hexact who).2 hcontinue)]
  have hdecodedClose : ∀ who,
      |cert.value 0 who - cert.value (0 + n + 1) who| ≤ seamError := by
    intro who
    rw [zero_add, hlength]
    exact hclose who
  have hweighted : chargeFloor / (1 + chargeFloor) ≤
      quittingCyclicWeightedAbsorption
        (quittingReversedForwardCycle cert.roots 0 n) := by
    exact cumulativeChargeRatio_le_reversedForwardWeightedAbsorption
      cert chargeFloor hchargeFloor hcharge
  have hclosingRatio : seamError ≤
      (supportError + seamError) *
        quittingCyclicWeightedAbsorption
          (quittingReversedForwardCycle cert.roots 0 n) := by
    have htotal : supportError + seamError = error := by
      dsimp only [supportError]
      ring
    rw [htotal]
    exact hseamScale.trans (mul_le_mul_of_nonneg_left hweighted herror)
  have hrational : ∀ targetWho time,
      0 < time → time ≤ 0 + n + 1 →
      quittingPunishmentValue reward targetWho -
          (supportError + seamError) ≤ cert.value time targetWho := by
    intro targetWho time _ htime
    have hfloor := quittingPunishmentValue_le_finitePrefixValue
      cert time (by simpa only [zero_add, hlength] using htime) targetWho
    linarith [hfloor, herror]
  have hsumPos : 0 < ∑ time ∈ Finset.range cert.horizon,
      quittingRootAbsorptionMass (cert.roots time) := by
    exact hchargeFloor.trans_le hcharge
  have hexists : ∃ stage ∈ Finset.range cert.horizon,
      0 < quittingRootAbsorptionMass (cert.roots stage) := by
    apply (Finset.sum_pos_iff_of_nonneg ?_).mp hsumPos
    intro stage _
    exact quittingRootAbsorptionMass_nonneg (cert.roots stage)
  obtain ⟨stage, hstage, hstagePositive⟩ := hexists
  let rawPhase : Fin (n + 1) :=
    ⟨stage, by simpa only [hlength] using Finset.mem_range.mp hstage⟩
  let absorbingPhase : Fin (n + 1) := rawPhase.rev
  have habsorbing : 0 < quittingRootAbsorptionMass
      (quittingReversedForwardCycle cert.roots 0 n absorbingPhase) := by
    simpa [quittingReversedForwardCycle, absorbingPhase, rawPhase] using
      hstagePositive
  let lasso :=
    quittingFiniteSingleSeamProjectiveLasso_of_reversedForwardBlock
      reward cert.roots cert.value 0 n
      (supportError := supportError) (seamError := seamError)
      hsupportError hseamError hpolicy hsupport hdecodedClose hclosingRatio
      hrational absorbingPhase habsorbing
  refine ⟨n + 1, ?_⟩
  have htotal : supportError + seamError = error := by
    dsimp only [supportError]
    ring
  rw [← htotal]
  exact ⟨lasso⟩

/-- A fixed positive lower bound on total path charge together with exact
floor-admissible payoff near-returns at every endpoint tolerance. -/
structure QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota) where
  chargeFloor : ℝ
  chargeFloor_pos : 0 < chargeFloor
  nearReturn : ∀ endpointError : ℝ, 0 < endpointError →
    ∃ (source target : QuittingPunishmentFloorAdmissibleState reward)
      (path : (quittingPunishmentFloorAdmissibleChargedRelation reward).Path
        source target),
      chargeFloor ≤ path.chargeSum ∧
        ∀ who,
          |source.1.1.1 who - target.1.1.1 who| ≤ endpointError

/-- Cumulative-charge payoff near-returns imply a uniform-equilibrium payoff.
No individual edge is required to retain a positive charge floor. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_cumulativePayoffNearReturns
    (family : QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily
      reward) :
    ∃ payoff : Payoff iota,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  have hratio : 0 < family.chargeFloor / (1 + family.chargeFloor) := by
    exact div_pos family.chargeFloor_pos (by
      linarith [family.chargeFloor_pos])
  obtain ⟨sampleSource, sampleTarget, samplePath, hsampleCharge,
      _hsampleClose⟩ := family.nearReturn family.chargeFloor
        family.chargeFloor_pos
  letI : Nonempty iota := by
    rcases isEmpty_or_nonempty iota with hempty | hnonempty
    · letI : IsEmpty iota := hempty
      have hzero : samplePath.chargeSum = 0 := by
        rw [← QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix_charge]
        unfold QuittingPunishmentFloorFinitePrefix.charge
        apply Finset.sum_eq_zero
        intro time _
        have hroot :
            (QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix
              samplePath).roots time = quittingAllContinueRoot := by
          funext who
          exact isEmptyElim who
        rw [hroot, quittingRootAbsorptionMass_allContinueRoot]
      rw [hzero] at hsampleCharge
      exact False.elim (not_lt_of_ge hsampleCharge family.chargeFloor_pos)
    · exact hnonempty
  apply quittingGame_exists_uniformEquilibriumPayoff_of_singleSeamProjectiveLassos
    reward
  intro error herror
  have hendpointError :
      0 < error * (family.chargeFloor / (1 + family.chargeFloor)) :=
    mul_pos herror hratio
  obtain ⟨source, target, path, hcharge, hclose⟩ :=
    family.nearReturn
      (error * (family.chargeFloor / (1 + family.chargeFloor)))
      hendpointError
  let cert :=
    QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix path
  apply exists_singleSeamProjectiveLasso_of_floorPrefix_cumulativePayoffNearReturn
    cert family.chargeFloor
      (error * (family.chargeFloor / (1 + family.chargeFloor))) error
      family.chargeFloor_pos
  · simpa only [cert,
      QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix_charge]
      using hcharge
  · exact hendpointError.le
  · exact le_rfl
  · intro who
    have hzero : cert.value 0 = source.1.1.1 := by
      exact QuittingPunishmentFloorBoxPath.value_zero
        (QuittingPunishmentFloorAdmissibleChargedRelation.pathToBoxPath path)
    have hfinal : cert.value cert.horizon = target.1.1.1 :=
      QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix_value_horizon
        path
    rw [hzero, hfinal]
    exact hclose who

namespace QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily

/-- The former fixed-edge-scale near-return interface implies the weaker
cumulative-charge interface. -/
def ofPositiveAdmissiblePayoffNearReturnFamily
    (family : QuittingPositiveAdmissiblePayoffNearReturnFamily reward) :
    QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily reward where
  chargeFloor := family.chargeThreshold
  chargeFloor_pos := family.charge_pos
  nearReturn := by
    intro endpointError hendpointError
    obtain ⟨source, target, path, hclose, hhigh⟩ :=
      family.nearReturn endpointError hendpointError
    obtain ⟨stage, hstage, hstageCharge⟩ :=
      decodedPathHasChargeAtLeast_of_highChargeCount_pos
        path family.chargeThreshold hhigh
    refine ⟨source, target, path, ?_, hclose⟩
    apply hstageCharge.trans
    rw [← QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix_charge]
    unfold QuittingPunishmentFloorFinitePrefix.charge
    exact Finset.single_le_sum
      (s := Finset.range
        (QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix
          path).horizon)
      (f := fun time => quittingRootAbsorptionMass
        ((QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix
          path).roots time))
      (fun time _ => quittingRootAbsorptionMass_nonneg
        ((QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix
          path).roots time))
      (Finset.mem_range.mpr hstage)

/-- Packaged cumulative-charge near-returns are a direct uniform-payoff
certificate. -/
theorem exists_uniformEquilibriumPayoff
    (family : QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily
      reward) :
    ∃ payoff : Payoff iota,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  quittingGame_exists_uniformEquilibriumPayoff_of_cumulativePayoffNearReturns
    family

end QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily

end GameTheory

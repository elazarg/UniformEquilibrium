/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Examples.BlockPair.PairedCollisionRewardTable
import UniformEquilibrium.Quitting.Stationary.EndpointCompiler
import UniformEquilibrium.Quitting.Stationary.CompleteBehavioralCap
import MathUE.PMFProduct.FiniteFubini
import Mathlib.Topology.Order.IntermediateValue

/-!
# Common-hazard stationary production on the literal collision table

The scalar intermediate value theorem produces the hazard internally. Root
expectations are evaluated on the actual raw rewards. The contracting endpoint
compiler supplies the complete behavioral cap and the fixed uniform payoff.
-/

noncomputable section

namespace GameTheory.PairedCollisionReward

open StochasticGame _root_.Math.Probability Math.PMFProduct

def stationaryQuitValue (c q : ℝ) : ℝ :=
  (1 - q) ^ 3 + 3 * c * q * (1 - q) ^ 2 + q ^ 2 * (1 - q) - q ^ 3

def stationaryContinueReward (q : ℝ) : ℝ :=
  4 * q * (1 - q) ^ 2 + 2 * q ^ 2 * (1 - q)

def stationaryOpponentMass (q : ℝ) : ℝ := (1 - q) ^ 3

def stationaryResidual (c q : ℝ) : ℝ :=
  (1 - stationaryOpponentMass q) * stationaryQuitValue c q -
    stationaryContinueReward q

theorem stationaryResidual_half (c : ℝ) :
    stationaryResidual c (1 / 2) = (21 * c - 41) / 64 := by
  unfold stationaryResidual stationaryOpponentMass stationaryQuitValue
    stationaryContinueReward
  ring

theorem stationaryResidual_four_oneHundredth :
    stationaryResidual 4 (1 / 100) = -7087044691 / 10 ^ 12 := by
  norm_num [stationaryResidual, stationaryOpponentMass, stationaryQuitValue,
    stationaryContinueReward]

theorem stationaryResidual_parameter_difference (c d q : ℝ) :
    stationaryResidual d q - stationaryResidual c q =
      3 * q * (1 - q) ^ 2 * (1 - (1 - q) ^ 3) * (d - c) := by
  unfold stationaryResidual stationaryOpponentMass stationaryQuitValue
    stationaryContinueReward
  ring

/-- An actual interior zero, with no supplied favorable continuation or cap. -/
theorem exists_stationaryHazard {c : ℝ} (hc2 : 2 ≤ c) (hc4 : c ≤ 4) :
    ∃ q : ℝ, q ∈ Set.Ioo ((1 : ℝ) / 100) (1 / 2) ∧
      stationaryResidual c q = 0 := by
  have hleft : stationaryResidual c (1 / 100) < 0 := by
    have hdiff := stationaryResidual_parameter_difference c 4 (1 / 100)
    rw [stationaryResidual_four_oneHundredth] at hdiff
    norm_num at hdiff
    nlinarith
  have hright : 0 < stationaryResidual c (1 / 2) := by
    rw [stationaryResidual_half]
    linarith
  have hcontinuous : ContinuousOn (stationaryResidual c)
      (Set.Icc ((1 : ℝ) / 100) (1 / 2)) := by
    unfold stationaryResidual stationaryOpponentMass stationaryQuitValue
      stationaryContinueReward
    fun_prop
  obtain ⟨q, hq, hroot⟩ := intermediate_value_Icc
    (by norm_num : (1 : ℝ) / 100 ≤ 1 / 2) hcontinuous ⟨hleft.le, hright.le⟩
  refine ⟨q, ⟨?_, ?_⟩, hroot⟩
  · exact lt_of_le_of_ne hq.1 fun h ↦ by subst q; linarith
  · exact lt_of_le_of_ne hq.2 fun h ↦ by subst q; linarith

def commonCoin (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : PMF Bool :=
  quittingHazardCoin q hq0 hq1

@[simp] theorem commonCoin_true (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (commonCoin q hq0 hq1 true).toReal = q := by
  simp [commonCoin]

@[simp] theorem commonCoin_false (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (commonCoin q hq0 hq1 false).toReal = 1 - q := by
  simp [commonCoin]

@[simp] theorem expect_commonCoin (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (f : Bool → ℝ) :
    expect (commonCoin q hq0 hq1) f = (1 - q) * f false + q * f true := by
  rw [expect_eq_sum, Fintype.sum_bool]
  simp
  ring

def commonRoot (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : Player → PMF Bool :=
  fun _ => commonCoin q hq0 hq1

/-- Evaluation of the eight literal Quit outcomes for any queried player. -/
theorem commonRoot_quitPayoff (c q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (tail : Payoff Player) (who : Player) :
    quittingRootQuitPayoff (reward c) tail (commonRoot q hq0 hq1) who =
      stationaryQuitValue c q := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  fin_cases who <;>
    simp [commonRoot, quittingRootPayoff, quittingQuitters, reward,
      stationaryQuitValue] <;> ring

/-- Evaluation of actual Continue outcomes, including the live continuation. -/
theorem commonRoot_continuePayoff (c q v : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (who : Player) :
    quittingRootContinuePayoff (reward c) (fun _ => v) (commonRoot q hq0 hq1) who =
      stationaryContinueReward q + stationaryOpponentMass q * v := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  fin_cases who <;>
    simp [commonRoot, quittingRootPayoff, quittingQuitters, reward,
      stationaryContinueReward, stationaryOpponentMass] <;> ring

theorem commonRoot_continueMass (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    quittingStationaryContinueMass (commonRoot q hq0 hq1) = (1 - q) ^ 4 := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  simp [commonRoot]

theorem commonRoot_opponentMass (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (who : Player) :
    quittingStationaryFixedOpponentsContinueMass (commonRoot q hq0 hq1) who =
      stationaryOpponentMass q := by
  unfold quittingStationaryFixedOpponentsContinueMass quittingFixedOpponentsContinueMass
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  fin_cases who <;> simp [commonRoot, Fin.prod_univ_succ, stationaryOpponentMass] <;> ring

theorem commonRoot_absorbs (q : ℝ) (hq1 : q ≤ 1) (hq : 0 < q) :
    quittingStationaryContinueMass (commonRoot q (le_of_lt hq) hq1) < 1 := by
  apply lt_of_le_of_lt
    (quittingStationaryContinueMass_le_ownContinueProbability
      (commonRoot q (le_of_lt hq) hq1) 0)
  simp only [commonRoot, commonCoin_false]
  linarith

theorem commonRoot_contracts (q : ℝ) (hq1 : q ≤ 1)
    (hq : 0 < q) (who : Player) :
    quittingStationaryFixedOpponentsContinueMass
      (commonRoot q (le_of_lt hq) hq1) who < 1 := by
  rw [commonRoot_opponentMass]
  unfold stationaryOpponentMass
  exact pow_lt_one₀ (sub_nonneg.mpr hq1) (by linarith : 1 - q < 1) (by decide)

theorem commonRoot_fixedQuitValue (c q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (who : Player) :
    quittingStationaryFixedOpponentsQuitValue (reward c) (commonRoot q hq0 hq1) who =
      stationaryQuitValue c q := by
  have h := quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
    (reward c) (fun _ => commonRoot q hq0 hq1) who 0 0
  rw [commonRoot_quitPayoff] at h
  exact h.symm

theorem commonRoot_fixedContinueReward (c q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (who : Player) :
    quittingStationaryFixedOpponentsContinueReward (reward c) (commonRoot q hq0 hq1)
      who = stationaryContinueReward q := by
  have h := quittingRootContinuePayoff_eq_fixedOpponents
    (reward c) (fun _ => commonRoot q hq0 hq1) who (fun _ => 0) 0
  rw [commonRoot_continuePayoff] at h
  simpa [quittingStationaryFixedOpponentsContinueReward] using h.symm

/-- Before selecting a zero, the exact cap is the maximum of Quit and literal Never. -/
theorem commonProfile_completeCap_eq_max (c q : ℝ) (hq1 : q ≤ 1)
    (hq : 0 < q) (who : Player) :
    quittingContinuationBestResponseValue (reward c)
      (quittingStationaryProfile (reward c) (commonRoot q (le_of_lt hq) hq1)) who =
        max (stationaryQuitValue c q)
          (stationaryContinueReward q / (1 - stationaryOpponentMass q)) := by
  rw [quittingContinuationBestResponseValue_stationary_eq_fullRateUnilateralCap,
    quittingStationaryFullRateUnilateralCap_of_lt (reward c)
      (commonRoot q (le_of_lt hq) hq1) who (commonRoot_contracts q hq1 hq who)]
  unfold quittingStationaryUnilateralCap quittingStationarySelectedCap
    quittingStationaryNeverValue
  rw [commonRoot_fixedQuitValue, commonRoot_fixedContinueReward, commonRoot_opponentMass]

theorem commonRoot_fixedPoint (c q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hroot : stationaryResidual c q = 0) :
    (fun _ => stationaryQuitValue c q) = quittingRootSuccessorPayoff (reward c)
      (fun _ => stationaryQuitValue c q) (commonRoot q hq0 hq1) := by
  funext who
  rw [quittingRootSuccessorPayoff_eq_endpointMix, commonRoot_quitPayoff,
    commonRoot_continuePayoff]
  simp only [commonRoot, commonCoin_true, commonCoin_false]
  unfold stationaryResidual at hroot
  have hcontinue : stationaryContinueReward q +
      stationaryOpponentMass q * stationaryQuitValue c q = stationaryQuitValue c q := by
    linarith
  rw [hcontinue]
  ring

theorem commonRoot_endpointNash (c q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hroot : stationaryResidual c q = 0) :
    IsεQuittingRootEndpointNash (reward c) (fun _ => stationaryQuitValue c q) 0
      (commonRoot q hq0 hq1) := by
  intro who
  have hdiff : quittingRootEndpointDifference (reward c)
      (fun _ => stationaryQuitValue c q) (commonRoot q hq0 hq1) who = 0 := by
    unfold quittingRootEndpointDifference
    rw [commonRoot_quitPayoff, commonRoot_continuePayoff]
    unfold stationaryResidual at hroot
    linarith
  simp [hdiff]

/-- The terminal payoff is the constant vector of the actual Quit expectation. -/
theorem commonProfile_terminalPayoff (c q : ℝ) (hq1 : q ≤ 1)
    (hq : 0 < q) (hroot : stationaryResidual c q = 0) :
    quittingTerminalPayoff (reward c)
      (quittingStationaryProfile (reward c) (commonRoot q (le_of_lt hq) hq1)) =
        fun _ => stationaryQuitValue c q :=
  quittingTerminalPayoff_stationary_eq_of_fixedPoint (reward c)
    (commonRoot q (le_of_lt hq) hq1)
    (fun _ => stationaryQuitValue c q) (commonRoot_absorbs q hq1 hq)
    (commonRoot_fixedPoint c q (le_of_lt hq) hq1 hroot)

/-- The exact complete behavioral cap includes every stopping date and literal Never. -/
theorem commonProfile_completeCap (c q : ℝ) (hq1 : q ≤ 1)
    (hq : 0 < q) (hroot : stationaryResidual c q = 0) (who : Player) :
    quittingContinuationBestResponseValue (reward c)
      (quittingStationaryProfile (reward c) (commonRoot q (le_of_lt hq) hq1)) who =
        stationaryQuitValue c q := by
  rw [quittingContinuationBestResponseValue_stationary_eq_fullRateUnilateralCap]
  exact quittingStationaryFullRateUnilateralCap_eq_of_fixedPoint_endpointNash
    (reward c) (commonRoot q (le_of_lt hq) hq1) (fun _ => stationaryQuitValue c q)
    (commonRoot_absorbs q hq1 hq) (commonRoot_fixedPoint c q (le_of_lt hq) hq1 hroot)
    (commonRoot_endpointNash c q (le_of_lt hq) hq1 hroot)
    (isQuittingStationaryBoundaryAdmissible_of_contracts (reward c)
      (commonRoot q (le_of_lt hq) hq1) (fun _ => stationaryQuitValue c q)
      (commonRoot_contracts q hq1 hq)) who

theorem commonProfile_isExactTerminalNash (c q : ℝ) (hq1 : q ≤ 1)
    (hq : 0 < q) (hroot : stationaryResidual c q = 0) :
    (quittingGame (reward c)).IsεAsymptoticNash (quittingTerminalPayoff (reward c)) 0
      (quittingStationaryProfile (reward c) (commonRoot q (le_of_lt hq) hq1)) :=
  isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts
    (reward c) (commonRoot q (le_of_lt hq) hq1) (fun _ => stationaryQuitValue c q)
    (commonRoot_absorbs q hq1 hq) (commonRoot_fixedPoint c q (le_of_lt hq) hq1 hroot)
    (commonRoot_endpointNash c q (le_of_lt hq) hq1 hroot) (commonRoot_contracts q hq1 hq)

theorem commonProfile_isUniformEquilibriumPayoff (c q : ℝ)
    (hq1 : q ≤ 1) (hq : 0 < q) (hroot : stationaryResidual c q = 0) :
    (quittingGame (reward c)).IsUniformEquilibriumPayoff none
      (fun _ => stationaryQuitValue c q) :=
  isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts
    (reward c) (commonRoot q (le_of_lt hq) hq1) (fun _ => stationaryQuitValue c q)
    (commonRoot_absorbs q hq1 hq) (commonRoot_fixedPoint c q (le_of_lt hq) hq1 hroot)
    (commonRoot_endpointNash c q (le_of_lt hq) hq1 hroot) (commonRoot_contracts q hq1 hq)

/-- Internally selected common hazard and its fixed uniform payoff on `2 ≤ c ≤ 4`. -/
theorem exists_stationaryUniformPayoff {c : ℝ} (hc2 : 2 ≤ c) (hc4 : c ≤ 4) :
    ∃ q : ℝ, q ∈ Set.Ioo ((1 : ℝ) / 100) (1 / 2) ∧
      (quittingGame (reward c)).IsUniformEquilibriumPayoff none
        (fun _ => stationaryQuitValue c q) := by
  obtain ⟨q, hq, hroot⟩ := exists_stationaryHazard hc2 hc4
  have hq1 : q ≤ 1 := by linarith [hq.2]
  have hqpos : 0 < q := by linarith [hq.1]
  exact ⟨q, hq, commonProfile_isUniformEquilibriumPayoff c q hq1 hqpos hroot⟩

end GameTheory.PairedCollisionReward

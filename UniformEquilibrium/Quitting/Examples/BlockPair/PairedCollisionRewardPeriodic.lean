/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.PairedPhasePolynomialRoots
import UniformEquilibrium.Quitting.Examples.BlockPair.PairedCollisionRewardStationary
import UniformEquilibrium.Quitting.Cycles.PeriodicCompiler

/-!
# Actual period-two equilibrium in the literal paired-collision reward family

The scalar producer supplies the two rates. This module evaluates the literal
root rewards and uses the generic periodic compiler for unrestricted behavioral
deviations. It does not yet establish the packet's separate exact censored-law
identities or its explicit finite-horizon constants.
-/

noncomputable section

namespace GameTheory.PairedCollisionReward

open StochasticGame _root_.Math.Probability Math.PMFProduct
open _root_.Math.PairedPhasePolynomialRoots

/-- Scalar data produced by the two intermediate value arguments. -/
structure PeriodicRates (c : ℝ) where
  primary : ℝ
  secondary : ℝ
  quarter_lt : (1 : ℝ) / 4 < secondary
  secondary_lt_primary : secondary < primary
  primary_lt : primary < 9 / 10
  half_lt : (1 : ℝ) / 2 < primary
  primary_zero : primaryResidual c primary secondary = 0
  secondary_zero : secondaryResidual c primary secondary = 0

theorem exists_periodicRates {c : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2) :
    Nonempty (PeriodicRates c) := by
  obtain ⟨a, b, hb, hba, ha, hhalf, hF, hG⟩ := exists_admissible_rates hc
  exact ⟨⟨a, b, hb, hba, ha, hhalf, hF, hG⟩⟩

namespace PeriodicRates

variable {c : ℝ} (rates : PeriodicRates c)

theorem primary_pos : 0 < rates.primary := by linarith [rates.half_lt]

theorem secondary_pos : 0 < rates.secondary := by linarith [rates.quarter_lt]

theorem primary_lt_one : rates.primary < 1 := by linarith [rates.primary_lt]

theorem secondary_lt_one : rates.secondary < 1 := by
  linarith [rates.secondary_lt_primary, rates.primary_lt]

/-- The multiplied primary equation gives the actual quiet-phase recursion. -/
theorem primary_recursion :
    affineEndpoint c rates.secondary / rates.secondary =
      (1 - rates.primary) * (1 + 3 * rates.secondary) +
        rates.primary * rates.secondary * affineEndpoint c rates.secondary := by
  apply (div_eq_iff rates.secondary_pos.ne').mpr
  have hF := rates.primary_zero
  unfold primaryResidual at hF
  nlinarith

theorem secondary_recursion :
    affineEndpoint c rates.primary / rates.primary =
      4 * rates.primary * (1 - rates.secondary) +
        rates.primary * rates.secondary * affineEndpoint c rates.primary := by
  apply (div_eq_iff rates.primary_pos.ne').mpr
  have hG := rates.secondary_zero
  unfold secondaryResidual at hG
  nlinarith

def primaryCoin : PMF Bool :=
  commonCoin (1 - rates.primary) (by linarith [rates.primary_lt_one])
    (by linarith [rates.primary_pos])

def secondaryCoin : PMF Bool :=
  commonCoin (1 - rates.secondary) (by linarith [rates.secondary_lt_one])
    (by linarith [rates.secondary_pos])

@[simp] theorem expect_primaryCoin (f : Bool → ℝ) :
    expect rates.primaryCoin f = rates.primary * f false +
      (1 - rates.primary) * f true := by
  simp [primaryCoin]

@[simp] theorem expect_secondaryCoin (f : Bool → ℝ) :
    expect rates.secondaryCoin f = rates.secondary * f false +
      (1 - rates.secondary) * f true := by
  simp [secondaryCoin]

@[simp] theorem primaryCoin_false : (rates.primaryCoin false).toReal = rates.primary := by
  simp [primaryCoin]

@[simp] theorem primaryCoin_true :
    (rates.primaryCoin true).toReal = 1 - rates.primary := by simp [primaryCoin]

@[simp] theorem secondaryCoin_false :
    (rates.secondaryCoin false).toReal = rates.secondary := by simp [secondaryCoin]

@[simp] theorem secondaryCoin_true :
    (rates.secondaryCoin true).toReal = 1 - rates.secondary := by simp [secondaryCoin]

def phaseARoot : Player → PMF Bool :=
  ![rates.primaryCoin, PMF.pure false, rates.secondaryCoin, PMF.pure false]

def phaseBRoot : Player → PMF Bool :=
  ![PMF.pure false, rates.primaryCoin, PMF.pure false, rates.secondaryCoin]

def phaseAValue : Payoff Player :=
  ![affineEndpoint c rates.secondary, affineEndpoint c rates.secondary / rates.secondary,
    affineEndpoint c rates.primary, affineEndpoint c rates.primary / rates.primary]

def phaseBValue : Payoff Player :=
  ![affineEndpoint c rates.secondary / rates.secondary, affineEndpoint c rates.secondary,
    affineEndpoint c rates.primary / rates.primary, affineEndpoint c rates.primary]

/-- All four immediate Quit expectations at phase A, on the actual raw table. -/
theorem phaseA_quitPayoff (who : Player) :
    quittingRootQuitPayoff (reward c) rates.phaseBValue rates.phaseARoot who =
      ![affineEndpoint c rates.secondary, primaryJoin c rates.primary rates.secondary,
        affineEndpoint c rates.primary, secondaryJoin c rates.primary rates.secondary]
        who := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  fin_cases who <;>
    simp [phaseARoot, phaseBValue, quittingRootPayoff, quittingQuitters, reward,
      affineEndpoint, primaryJoin, secondaryJoin] <;> ring

theorem phaseB_quitPayoff (who : Player) :
    quittingRootQuitPayoff (reward c) rates.phaseAValue rates.phaseBRoot who =
      ![primaryJoin c rates.primary rates.secondary, affineEndpoint c rates.secondary,
        secondaryJoin c rates.primary rates.secondary, affineEndpoint c rates.primary]
        who := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  fin_cases who <;>
    simp [phaseBRoot, phaseAValue, quittingRootPayoff, quittingQuitters, reward,
      affineEndpoint, primaryJoin, secondaryJoin] <;> ring

/-- Every prescribed Continue endpoint equals its phase-A value. -/
theorem phaseA_continuePayoff (who : Player) :
    quittingRootContinuePayoff (reward c) rates.phaseBValue rates.phaseARoot who =
      rates.phaseAValue who := by
  have hF := rates.primary_zero
  have hG := rates.secondary_zero
  unfold primaryResidual at hF
  unfold secondaryResidual at hG
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  fin_cases who <;>
    simp [phaseARoot, phaseAValue, phaseBValue, quittingRootPayoff, quittingQuitters,
      reward] <;>
    field_simp [rates.primary_pos.ne', rates.secondary_pos.ne'] <;> nlinarith

theorem phaseB_continuePayoff (who : Player) :
    quittingRootContinuePayoff (reward c) rates.phaseAValue rates.phaseBRoot who =
      rates.phaseBValue who := by
  have hF := rates.primary_zero
  have hG := rates.secondary_zero
  unfold primaryResidual at hF
  unfold secondaryResidual at hG
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  fin_cases who <;>
    simp [phaseBRoot, phaseAValue, phaseBValue, quittingRootPayoff, quittingQuitters,
      reward] <;>
    field_simp [rates.primary_pos.ne', rates.secondary_pos.ne'] <;> nlinarith

theorem phaseA_successor :
    rates.phaseAValue = quittingRootSuccessorPayoff (reward c) rates.phaseBValue
      rates.phaseARoot := by
  funext who
  rw [quittingRootSuccessorPayoff_eq_endpointMix, rates.phaseA_quitPayoff,
    rates.phaseA_continuePayoff]
  fin_cases who <;> simp [phaseARoot, phaseAValue] <;> ring

theorem phaseB_successor :
    rates.phaseBValue = quittingRootSuccessorPayoff (reward c) rates.phaseAValue
      rates.phaseBRoot := by
  funext who
  rw [quittingRootSuccessorPayoff_eq_endpointMix, rates.phaseB_quitPayoff,
    rates.phaseB_continuePayoff]
  fin_cases who <;> simp [phaseBRoot, phaseBValue] <;> ring

/-- Both quiet joins are strictly worse than the actual quiet Continue endpoints. -/
theorem quiet_slacks_pos (hc : c ∈ Set.Icc (1 : ℝ) 2) :
    primaryJoin c rates.primary rates.secondary <
        affineEndpoint c rates.secondary / rates.secondary ∧
      secondaryJoin c rates.primary rates.secondary <
        affineEndpoint c rates.primary / rates.primary := by
  exact ⟨primary_slack_pos hc ⟨rates.primary_pos, rates.primary_lt_one⟩
    rates.secondary_pos rates.secondary_lt_primary rates.secondary_zero,
    secondary_slack_pos hc ⟨rates.primary_pos, rates.primary_lt_one⟩ rates.secondary_zero⟩

theorem phaseA_endpointNash (hc : c ∈ Set.Icc (1 : ℝ) 2) :
    IsεQuittingRootEndpointNash (reward c) rates.phaseBValue 0 rates.phaseARoot := by
  have hquiet := rates.quiet_slacks_pos hc
  intro who
  unfold quittingRootEndpointDifference
  rw [rates.phaseA_quitPayoff, rates.phaseA_continuePayoff]
  fin_cases who <;> simp [phaseARoot, phaseAValue] <;> linarith [hquiet.1, hquiet.2]

theorem phaseB_endpointNash (hc : c ∈ Set.Icc (1 : ℝ) 2) :
    IsεQuittingRootEndpointNash (reward c) rates.phaseAValue 0 rates.phaseBRoot := by
  have hquiet := rates.quiet_slacks_pos hc
  intro who
  unfold quittingRootEndpointDifference
  rw [rates.phaseB_quitPayoff, rates.phaseB_continuePayoff]
  fin_cases who <;> simp [phaseBRoot, phaseBValue] <;> linarith [hquiet.1, hquiet.2]

def cycleRoot : Fin 2 → Player → PMF Bool := ![rates.phaseARoot, rates.phaseBRoot]

def cycleValue : Fin 2 → Payoff Player := ![rates.phaseAValue, rates.phaseBValue]

theorem cycle_policy (phase : Fin 2) :
    rates.cycleValue phase = quittingRootSuccessorPayoff (reward c)
      (rates.cycleValue (finRotate 2 phase)) (rates.cycleRoot phase) := by
  fin_cases phase
  · simpa [cycleRoot, cycleValue] using rates.phaseA_successor
  · simpa [cycleRoot, cycleValue] using rates.phaseB_successor

theorem cycle_rootNash (hc : c ∈ Set.Icc (1 : ℝ) 2) (phase : Fin 2) :
    IsεQuittingRootNash (reward c) (rates.cycleValue (finRotate 2 phase)) 0
      (rates.cycleRoot phase) := by
  apply (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash _ _ _).mp
  fin_cases phase
  · simpa [cycleRoot, cycleValue] using rates.phaseA_endpointNash hc
  · simpa [cycleRoot, cycleValue] using rates.phaseB_endpointNash hc

/-- Actual player-deleted survival over a whole two-phase cycle. -/
theorem cycle_opponentMass (who : Player) :
    (∏ phase : Fin 2,
      quittingStationaryFixedOpponentsContinueMass (rates.cycleRoot phase) who) =
      if who.val < 2 then rates.primary * rates.secondary ^ 2
      else rates.primary ^ 2 * rates.secondary := by
  unfold quittingStationaryFixedOpponentsContinueMass quittingFixedOpponentsContinueMass
  simp_rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  fin_cases who <;>
    simp [cycleRoot, phaseARoot, phaseBRoot, Fin.prod_univ_succ] <;> ring

theorem cycle_contracts (who : Player) :
    (∏ phase : Fin 2,
      quittingStationaryFixedOpponentsContinueMass (rates.cycleRoot phase) who) < 1 := by
  rw [rates.cycle_opponentMass]
  have ha := rates.primary_pos
  have hb := rates.secondary_pos
  have ha1 := rates.primary_lt_one
  have hb1 := rates.secondary_lt_one
  have ha2 : rates.primary ^ 2 < 1 := pow_lt_one₀ ha.le ha1 (by decide)
  have hb2 : rates.secondary ^ 2 < 1 := pow_lt_one₀ hb.le hb1 (by decide)
  split_ifs
  · calc
      rates.primary * rates.secondary ^ 2 ≤ rates.primary * 1 :=
        mul_le_mul_of_nonneg_left hb2.le ha.le
      _ < 1 := by simpa using ha1
  · calc
      rates.primary ^ 2 * rates.secondary ≤ 1 * rates.secondary :=
        mul_le_mul_of_nonneg_right ha2.le hb.le
      _ < 1 := by simpa using hb1

theorem cycle_actualValue :
    rates.cycleValue = quittingCyclicTerminalValue (reward c) rates.cycleRoot :=
  eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff (reward c) rates.cycleRoot
    rates.cycleValue rates.cycle_policy rates.cycle_contracts

/-- The same infinite independent two-phase profile is used at every accuracy. -/
def profile (phase : Fin 2) : (quittingGame (reward c)).BehaviorProfile :=
  quittingCyclicBehaviorProfile (reward c) rates.cycleRoot phase

/-- Exact full behavioral terminal Nash at both initial phases. -/
theorem profile_isExactTerminalNash (hc : c ∈ Set.Icc (1 : ℝ) 2) (phase : Fin 2) :
    (quittingGame (reward c)).IsεAsymptoticNash (quittingTerminalPayoff (reward c)) 0
      (rates.profile phase) :=
  isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate
    (reward c) rates.cycleRoot rates.cycleValue phase rates.cycle_policy
    (rates.cycle_rootNash hc) rates.cycle_contracts

theorem profile_terminalPayoff (phase : Fin 2) :
    quittingTerminalPayoff (reward c) (rates.profile phase) = rates.cycleValue phase := by
  change quittingCyclicTerminalValue (reward c) rates.cycleRoot phase = _
  rw [← rates.cycle_actualValue]

/-- Literal live suffixes rotate the same independent phase roots. -/
theorem profile_suffix (phase : Fin 2) (start : ℕ) :
    quittingRootSequenceProfile (reward c)
      (quittingCyclicRootSequence rates.cycleRoot phase) start =
        rates.profile (quittingCyclicOrbit phase start) := by
  funext who time history
  simp [quittingRootSequenceProfile, profile, quittingCyclicBehaviorProfile,
    quittingCyclicRootSequence_add]
  rfl

theorem allSuffix_isExactTerminalNash (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (phase : Fin 2) (start : ℕ) :
    (quittingGame (reward c)).IsεAsymptoticNash (quittingTerminalPayoff (reward c)) 0
      (quittingRootSequenceProfile (reward c)
        (quittingCyclicRootSequence rates.cycleRoot phase) start) := by
  rw [rates.profile_suffix]
  exact rates.profile_isExactTerminalNash hc _

/-- The full behavioral cap equals the actual phase payoff, including literal Never. -/
theorem profile_completeCap (hc : c ∈ Set.Icc (1 : ℝ) 2) (phase : Fin 2)
    (who : Player) :
    quittingContinuationBestResponseValue (reward c) (rates.profile phase) who =
      rates.cycleValue phase who := by
  apply le_antisymm
  · unfold quittingContinuationBestResponseValue
    apply csSup_le
    · exact ⟨_, rates.profile phase who, rfl⟩
    · rintro value ⟨deviation, rfl⟩
      have hcap := rates.profile_isExactTerminalNash hc phase who deviation
      simpa [rates.profile_terminalPayoff phase] using hcap
  · have hself := quittingTerminalPayoff_update_le_continuationBestResponseValue
      (reward c) (rates.profile phase) who (rates.profile phase who)
    simpa [Function.update_eq_self, rates.profile_terminalPayoff phase] using hself

theorem isUniformEquilibriumPayoff (hc : c ∈ Set.Icc (1 : ℝ) 2) (phase : Fin 2) :
    (quittingGame (reward c)).IsUniformEquilibriumPayoff none (rates.cycleValue phase) := by
  have h := isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate
    (reward c) rates.cycleRoot rates.cycleValue phase rates.cycle_policy
    (rates.cycle_rootNash hc) rates.cycle_contracts
  simpa [← rates.cycle_actualValue] using h

/-- Each accuracy uses this very same literal phase profile at every sufficiently long horizon. -/
theorem profile_uniformPayoffWitness (hc : c ∈ Set.Icc (1 : ℝ) 2) (phase : Fin 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ threshold : ℕ, ∀ horizon, threshold ≤ horizon →
      (quittingGame (reward c)).IsεHorizonNash none horizon ε (rates.profile phase) ∧
        ∀ who, |(quittingGame (reward c)).finiteAveragePayoff none horizon
          (rates.profile phase) who - rates.cycleValue phase who| ≤ ε := by
  have haccept : ∀ δ : ℝ, 0 < δ → ∃ _index : Unit,
      (quittingGame (reward c)).IsεAsymptoticNash (quittingTerminalPayoff (reward c)) δ
        (rates.profile phase) ∧
      ∀ who, |quittingTerminalPayoff (reward c) (rates.profile phase) who -
        rates.cycleValue phase who| ≤ δ := by
    intro δ hδ
    refine ⟨(), (rates.profile_isExactTerminalNash hc phase).mono hδ.le, ?_⟩
    intro who
    rw [rates.profile_terminalPayoff]
    simpa using hδ.le
  obtain ⟨_index, threshold, hthreshold⟩ :=
    quittingGame_uniformPayoffWitnesses_of_terminalTargetAcceptance_family
      (reward c) (rates.cycleValue phase) (fun _ : Unit => rates.profile phase)
      haccept ε hε
  exact ⟨threshold, hthreshold⟩

end PeriodicRates

/-- The rates and exact periodic fixed target are both produced from the input parameter. -/
theorem exists_periodicUniformPayoff {c : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2) :
    ∃ rates : PeriodicRates c,
      (quittingGame (reward c)).IsUniformEquilibriumPayoff none rates.phaseAValue := by
  obtain ⟨rates⟩ := exists_periodicRates hc
  exact ⟨rates, rates.isUniformEquilibriumPayoff hc 0⟩

end GameTheory.PairedCollisionReward

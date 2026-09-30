/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Examples.BlockPair.PairedCollisionRewardPeriodic
import UniformEquilibrium.Quitting.Examples.BlockPair.PairedCollisionRewardBoundary
import UniformEquilibrium.Quitting.Classification.AbnormalPlayers
import UniformEquilibrium.Quitting.Cycles.PairedCycleStoppingLaws
import UniformEquilibrium.Quitting.Terminal.FiniteDeadlineHorizonError

/-!
# Exact independent finite calendars for the paired-collision reward family

The rates and phase-A target are fixed before the truncation count. Literal
whole-cycle censoring preserves the full behavioral cap exactly, including
after-support quitting dates and Never. The finite timing-law realization
preserves the complete terminal semantic pair, not just its finite menu.
-/

noncomputable section

namespace GameTheory.PairedCollisionReward

open Filter StochasticGame _root_.Math.Probability
open _root_.Math.PairedPhasePolynomialRoots
open scoped BigOperators Topology

/-- Punishment normality uses the actual all-Never punishment plan and unit solo exit. -/
theorem normalPlayer (c : ℝ) (who : Player) : IsQuittingNormalPlayer (reward c) who := by
  change quittingPunishmentValue (reward c) who ≤ quittingSoloReward (reward c) who who
  simpa using punishmentValue_le_one c who

/-- Phase zero activates `0,2`, and phase one activates `1,3`. -/
def calendarSchedule : PairedCycle.Schedule Player 2 where
  label :=
    { toFun := fun pair => ⟨pair.1.val + if pair.2 then 2 else 0, by
        have hphase := pair.1.isLt
        cases pair.2 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩
      invFun := fun who => (⟨who.val % 2, Nat.mod_lt _ (by decide)⟩, decide (2 ≤ who.val))
      left_inv := by
        rintro ⟨phase, side⟩
        fin_cases phase <;> cases side <;> rfl
      right_inv := by
        intro who
        fin_cases who <;> rfl }

namespace PeriodicRates

variable {c : ℝ} (rates : PeriodicRates c)

def ownContinue (who : Player) : ℝ :=
  if who.val < 2 then rates.primary else rates.secondary

def calendarHazard (who : Player) : ℝ := 1 - rates.ownContinue who

theorem ownContinue_pos (who : Player) : 0 < rates.ownContinue who := by
  unfold ownContinue
  split_ifs
  · exact rates.primary_pos
  · exact rates.secondary_pos

theorem ownContinue_lt_one (who : Player) : rates.ownContinue who < 1 := by
  unfold ownContinue
  split_ifs
  · exact rates.primary_lt_one
  · exact rates.secondary_lt_one

theorem calendarHazard_unit (who : Player) :
    rates.calendarHazard who ∈ Set.Icc (0 : ℝ) 1 := by
  unfold calendarHazard
  constructor
  · linarith [rates.ownContinue_lt_one who]
  · linarith [rates.ownContinue_pos who]

theorem cycleRoot_eq_calendar : rates.cycleRoot =
    PairedCycle.cycle calendarSchedule rates.calendarHazard rates.calendarHazard_unit := by
  funext phase who
  fin_cases phase <;> fin_cases who <;>
    simp [cycleRoot, phaseARoot, phaseBRoot, PairedCycle.cycle, PairedCycle.root,
      PairedCycle.Schedule.first, PairedCycle.Schedule.second, calendarSchedule,
      calendarHazard, ownContinue, primaryCoin, secondaryCoin, commonCoin]

def firstActiveDate (who : Player) : ℕ := who.val % 2

theorem firstActiveDate_eq_calendar (who : Player) :
    firstActiveDate who = PairedCycle.firstActiveTime calendarSchedule 0 who := by
  fin_cases who <;> decide

/-- Keep exactly `cycles` whole cycles and then Continue forever. -/
def finiteProfile (cycles : ℕ) : (quittingGame (reward c)).BehaviorProfile :=
  quittingCyclicFiniteProfile (reward c) rates.cycleRoot 0 (cycles * 2)

def jointCycleMass : ℝ := rates.primary ^ 2 * rates.secondary ^ 2

theorem jointCycleMass_nonneg : 0 ≤ rates.jointCycleMass := by
  unfold jointCycleMass
  positivity

theorem jointCycleMass_eq :
    (∏ phase, quittingStationaryContinueMass (rates.cycleRoot phase)) =
      rates.jointCycleMass := by
  simp_rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  simp [cycleRoot, phaseARoot, phaseBRoot, jointCycleMass, Fin.prod_univ_succ]
  ring

theorem cycleValue_bounds (hc : c ∈ Set.Icc (1 : ℝ) 2) (phase : Fin 2) (who : Player) :
    1 ≤ rates.cycleValue phase who ∧ rates.cycleValue phase who < 8 := by
  have hP := affineEndpoint_bounds hc ⟨rates.secondary_pos.le, rates.secondary_lt_one.le⟩
  have hR := affineEndpoint_bounds hc ⟨rates.primary_pos.le, rates.primary_lt_one.le⟩
  have hPb : 1 ≤ affineEndpoint c rates.secondary / rates.secondary := by
    apply (le_div_iff₀ rates.secondary_pos).mpr
    linarith [rates.secondary_lt_one, hP.1]
  have hRa : 1 ≤ affineEndpoint c rates.primary / rates.primary := by
    apply (le_div_iff₀ rates.primary_pos).mpr
    linarith [rates.primary_lt_one, hR.1]
  have hPb8 : affineEndpoint c rates.secondary / rates.secondary < 8 := by
    apply (div_lt_iff₀ rates.secondary_pos).mpr
    linarith [rates.quarter_lt, hP.2]
  have hRa8 : affineEndpoint c rates.primary / rates.primary < 8 := by
    apply (div_lt_iff₀ rates.primary_pos).mpr
    linarith [rates.half_lt, hR.2]
  fin_cases phase <;> fin_cases who <;>
    simp [cycleValue, phaseAValue, phaseBValue] <;>
    constructor <;> linarith [hP.1, hP.2, hR.1, hR.2]

/-- The exact renewal identity of the actual censored profile. -/
theorem finiteProfile_payoff_eq (cycles : ℕ) (who : Player) :
    quittingTerminalPayoff (reward c) (rates.finiteProfile cycles) who =
      (1 - rates.jointCycleMass ^ cycles) * rates.phaseAValue who := by
  rw [finiteProfile, quittingTerminalPayoff_cyclicFiniteProfile_mul_card,
    rates.jointCycleMass_eq, ← rates.cycle_actualValue]
  rfl

/-- A legal retained first active date attains the infinite target exactly. -/
theorem finiteProfile_firstActive_attains (cycles : ℕ) (hcycles : 1 ≤ cycles)
    (who : Player) :
    quittingTerminalPayoff (reward c)
        (Function.update (rates.finiteProfile cycles) who
          (quittingPureTimeBehaviorStrategy (reward c) who
            (some (firstActiveDate who)))) who = rates.phaseAValue who := by
  apply quittingTerminalPayoff_cyclicWord_pureTime_eq (reward c) rates.cycleRoot
    rates.cycleValue (quittingAlwaysContinueProfile (reward c)) 0 (cycles * 2)
      (firstActiveDate who) who
  · have hdate : firstActiveDate who < 2 := Nat.mod_lt _ (by decide)
    omega
  · intro offset hoff
    have hoffzero : offset = 0 := by
      have hdate : firstActiveDate who < 2 := Nat.mod_lt _ (by decide)
      omega
    subst offset
    simpa [cycleRoot, cycleValue, quittingCyclicOrbit_zero] using
      rates.phaseA_continuePayoff who
  · have hA (player : Player) := rates.phaseA_quitPayoff player
    have hB (player : Player) := rates.phaseB_quitPayoff player
    simp_rw [← quittingRootQuitPayoff_continuation_invariant
      (reward c) 0 rates.phaseBValue rates.phaseARoot] at hA
    simp_rw [← quittingRootQuitPayoff_continuation_invariant
      (reward c) 0 rates.phaseAValue rates.phaseBRoot] at hB
    fin_cases who
    · simpa [cycleRoot, cycleValue, firstActiveDate, quittingCyclicOrbit, phaseAValue]
        using hA 0
    · simpa [cycleRoot, cycleValue, firstActiveDate, quittingCyclicOrbit, phaseBValue]
        using hB 1
    · simpa [cycleRoot, cycleValue, firstActiveDate, quittingCyclicOrbit, phaseAValue]
        using hA 2
    · simpa [cycleRoot, cycleValue, firstActiveDate, quittingCyclicOrbit, phaseBValue]
        using hB 3

/-- This equality is for the full behavioral supremum, including late dates and Never. -/
theorem finiteProfile_completeCap (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (cycles : ℕ) (hcycles : 1 ≤ cycles) (who : Player) :
    quittingContinuationBestResponseValue (reward c) (rates.finiteProfile cycles) who =
      rates.phaseAValue who := by
  apply le_antisymm
  · have htail : max 0 (reward c (quittingSingletonTerminal who) who) ≤
        quittingCyclicTerminalValue (reward c) rates.cycleRoot
          (quittingCyclicOrbit 0 (cycles * 2)) who := by
      rw [← rates.cycle_actualValue]
      have hvalue := (rates.cycleValue_bounds hc (quittingCyclicOrbit 0 (cycles * 2)) who).1
      have hsolo : reward c (quittingSingletonTerminal who) who = 1 := unitSoloExit c who
      simpa only [hsolo, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)] using hvalue
    have h := quittingContinuationBestResponseValue_cyclicFiniteProfile_le (reward c)
      rates.cycleRoot
      (by simpa only [← rates.cycle_actualValue] using rates.cycle_rootNash hc)
      0 (cycles * 2) who htail
    simpa only [← rates.cycle_actualValue, finiteProfile, cycleValue,
      Matrix.cons_val_zero] using h
  · rw [← rates.finiteProfile_firstActive_attains cycles hcycles who]
    exact quittingTerminalPayoff_update_le_continuationBestResponseValue
      (reward c) (rates.finiteProfile cycles) who _

theorem finiteProfile_debt_eq (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (cycles : ℕ) (hcycles : 1 ≤ cycles) (who : Player) :
    quittingTerminalDeviationDebt (reward c) (rates.finiteProfile cycles) who =
      rates.jointCycleMass ^ cycles * rates.phaseAValue who := by
  rw [quittingTerminalDeviationDebt, rates.finiteProfile_completeCap hc cycles hcycles,
    rates.finiteProfile_payoff_eq]
  ring

theorem finiteProfile_exploitability_eq (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (cycles : ℕ) (hcycles : 1 ≤ cycles) :
    quittingTerminalExploitability (reward c) (rates.finiteProfile cycles) =
      rates.jointCycleMass ^ cycles *
        QuittingBoundaryHolonomy.finitePlayerMax rates.phaseAValue := by
  rw [quittingTerminalExploitability_eq_max_debt]
  simp_rw [rates.finiteProfile_debt_eq hc cycles hcycles]
  simpa only [QuittingBoundaryHolonomy.finitePlayerMax, zero_add] using
    Math.sup'_affine_of_nonneg rates.phaseAValue 0 (rates.jointCycleMass ^ cycles)
      (pow_nonneg rates.jointCycleMass_nonneg cycles)

theorem jointCycleMass_le_geometric : rates.jointCycleMass ≤ (9 / 10 : ℝ) ^ 4 := by
  have ha := pow_le_pow_left₀ rates.primary_pos.le rates.primary_lt.le 2
  have hb := pow_le_pow_left₀ rates.secondary_pos.le
    (rates.secondary_lt_primary.trans rates.primary_lt).le 2
  have hprod := mul_le_mul ha hb (sq_nonneg rates.secondary) (by positivity)
  calc
    rates.jointCycleMass ≤ (9 / 10 : ℝ) ^ 2 * (9 / 10 : ℝ) ^ 2 := hprod
    _ = _ := by ring

theorem finiteProfile_exploitability_le_geometric (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (cycles : ℕ) (hcycles : 1 ≤ cycles) :
    quittingTerminalExploitability (reward c) (rates.finiteProfile cycles) ≤
      8 * (9 / 10 : ℝ) ^ (4 * cycles) := by
  rw [rates.finiteProfile_exploitability_eq hc cycles hcycles]
  have hmax : QuittingBoundaryHolonomy.finitePlayerMax rates.phaseAValue ≤ 8 := by
    apply QuittingBoundaryHolonomy.finitePlayerMax_le
    intro who
    exact (rates.cycleValue_bounds hc 0 who).2.le
  have hpow := pow_le_pow_left₀ rates.jointCycleMass_nonneg
    rates.jointCycleMass_le_geometric cycles
  rw [← pow_mul] at hpow
  calc
    _ ≤ rates.jointCycleMass ^ cycles * 8 :=
      mul_le_mul_of_nonneg_left hmax (pow_nonneg rates.jointCycleMass_nonneg cycles)
    _ ≤ _ := by nlinarith

theorem finiteProfile_debt_le_geometric (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (cycles : ℕ) (hcycles : 1 ≤ cycles) (who : Player) :
    quittingTerminalDeviationDebt (reward c) (rates.finiteProfile cycles) who ≤
      8 * (9 / 10 : ℝ) ^ (4 * cycles) :=
  (quittingTerminalDeviationDebt_le_exploitability
    (reward c) (rates.finiteProfile cycles) who).trans
    (rates.finiteProfile_exploitability_le_geometric hc cycles hcycles)

theorem finiteProfile_isGeometricNash (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (cycles : ℕ) (hcycles : 1 ≤ cycles) :
    (quittingGame (reward c)).IsεAsymptoticNash (quittingTerminalPayoff (reward c))
      (8 * (9 / 10 : ℝ) ^ (4 * cycles)) (rates.finiteProfile cycles) :=
  isεAsymptoticNash_of_quittingTerminalExploitability_le (rates.finiteProfile cycles)
    (rates.finiteProfile_exploitability_le_geometric hc cycles hcycles)

/-- Each retained independent marginal has the packet's literal geometric atom. -/
theorem finiteStoppingLaw_active_toReal (cycles turn : ℕ) (hturn : turn < cycles)
    (who : Player) :
    (quittingBehaviorStoppingLaw (reward c) (rates.finiteProfile cycles who)
      (some (2 * turn + firstActiveDate who))).toReal =
        (1 - rates.ownContinue who) * rates.ownContinue who ^ turn := by
  rw [finiteProfile, rates.cycleRoot_eq_calendar, firstActiveDate_eq_calendar]
  have h := PairedCycle.finiteStoppingLaw_activeDate_toReal (reward c) calendarSchedule
    rates.calendarHazard rates.calendarHazard_unit 0 cycles turn hturn who
  simpa only [calendarHazard, sub_sub_cancel, Nat.mul_comm turn 2] using h

theorem finiteStoppingLaw_none_toReal (cycles : ℕ) (who : Player) :
    (quittingBehaviorStoppingLaw (reward c) (rates.finiteProfile cycles who) none).toReal =
      rates.ownContinue who ^ cycles := by
  cases cycles with
  | zero =>
      change (quittingBehaviorStoppingLaw (reward c)
        (quittingPureTimeBehaviorStrategy (reward c) who none) none).toReal = _
      rw [quittingBehaviorStoppingLaw_pureTime_never]
      simp
  | succ cycles =>
      rw [finiteProfile, rates.cycleRoot_eq_calendar]
      simpa only [calendarHazard, sub_sub_cancel] using
        PairedCycle.finiteStoppingLaw_none_toReal (reward c) calendarSchedule
          rates.calendarHazard rates.calendarHazard_unit 0 (cycles + 1) (by omega) who

theorem finiteStoppingLaw_late_or_inactive (cycles time : ℕ) (who : Player)
    (htime : time % 2 ≠ firstActiveDate who ∨ cycles * 2 ≤ time) :
    quittingBehaviorStoppingLaw (reward c) (rates.finiteProfile cycles who) (some time) = 0 := by
  rw [finiteProfile, rates.cycleRoot_eq_calendar]
  apply PairedCycle.finiteStoppingLaw_some_eq_zero_of_inactive_or_late (reward c)
    calendarSchedule rates.calendarHazard rates.calendarHazard_unit 0 cycles time who
  rcases htime with hinactive | hlate
  · left
    intro heq
    apply hinactive
    have hval := congrArg Fin.val heq
    simpa [quittingCyclicOrbit, PairedCycle.Schedule.phase, calendarSchedule,
      firstActiveDate] using hval
  · exact Or.inr hlate

/-- Censoring is marginal, hence does not couple the four players' private draws. -/
theorem finiteStoppingLaw_eq_censor (cycles : ℕ) (hcycles : 1 ≤ cycles) (who : Player) :
    quittingBehaviorStoppingLaw (reward c) (rates.finiteProfile cycles who) =
      censorLateFiniteStoppingLaw
        (quittingBehaviorStoppingLaw (reward c) (rates.profile 0 who)) (cycles * 2 - 1) := by
  rw [finiteProfile, quittingCyclicFiniteProfile_eq_truncatedRootProfile]
  exact quittingBehaviorStoppingLaw_truncatedRoots_eq_censor (reward c)
    (quittingCyclicRootSequence rates.cycleRoot 0) (cycles * 2) (by omega) who

/-- Actual finite-date-or-Never laws realize the same full semantic pair and
every complete pure-date response, not just the retained dates. -/
theorem exists_finiteTimingLaws_exact (cycles : ℕ) :
    ∃ mixed : Player → PMF (QuittingFiniteDeadlineTimingAction (cycles * 2)),
      (∀ who, (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF =
        quittingBehaviorStoppingLaw (reward c) (rates.finiteProfile cycles who)) ∧
      quittingTerminalSemanticPair (reward c)
          (quittingFiniteDeadlineTimingProfile (reward c) (cycles * 2) mixed) =
        quittingTerminalSemanticPair (reward c) (rates.finiteProfile cycles) ∧
      ∀ who choice, quittingTerminalPayoff (reward c)
          (Function.update
            (quittingFiniteDeadlineTimingProfile (reward c) (cycles * 2) mixed) who
            (quittingPureTimeBehaviorStrategy (reward c) who choice)) who =
        quittingTerminalPayoff (reward c)
          (Function.update (rates.finiteProfile cycles) who
            (quittingPureTimeBehaviorStrategy (reward c) who choice)) who :=
  exists_finiteDeadlineTimingProfile_cyclicFinite_exact
    (reward c) rates.cycleRoot 0 (cycles * 2)

/-- The literal finite laws retain Never and the displayed geometric active atoms. -/
theorem exists_finiteTimingLaws_with_masses (cycles : ℕ) :
    ∃ mixed : Player → PMF (QuittingFiniteDeadlineTimingAction (cycles * 2)),
      (∀ who, (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF =
        quittingBehaviorStoppingLaw (reward c) (rates.finiteProfile cycles who)) ∧
      quittingTerminalSemanticPair (reward c)
          (quittingFiniteDeadlineTimingProfile (reward c) (cycles * 2) mixed) =
        quittingTerminalSemanticPair (reward c) (rates.finiteProfile cycles) ∧
      (∀ who, ((quittingFiniteDeadlineTimingLaw (mixed who)).toPMF none).toReal =
        rates.ownContinue who ^ cycles) ∧
      (∀ who turn, turn < cycles →
        ((quittingFiniteDeadlineTimingLaw (mixed who)).toPMF
          (some (2 * turn + firstActiveDate who))).toReal =
            (1 - rates.ownContinue who) * rates.ownContinue who ^ turn) ∧
      ∀ who time, time % 2 ≠ firstActiveDate who ∨ cycles * 2 ≤ time →
        (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF (some time) = 0 := by
  obtain ⟨mixed, hlaw, hpair, _⟩ := rates.exists_finiteTimingLaws_exact cycles
  refine ⟨mixed, hlaw, hpair, ?_, ?_, ?_⟩
  · intro who
    rw [hlaw who]
    exact rates.finiteStoppingLaw_none_toReal cycles who
  · intro who turn hturn
    rw [hlaw who]
    exact rates.finiteStoppingLaw_active_toReal cycles turn hturn who
  · intro who time htime
    rw [hlaw who]
    exact rates.finiteStoppingLaw_late_or_inactive cycles time who htime

/-- The actual finite profile is quiet at every history after its cutoff. -/
theorem finiteProfile_quiet (cycles later : ℕ) (hlater : cycles * 2 ≤ later) :
    quittingProfileLiveRoot (reward c) (rates.finiteProfile cycles) later =
      quittingAllContinueRoot := by
  funext who
  change rates.finiteProfile cycles who later (quittingLiveHist (reward c) later) =
    PMF.pure false
  rw [finiteProfile, quittingCyclicFiniteProfile_apply, ite_eq_right (by omega)]

theorem abs_reward_le_four (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (terminal : {S : Finset Player // S.Nonempty}) (who : Player) :
    |reward c terminal who| ≤ 4 := by
  have hc0 : 0 ≤ c := by linarith [hc.1]
  fin_cases terminal <;> fin_cases who <;>
    simp [reward, abs_of_nonneg hc0] <;> linarith [hc.2]

/-- Signed-safe prescribed delivery for the finite profile, without infinite-tail contraction. -/
theorem finiteProfile_horizonDelivery (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (cycles horizon : ℕ) (hhorizon : 0 < horizon) (who : Player) :
    |(quittingGame (reward c)).finiteAveragePayoff none horizon
        (rates.finiteProfile cycles) who -
      quittingTerminalPayoff (reward c) (rates.finiteProfile cycles) who| ≤
        8 * cycles / horizon := by
  have h := abs_finiteAveragePayoff_sub_terminal_quietAfterDeadline_le
    (reward c) (cycles * 2) horizon (rates.finiteProfile cycles)
    (rates.finiteProfile_quiet cycles) who (fun terminal => abs_reward_le_four hc terminal who)
      hhorizon
  have hboundary : (4 : ℝ) * (cycles * 2 : ℕ) / (horizon : ℝ) =
      8 * (cycles : ℝ) / (horizon : ℝ) := by push_cast; ring
  rw [hboundary] at h
  exact h

/-- Every actual behavioral replacement is below its own terminal payoff plus `8K/N`.
Only its own singleton is nonnegative; all other coordinates retain their signs. -/
theorem finiteProfile_horizonDeviation (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (cycles horizon : ℕ) (hhorizon : 0 < horizon) (who : Player)
    (deviation : (quittingGame (reward c)).BehaviorStrategy who) :
    (quittingGame (reward c)).finiteAveragePayoff none horizon
        (Function.update (rates.finiteProfile cycles) who deviation) who ≤
      quittingTerminalPayoff (reward c)
          (Function.update (rates.finiteProfile cycles) who deviation) who +
        8 * cycles / horizon := by
  have hsolo : 0 ≤ reward c (quittingSingletonTerminal who) who := by
    change 0 ≤ quittingSoloReward (reward c) who who
    simp
  have h := finiteAveragePayoff_update_quietAfterDeadline_le_terminal_add
    (reward c) (cycles * 2) horizon (rates.finiteProfile cycles)
    (rates.finiteProfile_quiet cycles) who deviation
    (fun terminal => abs_reward_le_four hc terminal who) hsolo hhorizon
  have hboundary : (4 : ℝ) * (cycles * 2 : ℕ) / (horizon : ℝ) =
      8 * (cycles : ℝ) / (horizon : ℝ) := by push_cast; ring
  rw [hboundary] at h
  exact h

theorem finiteProfile_horizonRegret_le_debt (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (cycles horizon : ℕ) (hhorizon : 0 < horizon) (who : Player)
    (deviation : (quittingGame (reward c)).BehaviorStrategy who) :
    (quittingGame (reward c)).finiteAveragePayoff none horizon
        (Function.update (rates.finiteProfile cycles) who deviation) who -
      (quittingGame (reward c)).finiteAveragePayoff none horizon
        (rates.finiteProfile cycles) who ≤
      quittingTerminalDeviationDebt (reward c) (rates.finiteProfile cycles) who +
        16 * cycles / horizon := by
  have hdev := rates.finiteProfile_horizonDeviation hc cycles horizon hhorizon who deviation
  have hon := (abs_le.mp
    (rates.finiteProfile_horizonDelivery hc cycles horizon hhorizon who)).1
  have hcap := quittingTerminalPayoff_update_le_continuationBestResponseValue
    (reward c) (rates.finiteProfile cycles) who deviation
  have hboundary : (16 : ℝ) * cycles / horizon = 2 * (8 * cycles / horizon) := by ring
  rw [hboundary, quittingTerminalDeviationDebt]
  linarith

theorem finiteProfile_horizonRegret (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (cycles horizon : ℕ) (hhorizon : 0 < horizon) (who : Player)
    (deviation : (quittingGame (reward c)).BehaviorStrategy who) :
    (quittingGame (reward c)).finiteAveragePayoff none horizon
        (Function.update (rates.finiteProfile cycles) who deviation) who -
      (quittingGame (reward c)).finiteAveragePayoff none horizon
        (rates.finiteProfile cycles) who ≤
      quittingTerminalExploitability (reward c) (rates.finiteProfile cycles) +
        16 * cycles / horizon :=
  (rates.finiteProfile_horizonRegret_le_debt hc cycles horizon hhorizon who deviation).trans
    (_root_.add_le_add (quittingTerminalDeviationDebt_le_exploitability
      (reward c) (rates.finiteProfile cycles) who) le_rfl)

theorem finiteProfile_horizonNash (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (cycles horizon : ℕ) (hhorizon : 0 < horizon) :
    (quittingGame (reward c)).IsεHorizonNash none horizon
      (quittingTerminalExploitability (reward c) (rates.finiteProfile cycles) +
        16 * cycles / horizon) (rates.finiteProfile cycles) := by
  intro who deviation
  have h := rates.finiteProfile_horizonRegret hc cycles horizon hhorizon who deviation
  linarith

theorem finiteProfile_horizonNash_geometric (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (cycles : ℕ) (hcycles : 1 ≤ cycles) (horizon : ℕ) (hhorizon : 0 < horizon) :
    (quittingGame (reward c)).IsεHorizonNash none horizon
      (8 * (9 / 10 : ℝ) ^ (4 * cycles) + 16 * cycles / horizon)
      (rates.finiteProfile cycles) :=
  (rates.finiteProfile_horizonNash hc cycles horizon hhorizon).mono
    (_root_.add_le_add (rates.finiteProfile_exploitability_le_geometric hc cycles hcycles)
      le_rfl)

theorem finiteProfile_targetError_eq (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (cycles : ℕ) (who : Player) :
    |quittingTerminalPayoff (reward c) (rates.finiteProfile cycles) who -
      rates.phaseAValue who| = rates.jointCycleMass ^ cycles * rates.phaseAValue who := by
  rw [rates.finiteProfile_payoff_eq]
  have hvalue : 0 ≤ rates.phaseAValue who := by
    have h := (rates.cycleValue_bounds hc 0 who).1
    change 1 ≤ rates.phaseAValue who at h
    linarith
  rw [show (1 - rates.jointCycleMass ^ cycles) * rates.phaseAValue who -
      rates.phaseAValue who = -(rates.jointCycleMass ^ cycles * rates.phaseAValue who)
      by ring, abs_neg, abs_of_nonneg
        (mul_nonneg (pow_nonneg rates.jointCycleMass_nonneg cycles) hvalue)]

theorem finiteProfile_horizonTargetDelivery (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (cycles : ℕ) (hcycles : 1 ≤ cycles) (horizon : ℕ) (hhorizon : 0 < horizon)
    (who : Player) :
    |(quittingGame (reward c)).finiteAveragePayoff none horizon
        (rates.finiteProfile cycles) who - rates.phaseAValue who| ≤
      quittingTerminalExploitability (reward c) (rates.finiteProfile cycles) +
        8 * cycles / horizon := by
  have htarget : |quittingTerminalPayoff (reward c) (rates.finiteProfile cycles) who -
      rates.phaseAValue who| ≤
        quittingTerminalExploitability (reward c) (rates.finiteProfile cycles) := by
    rw [rates.finiteProfile_targetError_eq hc,
      ← rates.finiteProfile_debt_eq hc cycles hcycles who]
    exact quittingTerminalDeviationDebt_le_exploitability
      (reward c) (rates.finiteProfile cycles) who
  have htriangle := abs_sub_le
    ((quittingGame (reward c)).finiteAveragePayoff none horizon (rates.finiteProfile cycles) who)
    (quittingTerminalPayoff (reward c) (rates.finiteProfile cycles) who) (rates.phaseAValue who)
  have hon := rates.finiteProfile_horizonDelivery hc cycles horizon hhorizon who
  linarith

/-- One positive whole-cycle count attains every requested terminal accuracy. -/
theorem exists_cycles_geometric_le (error : ℝ) (herror : 0 < error) :
    ∃ cycles : ℕ, 1 ≤ cycles ∧ 8 * (9 / 10 : ℝ) ^ (4 * cycles) ≤ error := by
  have hbase : (9 / 10 : ℝ) ^ 4 < 1 := by norm_num
  have htendsto : Tendsto (fun cycles : ℕ => 8 * (9 / 10 : ℝ) ^ (4 * cycles))
      atTop (𝓝 0) := by
    simpa only [pow_mul, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (show 0 ≤ (9 / 10 : ℝ) ^ 4 by positivity) hbase).const_mul (8 : ℝ)
  obtain ⟨threshold, hthreshold⟩ :=
    eventually_atTop.mp (htendsto.eventually (gt_mem_nhds herror))
  refine ⟨max 1 threshold, Nat.le_max_left _ _, ?_⟩
  exact (hthreshold _ (Nat.le_max_right _ _)).le

/-- The printed threshold controls the finite-support boundary charge. -/
theorem horizonBoundary_le_half (cycles horizon : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hhorizon : max 1 ⌈32 * (cycles : ℝ) / ε⌉₊ ≤ horizon) :
    0 < horizon ∧ 16 * (cycles : ℝ) / horizon ≤ ε / 2 := by
  have hpos : 0 < horizon := by omega
  have hhorizonReal : (0 : ℝ) < horizon := by exact_mod_cast hpos
  have hceil : (⌈32 * (cycles : ℝ) / ε⌉₊ : ℝ) ≤ horizon := by
    exact_mod_cast (Nat.le_max_right _ _).trans hhorizon
  have hscaled : 32 * (cycles : ℝ) ≤ ε * horizon := by
    have hquot := (Nat.le_ceil (32 * (cycles : ℝ) / ε)).trans hceil
    have hmul := (div_le_iff₀ hε).mp hquot
    nlinarith
  refine ⟨hpos, (div_le_iff₀ hhorizonReal).mpr ?_⟩
  nlinarith

/-- The rates and target are unchanged when the finite count and horizon accuracy change. -/
theorem finiteProfile_uniformPayoffWitness (hc : c ∈ Set.Icc (1 : ℝ) 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ cycles : ℕ, 1 ≤ cycles ∧
      quittingTerminalExploitability (reward c) (rates.finiteProfile cycles) ≤ ε / 2 ∧
      ∀ horizon, max 1 ⌈32 * (cycles : ℝ) / ε⌉₊ ≤ horizon →
        (quittingGame (reward c)).IsεHorizonNash none horizon ε (rates.finiteProfile cycles) ∧
        ∀ who, |(quittingGame (reward c)).finiteAveragePayoff none horizon
          (rates.finiteProfile cycles) who - rates.phaseAValue who| ≤ ε := by
  obtain ⟨cycles, hcycles, herror⟩ := exists_cycles_geometric_le (ε / 2) (by positivity)
  have hterminal := (rates.finiteProfile_exploitability_le_geometric hc cycles hcycles).trans
    herror
  refine ⟨cycles, hcycles, hterminal, fun horizon hhorizon => ?_⟩
  obtain ⟨hpositive, hboundary⟩ := horizonBoundary_le_half cycles horizon hε hhorizon
  have hsmall : 8 * (cycles : ℝ) / horizon ≤ 16 * (cycles : ℝ) / horizon := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hcyclesReal : (0 : ℝ) ≤ cycles := Nat.cast_nonneg cycles
    nlinarith
  refine ⟨?_, ?_⟩
  · intro who deviation
    have h := rates.finiteProfile_horizonRegret hc cycles horizon hpositive who deviation
    linarith
  · intro who
    have h := rates.finiteProfile_horizonTargetDelivery hc cycles hcycles horizon hpositive who
    linarith

/-- One actual independent finite-date-or-Never witness, at the fixed rate/target pair. -/
def FiniteCalendarAccuracy (ε : ℝ) : Prop :=
  ∃ cycles : ℕ, 1 ≤ cycles ∧
    ∃ mixed : Player → PMF (QuittingFiniteDeadlineTimingAction (cycles * 2)),
      (∀ who, (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF =
        quittingBehaviorStoppingLaw (reward c) (rates.finiteProfile cycles who)) ∧
      quittingTerminalSemanticPair (reward c)
          (quittingFiniteDeadlineTimingProfile (reward c) (cycles * 2) mixed) =
        quittingTerminalSemanticPair (reward c) (rates.finiteProfile cycles) ∧
      (∀ who, ((quittingFiniteDeadlineTimingLaw (mixed who)).toPMF none).toReal =
        rates.ownContinue who ^ cycles) ∧
      (∀ who turn, turn < cycles →
        ((quittingFiniteDeadlineTimingLaw (mixed who)).toPMF
          (some (2 * turn + firstActiveDate who))).toReal =
            (1 - rates.ownContinue who) * rates.ownContinue who ^ turn) ∧
      (∀ who time, time % 2 ≠ firstActiveDate who ∨ cycles * 2 ≤ time →
        (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF (some time) = 0) ∧
      quittingTerminalExploitability (reward c)
        (quittingFiniteDeadlineTimingProfile (reward c) (cycles * 2) mixed) ≤ ε / 2 ∧
      ∀ horizon, max 1 ⌈32 * (cycles : ℝ) / ε⌉₊ ≤ horizon →
        (quittingGame (reward c)).IsεHorizonNash none horizon ε
          (quittingFiniteDeadlineTimingProfile (reward c) (cycles * 2) mixed) ∧
        ∀ who, |(quittingGame (reward c)).finiteAveragePayoff none horizon
          (quittingFiniteDeadlineTimingProfile (reward c) (cycles * 2) mixed) who -
            rates.phaseAValue who| ≤ ε

/-- The reconstructed finite timing laws themselves satisfy every sufficiently long
horizon inequality, not merely a different profile with the same terminal payoff. -/
theorem finiteTiming_uniformPayoffWitness (hc : c ∈ Set.Icc (1 : ℝ) 2)
    {ε : ℝ} (hε : 0 < ε) : rates.FiniteCalendarAccuracy ε := by
  obtain ⟨cycles, hcycles, hterminal, _⟩ := rates.finiteProfile_uniformPayoffWitness hc hε
  obtain ⟨mixed, hlaw, hpair, hnever, hatom, hzero⟩ :=
    rates.exists_finiteTimingLaws_with_masses cycles
  have hpay : quittingTerminalPayoff (reward c)
      (quittingFiniteDeadlineTimingProfile (reward c) (cycles * 2) mixed) =
      quittingTerminalPayoff (reward c) (rates.finiteProfile cycles) :=
    congrArg Prod.fst hpair
  have hcap : (fun who => quittingContinuationBestResponseValue (reward c)
      (quittingFiniteDeadlineTimingProfile (reward c) (cycles * 2) mixed) who) =
      fun who => quittingContinuationBestResponseValue (reward c)
        (rates.finiteProfile cycles) who := congrArg Prod.snd hpair
  have hexploit : quittingTerminalExploitability (reward c)
      (quittingFiniteDeadlineTimingProfile (reward c) (cycles * 2) mixed) =
      quittingTerminalExploitability (reward c) (rates.finiteProfile cycles) := by
    unfold quittingTerminalExploitability
    apply congrArg QuittingBoundaryHolonomy.finitePlayerMax
    funext who
    rw [congrFun hpay who, congrFun hcap who]
  have htimingError : quittingTerminalExploitability (reward c)
      (quittingFiniteDeadlineTimingProfile (reward c) (cycles * 2) mixed) ≤ ε / 2 := by
    rw [hexploit]
    exact hterminal
  have hnash := isεAsymptoticNash_of_quittingTerminalExploitability_le
    (quittingFiniteDeadlineTimingProfile (reward c) (cycles * 2) mixed) htimingError
  have hsolo (who : Player) : 0 ≤ reward c (quittingSingletonTerminal who) who := by
    change 0 ≤ quittingSoloReward (reward c) who who
    simp
  refine ⟨cycles, hcycles, mixed, hlaw, hpair, hnever, hatom, hzero, htimingError,
    fun horizon hhorizon => ?_⟩
  obtain ⟨hpositive, hboundary⟩ := horizonBoundary_le_half cycles horizon hε hhorizon
  have hcharge : (2 : ℝ) * 4 * (cycles * 2 : ℕ) / horizon =
      16 * (cycles : ℝ) / horizon := by push_cast; ring
  have hdeliveryCharge : (4 : ℝ) * (cycles * 2 : ℕ) / horizon =
      8 * (cycles : ℝ) / horizon := by push_cast; ring
  have hsmall : 8 * (cycles : ℝ) / horizon ≤ 16 * (cycles : ℝ) / horizon := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hcyclesReal : (0 : ℝ) ≤ cycles := Nat.cast_nonneg cycles
    nlinarith
  refine ⟨?_, ?_⟩
  · have h := isHorizonNash_finiteDeadline_of_terminalNash (reward c) (cycles * 2)
      horizon mixed hnash (abs_reward_le_four hc) hsolo hpositive
    rw [hcharge] at h
    exact h.mono (by linarith)
  · intro who
    have hon := abs_finiteAveragePayoff_sub_terminal_finiteDeadline_le (reward c)
      (cycles * 2) horizon mixed who (fun terminal => abs_reward_le_four hc terminal who)
        hpositive
    rw [hdeliveryCharge] at hon
    have htarget : |quittingTerminalPayoff (reward c)
        (quittingFiniteDeadlineTimingProfile (reward c) (cycles * 2) mixed) who -
          rates.phaseAValue who| ≤ ε / 2 := by
      rw [congrFun hpay who, rates.finiteProfile_targetError_eq hc,
        ← rates.finiteProfile_debt_eq hc cycles hcycles who]
      exact (quittingTerminalDeviationDebt_le_exploitability
        (reward c) (rates.finiteProfile cycles) who).trans hterminal
    have htriangle := abs_sub_le
      ((quittingGame (reward c)).finiteAveragePayoff none horizon
        (quittingFiniteDeadlineTimingProfile (reward c) (cycles * 2) mixed) who)
      (quittingTerminalPayoff (reward c)
        (quittingFiniteDeadlineTimingProfile (reward c) (cycles * 2) mixed) who)
      (rates.phaseAValue who)
    linarith

/-- This fixed target has witnesses which are actual finite timing laws at every accuracy. -/
theorem isUniformEquilibriumPayoff_via_finiteCalendar (hc : c ∈ Set.Icc (1 : ℝ) 2) :
    (quittingGame (reward c)).IsUniformEquilibriumPayoff none rates.phaseAValue := by
  intro ε hε
  obtain ⟨cycles, _hcycles, mixed, _hlaw, _hpair, _hnever, _hatom, _hzero,
    _hterminal, hfinite⟩ := rates.finiteTiming_uniformPayoffWitness hc hε
  exact ⟨quittingFiniteDeadlineTimingProfile (reward c) (cycles * 2) mixed,
    max 1 ⌈32 * (cycles : ℝ) / ε⌉₊, hfinite⟩

end PeriodicRates

/-- The parameter alone chooses one rate pair before every accuracy, with literal
finite marginal masses, exact full semantic pairs and all long-horizon guarantees. -/
theorem exists_one_periodicRates_all_finiteCalendar_accuracies {c : ℝ}
    (hc : c ∈ Set.Icc (1 : ℝ) 2) :
    ∃ rates : PeriodicRates c, ∀ ε : ℝ, 0 < ε → rates.FiniteCalendarAccuracy ε := by
  obtain ⟨rates⟩ := exists_periodicRates hc
  exact ⟨rates, fun _ hε => rates.finiteTiming_uniformPayoffWitness hc hε⟩

theorem exists_periodicFiniteCalendarUniformPayoff {c : ℝ}
    (hc : c ∈ Set.Icc (1 : ℝ) 2) :
    ∃ rates : PeriodicRates c,
      (quittingGame (reward c)).IsUniformEquilibriumPayoff none rates.phaseAValue ∧
      ∀ ε : ℝ, 0 < ε → rates.FiniteCalendarAccuracy ε := by
  obtain ⟨rates, hfinite⟩ := exists_one_periodicRates_all_finiteCalendar_accuracies hc
  exact ⟨rates, rates.isUniformEquilibriumPayoff_via_finiteCalendar hc, hfinite⟩

end GameTheory.PairedCollisionReward

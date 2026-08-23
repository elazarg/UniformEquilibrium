/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.DiscreteHazardMixture
import MathUE.PMFProduct.FiniteFubini
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticStoppingLawFiniteSplice

/-!
# Harmonic survival-clock regression

Two of four players use the harmonic hazard `1 / (time + 2)` and the other
two always Continue.  Joint survival and every one-player-deleted survival
clock vanish, while deleting both active players leaves survival identically
one.  This is the game-facing clock obstruction behind finite splicing:
one-player-deleted exposure does not control the pair-deleted cemetery term.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.Probability.DiscreteHazard

namespace QuittingHarmonicGreenRegression

abbrev Player := Fin 4

/-- Harmonic stopping probability at a live date. -/
def hazardRate (time : ℕ) : ℝ := 1 / (time + 2 : ℝ)

theorem hazardRate_pos (time : ℕ) : 0 < hazardRate time := by
  unfold hazardRate
  positivity

theorem hazardRate_le_one (time : ℕ) : hazardRate time ≤ 1 := by
  unfold hazardRate
  have htime : (0 : ℝ) ≤ time := by positivity
  have hden : (0 : ℝ) < time + 2 := by linarith
  rw [div_le_one hden]
  linarith

/-- The scalar harmonic hazard, reused for its canonical survival product. -/
def scalarHazard : ScalarHazard where
  stop := hazardRate
  stop_nonneg time := (hazardRate_pos time).le
  stop_le_one := hazardRate_le_one

/-- Players zero and one are active; players two and three always Continue. -/
def rootSequence (time : ℕ) (who : Player) : PMF Bool :=
  if who = 0 ∨ who = 1 then scalarHazard.toBoolean time else PMF.pure false

@[simp] theorem rootSequence_active_zero (time : ℕ) :
    rootSequence time 0 = scalarHazard.toBoolean time := by
  simp [rootSequence]

@[simp] theorem rootSequence_active_one (time : ℕ) :
    rootSequence time 1 = scalarHazard.toBoolean time := by
  simp [rootSequence]

@[simp] theorem rootSequence_inactive_two (time : ℕ) :
    rootSequence time 2 = PMF.pure false := by
  simp [rootSequence]

@[simp] theorem rootSequence_inactive_three (time : ℕ) :
    rootSequence time 3 = PMF.pure false := by
  simp [rootSequence]

@[simp] theorem scalarHazard_continue_toReal (time : ℕ) :
    (scalarHazard.toBoolean time false).toReal = 1 - hazardRate time := by
  simp [ScalarHazard.toBoolean, scalarHazard]

/-- Exact harmonic survival over every finite window. -/
theorem scalarHazard_survival (start fuel : ℕ) :
    scalarHazard.survival start fuel =
      (start + 1 : ℝ) / (start + fuel + 1 : ℝ) := by
  induction fuel with
  | zero =>
      simp only [ScalarHazard.survival_zero]
      norm_num
      field_simp
  | succ fuel ih =>
      rw [ScalarHazard.survival_succ, ih]
      unfold scalarHazard hazardRate
      norm_num [Nat.cast_add, Nat.cast_one] at *
      have hfirst : (0 : ℝ) < start + fuel + 1 := by positivity
      have hsecond : (0 : ℝ) < start + fuel + 2 := by positivity
      field_simp [ne_of_gt hfirst, ne_of_gt hsecond]
      ring

theorem tendsto_scalarHazard_survival_zero (start : ℕ) :
    Tendsto (scalarHazard.survival start) atTop (nhds 0) := by
  rw [show scalarHazard.survival start = fun fuel : ℕ =>
      (start + 1 : ℝ) / ((start : ℝ) + (fuel : ℝ) + 1) by
    funext fuel
    exact scalarHazard_survival start fuel]
  have hden : Tendsto (fun fuel : ℕ =>
      (fuel : ℝ) + ((start : ℝ) + 1)) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop ((start : ℝ) + 1)
      tendsto_natCast_atTop_atTop
  simpa only [add_comm, add_left_comm, add_assoc] using
    hden.const_div_atTop ((start : ℝ) + 1)

theorem jointContinueMass (time : ℕ) :
    quittingStationaryContinueMass (rootSequence time) =
      (1 - hazardRate time) ^ 2 := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  rw [show (Finset.univ : Finset Player) = {0, 1, 2, 3} by decide]
  simp [rootSequence]
  ring

theorem fixedOpponentsContinueMass (time : ℕ) (who : Player) :
    quittingFixedOpponentsContinueMass rootSequence who time =
      if who = 0 ∨ who = 1 then 1 - hazardRate time
      else (1 - hazardRate time) ^ 2 := by
  fin_cases who <;>
    simp [quittingFixedOpponentsContinueMass,
      quittingStationaryContinueMass_eq_prod_continueProbability,
      rootSequence, Fin.prod_univ_succ] <;> ring

/-- Deleting either active player leaves the other harmonic clock. -/
theorem activeOpponentSurvivalWeight (who : Player)
    (hactive : who = 0 ∨ who = 1) (start fuel : ℕ) :
    quittingOpponentSurvivalWeight rootSequence who start fuel =
      scalarHazard.survival start fuel := by
  unfold quittingOpponentSurvivalWeight ScalarHazard.survival
  apply Finset.prod_congr rfl
  intro offset hoffset
  rw [fixedOpponentsContinueMass]
  simp [hactive, scalarHazard]

/-- Deleting an inactive player leaves both active harmonic clocks. -/
theorem inactiveOpponentSurvivalWeight (who : Player)
    (hinactive : who ≠ 0) (hinactive' : who ≠ 1) (start fuel : ℕ) :
    quittingOpponentSurvivalWeight rootSequence who start fuel =
      scalarHazard.survival start fuel ^ 2 := by
  unfold quittingOpponentSurvivalWeight ScalarHazard.survival
  unfold Math.survivalProduct
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro offset hoffset
  rw [fixedOpponentsContinueMass]
  simp [hinactive, hinactive', scalarHazard]

/-- Every one-player-deleted clock vanishes. -/
theorem tendsto_opponentSurvivalWeight_zero (who : Player) (start : ℕ) :
    Tendsto (quittingOpponentSurvivalWeight rootSequence who start)
      atTop (nhds 0) := by
  by_cases hzero : who = 0
  · have heq : quittingOpponentSurvivalWeight rootSequence who start =
        scalarHazard.survival start := by
      funext fuel
      exact activeOpponentSurvivalWeight who (Or.inl hzero) start fuel
    rw [heq]
    exact tendsto_scalarHazard_survival_zero start
  by_cases hone : who = 1
  · have heq : quittingOpponentSurvivalWeight rootSequence who start =
        scalarHazard.survival start := by
      funext fuel
      exact activeOpponentSurvivalWeight who (Or.inr hone) start fuel
    rw [heq]
    exact tendsto_scalarHazard_survival_zero start
  have heq : quittingOpponentSurvivalWeight rootSequence who start =
      fun fuel => scalarHazard.survival start fuel ^ 2 := by
    funext fuel
    exact inactiveOpponentSurvivalWeight who hzero hone start fuel
  rw [heq]
  simpa using (tendsto_scalarHazard_survival_zero start).pow 2

/-- The joint clock vanishes as well. -/
theorem tendsto_jointSurvivalWeight_zero (start : ℕ) :
    Tendsto (quittingJointSurvivalWeight rootSequence start) atTop (nhds 0) := by
  have hle : ∀ fuel,
      quittingJointSurvivalWeight rootSequence start fuel ≤
        quittingOpponentSurvivalWeight rootSequence 0 start fuel := by
    intro fuel
    exact quittingJointSurvivalWeight_le_quittingOpponentSurvivalWeight
      rootSequence 0 start fuel
  apply squeeze_zero
    (fun fuel => quittingJointSurvivalWeight_nonneg rootSequence start fuel)
    hle
    (tendsto_opponentSurvivalWeight_zero 0 start)

/-- Deleting both active players leaves only deterministic Continue marginals,
so the pair-deleted survival clock is identically one. -/
theorem pairDeletedActiveSurvivalWeight (start fuel : ℕ) :
    quittingPairDeletedSurvivalWeight rootSequence 0 1 start fuel = 1 := by
  unfold quittingPairDeletedSurvivalWeight quittingOpponentSurvivalWeight
  apply Finset.prod_eq_one
  intro offset hoffset
  unfold quittingFixedOpponentsContinueMass quittingRootSequenceUpdate
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  rw [show (Finset.univ : Finset Player) = {0, 1, 2, 3} by decide]
  simp [rootSequence, quittingAlwaysContinueHazard]

/-! ## Vanishing local defects with persistent terminal debt -/

/-- A player receives `-1` exactly when that player belongs to the first
quitting coalition and is one of the two active players. -/
def reward (terminal : {S : Finset Player // S.Nonempty}) : Payoff Player :=
  fun who =>
    if who = 0 ∨ who = 1 then
      if who ∈ terminal.1 then -1 else 0
    else 0

theorem reward_bound (terminal player) : |reward terminal player| ≤ 1 := by
  by_cases hactive : player = 0 ∨ player = 1 <;>
    by_cases hmem : player ∈ terminal.1 <;> simp [reward, hactive, hmem]

@[simp] theorem quittingQuitters_vec4 (a b c d : Bool) :
    quittingQuitters ![a, b, c, d] =
      (if a then {0} else ∅) ∪ (if b then {1} else ∅) ∪
        (if c then {2} else ∅) ∪ (if d then {3} else ∅) := by
  ext who
  fin_cases who <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp [quittingQuitters]

def prescribedFiniteValue (who : Player) (start fuel : ℕ) : ℝ :=
  quittingFiniteRootPayoff reward rootSequence who
    (fun time => rootSequence time who) start fuel

theorem prescribedFiniteValue_succ_zero (start fuel : ℕ) :
    prescribedFiniteValue 0 start (fuel + 1) =
      -hazardRate start + (1 - hazardRate start) ^ 2 *
        prescribedFiniteValue 0 (start + 1) fuel := by
  unfold prescribedFiniteValue
  rw [quittingFiniteRootPayoff]
  unfold quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4]
  simp [rootSequence, quittingRootPayoff, reward, expect_eq_sum,
    ScalarHazard.toBoolean, scalarHazard]
  ring

theorem prescribedFiniteValue_succ_one (start fuel : ℕ) :
    prescribedFiniteValue 1 start (fuel + 1) =
      -hazardRate start + (1 - hazardRate start) ^ 2 *
        prescribedFiniteValue 1 (start + 1) fuel := by
  unfold prescribedFiniteValue
  rw [quittingFiniteRootPayoff]
  unfold quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4]
  simp [rootSequence, quittingRootPayoff, reward, expect_eq_sum,
    ScalarHazard.toBoolean, scalarHazard]
  ring

theorem prescribedFiniteValue_succ (who : Player)
    (hactive : who = 0 ∨ who = 1) (start fuel : ℕ) :
    prescribedFiniteValue who start (fuel + 1) =
      -hazardRate start + (1 - hazardRate start) ^ 2 *
        prescribedFiniteValue who (start + 1) fuel := by
  rcases hactive with rfl | rfl
  · exact prescribedFiniteValue_succ_zero start fuel
  · exact prescribedFiniteValue_succ_one start fuel

/-- Each active player's finite-horizon loss is at least half of the absorbed
mass. -/
theorem prescribedFiniteValue_le_half_absorbed (who : Player)
    (hactive : who = 0 ∨ who = 1) (start fuel : ℕ) :
    prescribedFiniteValue who start fuel ≤
      -(1 / 2 : ℝ) * (1 - scalarHazard.survival start fuel ^ 2) := by
  induction fuel generalizing start with
  | zero =>
      simp [prescribedFiniteValue, quittingFiniteRootPayoff,
        ScalarHazard.survival_zero]
  | succ fuel ih =>
      rw [prescribedFiniteValue_succ who hactive]
      rw [ScalarHazard.survival_succ_left]
      simp only [scalarHazard]
      have hq0 := (hazardRate_pos start).le
      have hq1 := hazardRate_le_one start
      have hcoefficient : 0 ≤ (1 - hazardRate start) ^ 2 := sq_nonneg _
      have htail := mul_le_mul_of_nonneg_left (ih (start + 1)) hcoefficient
      calc
        -hazardRate start + (1 - hazardRate start) ^ 2 *
              prescribedFiniteValue who (start + 1) fuel ≤
            -hazardRate start + (1 - hazardRate start) ^ 2 *
              (-(1 / 2 : ℝ) *
                (1 - scalarHazard.survival (start + 1) fuel ^ 2)) :=
          by simpa [add_comm] using add_le_add_left htail (-hazardRate start)
        _ = -(1 / 2 : ℝ) *
                (1 - ((1 - hazardRate start) *
                  scalarHazard.survival (start + 1) fuel) ^ 2) -
              hazardRate start ^ 2 / 2 := by ring
        _ ≤ -(1 / 2 : ℝ) *
              (1 - ((1 - hazardRate start) *
                scalarHazard.survival (start + 1) fuel) ^ 2) :=
          sub_le_self _ (div_nonneg (sq_nonneg _) (by norm_num))

/-- The prescribed terminal payoff of either active player is at most
`-1/2`. -/
theorem terminalValue_active_le_neg_half (who : Player)
    (hactive : who = 0 ∨ who = 1) (start : ℕ) :
    quittingRootSequenceTerminalValue reward rootSequence who start ≤
      -(1 / 2 : ℝ) := by
  have hleft := tendsto_quittingFiniteRootPayoff_self_terminalValue
    reward rootSequence who start
  have hsurvival := tendsto_scalarHazard_survival_zero start
  have hright : Tendsto (fun fuel =>
      -(1 / 2 : ℝ) * (1 - scalarHazard.survival start fuel ^ 2))
      atTop (nhds (-(1 / 2 : ℝ))) := by
    convert (tendsto_const_nhds.mul
      (tendsto_const_nhds.sub (hsurvival.pow 2))) using 1
    · norm_num
  exact le_of_tendsto_of_tendsto hleft hright
    (Eventually.of_forall
      (prescribedFiniteValue_le_half_absorbed who hactive start))

def profile (start : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingRootSequenceProfile reward rootSequence start

/-- A Never deviation receives zero: every terminal coalition containing the
deviator has zero mass, and every other coalition gives that player zero. -/
theorem terminalPayoff_update_never_eq_zero (who : Player) (start : ℕ) :
    quittingTerminalPayoff reward
        (Function.update (profile start) who
          (quittingPureTimeBehaviorStrategy reward who none)) who = 0 := by
  unfold quittingTerminalPayoff
  apply Finset.sum_eq_zero
  intro terminal hterminal
  by_cases hmem : who ∈ terminal.1
  · have hmass :=
      quittingTerminalOutcomeMass_update_pureTime_none_mem_eq_zero
        reward (profile start) who terminal hmem
    change quittingAbsorbedMassLimit reward
        (Function.update (profile start) who
          (quittingPureTimeBehaviorStrategy reward who none)) terminal = 0 at hmass
    rw [hmass, zero_mul]
  · simp [reward, hmem]

/-- Both active players retain terminal deviation debt at least `1/2` at
every reached suffix. -/
theorem terminalDeviationDebt_active_ge_half (who : Player)
    (hactive : who = 0 ∨ who = 1) (start : ℕ) :
    1 / 2 ≤ quittingTerminalDeviationDebt reward (profile start) who := by
  have hbest := quittingTerminalPayoff_update_le_continuationBestResponseValue
    reward (profile start) who
      (quittingPureTimeBehaviorStrategy reward who none)
  rw [terminalPayoff_update_never_eq_zero] at hbest
  have hprescribed := terminalValue_active_le_neg_half who hactive start
  change quittingTerminalPayoff reward (profile start) who ≤ -(1 / 2 : ℝ)
    at hprescribed
  unfold quittingTerminalDeviationDebt
  linarith

def reachedTailValue (time : ℕ) : Payoff Player := fun who =>
  quittingRootSequenceTerminalValue reward rootSequence who (time + 1)

theorem reachedTailValue_abs_le_one (time : ℕ) (who : Player) :
    |reachedTailValue time who| ≤ 1 := by
  exact abs_quittingTerminalPayoff_le reward
    (quittingRootSequenceProfile reward rootSequence (time + 1)) who reward_bound

theorem reachedTailValue_nonpos (time : ℕ) (who : Player) :
    reachedTailValue time who ≤ 0 := by
  unfold reachedTailValue quittingRootSequenceTerminalValue
    quittingTerminalPayoff
  apply Finset.sum_nonpos
  intro terminal hterminal
  exact mul_nonpos_of_nonneg_of_nonpos
    (quittingAbsorbedMassLimit_nonneg reward _ terminal) (by
      by_cases hactive : who = 0 ∨ who = 1 <;>
        by_cases hmem : who ∈ terminal.1 <;>
          simp [reward, hactive, hmem])

theorem rootQuitPayoff_active (who : Player)
    (hactive : who = 0 ∨ who = 1) (time : ℕ) :
    quittingRootQuitPayoff reward (reachedTailValue time)
      (rootSequence time) who = -1 := by
  rcases hactive with rfl | rfl
  · unfold quittingRootQuitPayoff quittingRootExpectedPayoff
    rw [Math.PMFProduct.expect_pmfPi_fin4]
    simp [rootSequence, quittingRootPayoff, reward, expect_eq_sum,
      ScalarHazard.toBoolean, scalarHazard]
    ring
  · unfold quittingRootQuitPayoff quittingRootExpectedPayoff
    rw [Math.PMFProduct.expect_pmfPi_fin4]
    simp [rootSequence, quittingRootPayoff, reward, expect_eq_sum,
      ScalarHazard.toBoolean, scalarHazard]

theorem rootContinuePayoff_active (who : Player)
    (hactive : who = 0 ∨ who = 1) (time : ℕ) :
    quittingRootContinuePayoff reward (reachedTailValue time)
        (rootSequence time) who =
      (1 - hazardRate time) * reachedTailValue time who := by
  rcases hactive with rfl | rfl
  · unfold quittingRootContinuePayoff quittingRootExpectedPayoff
    rw [Math.PMFProduct.expect_pmfPi_fin4]
    simp [rootSequence, quittingRootPayoff, reward, expect_eq_sum,
      ScalarHazard.toBoolean, scalarHazard]
  · unfold quittingRootContinuePayoff quittingRootExpectedPayoff
    rw [Math.PMFProduct.expect_pmfPi_fin4]
    simp [rootSequence, quittingRootPayoff, reward, expect_eq_sum,
      ScalarHazard.toBoolean, scalarHazard]

theorem rootSuccessorPayoff_active (who : Player)
    (hactive : who = 0 ∨ who = 1) (time : ℕ) :
    quittingRootSuccessorPayoff reward (reachedTailValue time)
        (rootSequence time) who =
      -hazardRate time + (1 - hazardRate time) ^ 2 *
        reachedTailValue time who := by
  rw [quittingRootSuccessorPayoff_eq_endpointMix,
    rootQuitPayoff_active who hactive,
    rootContinuePayoff_active who hactive]
  rcases hactive with rfl | rfl <;>
    simp [rootSequence, ScalarHazard.toBoolean, scalarHazard] <;> ring

/-- The actual reached-row coordinate defect of either active player is at
most its current harmonic quit probability. -/
theorem coordinateNashDefect_active_le_hazardRate (who : Player)
    (hactive : who = 0 ∨ who = 1) (time : ℕ) :
    quittingRootCoordinateNashDefect reward (reachedTailValue time)
        (rootSequence time) who ≤ hazardRate time := by
  have hlower : -(1 : ℝ) ≤ reachedTailValue time who :=
    neg_le_of_abs_le (reachedTailValue_abs_le_one time who)
  have hq0 := (hazardRate_pos time).le
  have hq1 := hazardRate_le_one time
  have hc0 : 0 ≤ 1 - hazardRate time := sub_nonneg.mpr hq1
  have hcontinueLower : -(1 : ℝ) ≤
      (1 - hazardRate time) * reachedTailValue time who := by
    have hmul := mul_le_mul_of_nonneg_left hlower hc0
    nlinarith
  unfold quittingRootCoordinateNashDefect
  rw [rootQuitPayoff_active who hactive,
    rootContinuePayoff_active who hactive,
    rootSuccessorPayoff_active who hactive,
    max_eq_right hcontinueLower]
  have hcontinueNonpos :
      (1 - hazardRate time) * reachedTailValue time who ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hc0 (reachedTailValue_nonpos time who)
  have hpaid : hazardRate time *
      ((1 - hazardRate time) * reachedTailValue time who) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hq0 hcontinueNonpos
  nlinarith

theorem tendsto_coordinateNashDefect_active_zero (who : Player)
    (hactive : who = 0 ∨ who = 1) :
    Tendsto (fun time =>
      quittingRootCoordinateNashDefect reward (reachedTailValue time)
        (rootSequence time) who) atTop (nhds 0) := by
  apply squeeze_zero
    (fun time => quittingRootCoordinateNashDefect_nonneg reward
      (reachedTailValue time) (rootSequence time) who)
    (coordinateNashDefect_active_le_hazardRate who hactive)
  change Tendsto (fun time : ℕ => (1 : ℝ) / ((time : ℝ) + 2))
    atTop (nhds 0)
  exact (Filter.tendsto_atTop_add_const_right atTop (2 : ℝ)
    tendsto_natCast_atTop_atTop).const_div_atTop 1

end QuittingHarmonicGreenRegression

end GameTheory

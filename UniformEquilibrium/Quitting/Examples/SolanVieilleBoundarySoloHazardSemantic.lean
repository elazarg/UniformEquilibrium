/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality
import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryRestart
import UniformEquilibrium.Quitting.Cycles.SoloRootSequenceValues
import UniformEquilibrium.Quitting.Boundary.Holonomy.InfiniteBehavioralTailEvaluation
import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundarySoloHazardFloor
import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundaryTable

/-!
# Semantic accounting for arbitrary solo-hazard calendars

This module connects an arbitrary infinite solo-hazard calendar to the
project's literal terminal-payoff semantics.  It contains no periodicity or
positive-hazard assumption.
-/

noncomputable section

namespace GameTheory
namespace SolanVieilleBoundary
namespace SoloHazardLedger

open Filter

/-- Joint on-path survival immediately before a date. -/
def Schedule.survival (schedule : Schedule) : ℕ → ℝ
  | 0 => 1
  | time + 1 => schedule.survival time * (1 - schedule.hazard time)

/-- On-path singleton absorption mass at a date. -/
def Schedule.mass (schedule : Schedule) (time : ℕ) : ℝ :=
  schedule.survival time * schedule.hazard time

theorem Schedule.survival_nonneg (schedule : Schedule) (time : ℕ) :
    0 ≤ schedule.survival time := by
  induction time with
  | zero => norm_num [Schedule.survival]
  | succ time ih =>
      exact mul_nonneg ih (sub_nonneg.mpr (schedule.hazard_le_one time))

theorem Schedule.survival_le_one (schedule : Schedule) (time : ℕ) :
    schedule.survival time ≤ 1 := by
  induction time with
  | zero => norm_num [Schedule.survival]
  | succ time ih =>
      rw [Schedule.survival]
      calc
        schedule.survival time * (1 - schedule.hazard time) ≤
            1 * (1 - schedule.hazard time) :=
          mul_le_mul_of_nonneg_right ih
            (sub_nonneg.mpr (schedule.hazard_le_one time))
        _ ≤ 1 := by linarith [schedule.hazard_nonneg time]

theorem Schedule.mass_nonneg (schedule : Schedule) (time : ℕ) :
    0 ≤ schedule.mass time :=
  mul_nonneg (schedule.survival_nonneg time)
    (schedule.hazard_nonneg time)

theorem Schedule.mass_le_hazard (schedule : Schedule) (time : ℕ) :
    schedule.mass time ≤ schedule.hazard time := by
  unfold Schedule.mass
  calc
    schedule.survival time * schedule.hazard time ≤
        1 * schedule.hazard time :=
      mul_le_mul_of_nonneg_right (schedule.survival_le_one time)
        (schedule.hazard_nonneg time)
    _ = schedule.hazard time := one_mul _

theorem Schedule.sum_mass_eq_one_sub_survival
    (schedule : Schedule) (time : ℕ) :
    ∑ offset ∈ Finset.range time, schedule.mass offset =
      1 - schedule.survival time := by
  induction time with
  | zero => simp [Schedule.survival]
  | succ time ih =>
      rw [Finset.sum_range_succ, ih]
      simp [Schedule.survival, Schedule.mass]
      ring

theorem Schedule.summable_mass (schedule : Schedule) :
    Summable schedule.mass := by
  apply summable_of_sum_range_le (fun time ↦ schedule.mass_nonneg time)
  intro time
  rw [schedule.sum_mass_eq_one_sub_survival]
  exact sub_le_self 1 (schedule.survival_nonneg time)

/-- Owner-class mass contribution at one date. -/
def Schedule.ownerMassTerm
    (schedule : Schedule) (owner : Player) (time : ℕ) : ℝ :=
  if schedule.owner time = owner then schedule.mass time else 0

/-- Infinite owner-class mass. -/
def Schedule.ownerMass (schedule : Schedule) (owner : Player) : ℝ :=
  ∑' time, schedule.ownerMassTerm owner time

theorem Schedule.summable_ownerMassTerm
    (schedule : Schedule) (owner : Player) :
    Summable (schedule.ownerMassTerm owner) := by
  unfold Schedule.ownerMassTerm
  apply Summable.of_nonneg_of_le
    (fun time ↦ by
      split <;> simp_all [schedule.mass_nonneg time])
    (fun time ↦ by
      split <;> simp_all [schedule.mass_nonneg time])
    schedule.summable_mass

theorem Schedule.ownerMass_nonneg
    (schedule : Schedule) (owner : Player) :
    0 ≤ schedule.ownerMass owner :=
  tsum_nonneg fun time ↦ by
    unfold Schedule.ownerMassTerm
    split <;> simp_all [schedule.mass_nonneg time]

/-- Survival after deleting one player's prescribed hazards. -/
def Schedule.deletedSurvival
    (schedule : Schedule) (who : Player) : ℕ → ℝ
  | 0 => 1
  | time + 1 => schedule.deletedSurvival who time *
      (if schedule.owner time = who then 1 else 1 - schedule.hazard time)

/-- Opponent first-exit mass on the deleted clock. -/
def Schedule.deletedMass
    (schedule : Schedule) (who : Player) (time : ℕ) : ℝ :=
  if schedule.owner time = who then 0
  else schedule.deletedSurvival who time * schedule.hazard time

/-- Survival of one player's own prescribed hazard clock. -/
def Schedule.ownSurvival
    (schedule : Schedule) (who : Player) : ℕ → ℝ
  | 0 => 1
  | time + 1 => schedule.ownSurvival who time *
      (if schedule.owner time = who then 1 - schedule.hazard time else 1)

/-- Signed deleted-prefix potential. -/
def Schedule.prefixPotential
    (schedule : Schedule) (who : Player) (time : ℕ) : ℝ :=
  ∑ offset ∈ Finset.range time,
    if schedule.owner offset = who then 0
    else if schedule.owner offset = partner who then
      3 * schedule.deletedMass who offset
    else -schedule.deletedMass who offset

@[simp] theorem Schedule.prefixPotential_succ
    (schedule : Schedule) (who : Player) (time : ℕ) :
    schedule.prefixPotential who (time + 1) =
      schedule.prefixPotential who time +
        (if schedule.owner time = who then 0
        else if schedule.owner time = partner who then
          3 * schedule.deletedMass who time
        else -schedule.deletedMass who time) := by
  simp [Schedule.prefixPotential, Finset.sum_range_succ]

theorem Schedule.ownSurvival_nonneg
    (schedule : Schedule) (who : Player) (time : ℕ) :
    0 ≤ schedule.ownSurvival who time := by
  induction time with
  | zero => norm_num [Schedule.ownSurvival]
  | succ time ih =>
      rw [Schedule.ownSurvival]
      split
      · exact mul_nonneg ih
          (sub_nonneg.mpr (schedule.hazard_le_one time))
      · simpa using ih

theorem Schedule.survival_eq_own_mul_deleted
    (schedule : Schedule) (who : Player) (time : ℕ) :
    schedule.survival time =
      schedule.ownSurvival who time * schedule.deletedSurvival who time := by
  induction time with
  | zero => simp [Schedule.survival, Schedule.ownSurvival,
      Schedule.deletedSurvival]
  | succ time ih =>
      rw [Schedule.survival, Schedule.ownSurvival,
        Schedule.deletedSurvival, ih]
      split <;> ring

theorem Schedule.mass_eq_own_mul_deleted_mul_hazard
    (schedule : Schedule) (who : Player) (time : ℕ) :
    schedule.mass time = schedule.ownSurvival who time *
      schedule.deletedSurvival who time * schedule.hazard time := by
  rw [Schedule.mass, schedule.survival_eq_own_mul_deleted who]

theorem Schedule.deletedSurvival_add_sum_deletedMass
    (schedule : Schedule) (who : Player) (time : ℕ) :
    schedule.deletedSurvival who time +
        ∑ offset ∈ Finset.range time, schedule.deletedMass who offset = 1 := by
  induction time with
  | zero => simp [Schedule.deletedSurvival]
  | succ time ih =>
      rw [Finset.sum_range_succ, Schedule.deletedSurvival]
      by_cases howner : schedule.owner time = who
      · rw [if_pos howner,
          show schedule.deletedMass who time = 0 by
            simp [Schedule.deletedMass, howner], add_zero]
        simpa using ih
      · rw [if_neg howner,
          show schedule.deletedMass who time =
              schedule.deletedSurvival who time * schedule.hazard time by
            simp [Schedule.deletedMass, howner]]
        nlinarith [ih]

/-- Literal history-independent behavior profile generated by the calendar. -/
def Schedule.profile (schedule : Schedule) :
    (quittingGame boundaryReward).BehaviorProfile :=
  quittingRootSequenceProfile boundaryReward schedule.roots 0

theorem Schedule.jointSurvivalWeight_eq_survival
    (schedule : Schedule) (time : ℕ) :
    quittingJointSurvivalWeight schedule.roots 0 time =
      schedule.survival time := by
  induction time with
  | zero => rfl
  | succ time ih =>
      rw [quittingJointSurvivalWeight_succ, ih]
      simp [Schedule.roots, Schedule.survival,
        quittingHazardCoin_false_toReal]

/-- The semantic terminal payoff is the absolutely convergent singleton-atom
series of the solo calendar. -/
theorem Schedule.terminalPayoff_eq_tsum_mass_mul_soloReward
    (schedule : Schedule) (who : Player) :
    quittingTerminalPayoff boundaryReward schedule.profile who =
      ∑' time, schedule.mass time *
        quittingSoloReward boundaryReward (schedule.owner time) who := by
  rw [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot]
  simp only [Schedule.profile,
    quittingProfileLiveRoot_quittingRootSequenceProfile_zero]
  rw [quittingRootSequenceTerminalValue_eq_tsum_absorbingContribution]
  apply tsum_congr
  intro time
  rw [schedule.jointSurvivalWeight_eq_survival]
  by_cases hself : schedule.owner time = who
  · simp [Schedule.roots, quittingRootAbsorbingContribution_solo,
      Schedule.mass, hself]
  · by_cases hpair : (schedule.owner time).val / 2 = who.val / 2
    · simp [Schedule.roots, quittingRootAbsorbingContribution_solo,
        Schedule.mass, hself, hpair]
      ring
    · simp [Schedule.roots, quittingRootAbsorbingContribution_solo,
        Schedule.mass, hself, hpair]

private theorem mass_mul_soloReward_eq_ownerTerms
    (schedule : Schedule) (who : Player) (time : ℕ) :
    schedule.mass time *
        quittingSoloReward boundaryReward (schedule.owner time) who =
      schedule.ownerMassTerm who time +
        4 * schedule.ownerMassTerm (partner who) time := by
  generalize howner : schedule.owner time = owner
  fin_cases who <;> fin_cases owner <;>
    simp [Schedule.ownerMassTerm, soloReward_eval, partner, howner] <;> ring

/-- **Prescribed payoff adapter.**  Literal terminal semantics agrees exactly
with the four owner-class singleton formula used by the ledger. -/
theorem Schedule.terminalPayoff_eq_prescribedPayoff
    (schedule : Schedule) (who : Player) :
    quittingTerminalPayoff boundaryReward schedule.profile who =
      prescribedPayoff schedule.ownerMass who := by
  rw [schedule.terminalPayoff_eq_tsum_mass_mul_soloReward]
  simp_rw [mass_mul_soloReward_eq_ownerTerms]
  rw [(schedule.summable_ownerMassTerm who).tsum_add
      ((schedule.summable_ownerMassTerm (partner who)).mul_left 4),
    tsum_mul_left]
  rfl

private theorem update_scheduleRoot_owner
    (schedule : Schedule) (time : ℕ) (coin : PMF Bool) :
    Function.update (schedule.roots time) (schedule.owner time) coin =
      quittingSoloStationaryRoot (schedule.owner time) coin := by
  funext player
  by_cases hplayer : player = schedule.owner time
  · subst player
    simp [quittingSoloStationaryRoot]
  · rw [Function.update_of_ne hplayer,
      schedule.roots_other time player hplayer]
    simp [quittingSoloStationaryRoot, hplayer]

theorem Schedule.opponentSurvivalWeight_eq_deletedSurvival
    (schedule : Schedule) (who : Player) (time : ℕ) :
    quittingOpponentSurvivalWeight schedule.roots who 0 time =
      schedule.deletedSurvival who time := by
  induction time with
  | zero => rfl
  | succ time ih =>
      rw [quittingOpponentSurvivalWeight_zero_succ, ih,
        Schedule.deletedSurvival]
      by_cases howner : schedule.owner time = who
      · subst who
        unfold quittingFixedOpponentsContinueMass
        rw [update_scheduleRoot_owner,
          quittingStationaryContinueMass_eq_prod_continueProbability]
        simp [quittingSoloStationaryRoot]
      · rw [quittingFixedOpponentsContinueMass_eq_of_soloRoot
          schedule.roots (schedule.roots_isolated time) (Ne.symm howner)]
        simp [Schedule.roots, quittingHazardCoin_false_toReal, howner]

theorem Schedule.fixedOpponentsQuitValue_eq_one
    (schedule : Schedule) (who : Player) (time : ℕ) :
    quittingFixedOpponentsQuitValue boundaryReward schedule.roots who time = 1 := by
  by_cases howner : schedule.owner time = who
  · subst who
    unfold quittingFixedOpponentsQuitValue
    rw [update_scheduleRoot_owner,
      quittingRootAbsorbingContribution_solo]
    simp
  · rw [quittingFixedOpponentsQuitValue_eq_of_soloRoot boundaryReward
      schedule.roots (schedule.roots_isolated time) (Ne.symm howner)]
    rw [soloReward_self]
    have hcollision : quittingSingletonCollisionReward boundaryReward
        (schedule.owner time) who = 1 := by
      simpa [quittingSingletonCollisionReward] using
        boundaryReward_pair_eq_one (schedule.owner time) who
    rw [hcollision]
    have hcoin := quittingRoot_continueProbability_add_quitProbability
      (schedule.roots time) (schedule.owner time)
    linarith

theorem Schedule.fixedOpponentsContinueReward_eq
    (schedule : Schedule) (who : Player) (time : ℕ) :
    quittingFixedOpponentsContinueReward boundaryReward schedule.roots who time =
      if schedule.owner time = who then 0
      else schedule.hazard time *
        quittingSoloReward boundaryReward (schedule.owner time) who := by
  by_cases howner : schedule.owner time = who
  · subst who
    rw [if_pos rfl]
    unfold quittingFixedOpponentsContinueReward
    rw [update_scheduleRoot_owner,
      quittingRootAbsorbingContribution_solo]
    simp
  · rw [if_neg howner,
      quittingFixedOpponentsContinueReward_eq_of_soloRoot boundaryReward
        schedule.roots (schedule.roots_isolated time) (Ne.symm howner)]
    simp [Schedule.roots]

theorem Schedule.liveLedgerAccum_eq_sum_deletedMass
    (schedule : Schedule) (who : Player) (time : ℕ) :
    quittingLiveLedgerAccum boundaryReward schedule.roots who 0 time =
      ∑ offset ∈ Finset.range time,
        schedule.deletedMass who offset *
          quittingSoloReward boundaryReward (schedule.owner offset) who := by
  unfold quittingLiveLedgerAccum
  simp only [Nat.zero_add]
  refine Finset.sum_congr rfl fun offset _ ↦ ?_
  rw [schedule.opponentSurvivalWeight_eq_deletedSurvival,
    schedule.fixedOpponentsContinueReward_eq]
  unfold Schedule.deletedMass
  split <;> ring

private theorem deletedMass_mul_soloReward_eq_potentialTerm
    (schedule : Schedule) (who : Player) (time : ℕ) :
    schedule.deletedMass who time *
        quittingSoloReward boundaryReward (schedule.owner time) who =
      schedule.deletedMass who time +
        (if schedule.owner time = who then 0
        else if schedule.owner time = partner who then
          3 * schedule.deletedMass who time
        else -schedule.deletedMass who time) := by
  generalize howner : schedule.owner time = owner
  fin_cases who <;> fin_cases owner <;>
    simp [Schedule.deletedMass, soloReward_eval, partner, howner] <;> ring

theorem Schedule.liveLedger_add_deletedSurvival_eq
    (schedule : Schedule) (who : Player) (time : ℕ) :
    quittingLiveLedgerAccum boundaryReward schedule.roots who 0 time +
        schedule.deletedSurvival who time =
      1 + schedule.prefixPotential who time := by
  rw [schedule.liveLedgerAccum_eq_sum_deletedMass]
  have htelescope := schedule.deletedSurvival_add_sum_deletedMass who time
  simp_rw [deletedMass_mul_soloReward_eq_potentialTerm]
  rw [Finset.sum_add_distrib]
  unfold Schedule.prefixPotential
  linarith

/-- **Pure-time semantic adapter.**  Every finite quitting date has exactly
the deleted-prefix value used in the exploitability proof. -/
theorem Schedule.pureTimeTerminalValue_eq_one_add_prefixPotential
    (schedule : Schedule) (who : Player) (time : ℕ) :
    quittingRootSequencePureTimeTerminalValue boundaryReward schedule.roots
        who (some time) 0 =
      1 + schedule.prefixPotential who time := by
  rw [show time = 0 + time by omega,
    quittingRootSequencePureTimeTerminalValue_some_add,
    schedule.fixedOpponentsQuitValue_eq_one,
    schedule.opponentSurvivalWeight_eq_deletedSurvival, mul_one]
  simpa using schedule.liveLedger_add_deletedSurvival_eq who time

/-- The same pure-time formula in literal behavioral-profile semantics. -/
theorem Schedule.terminalPayoff_update_pureTime_eq
    (schedule : Schedule) (who : Player) (time : ℕ) :
    quittingTerminalPayoff boundaryReward
        (Function.update schedule.profile who
          (quittingPureTimeBehaviorStrategy boundaryReward who (some time))) who =
      1 + schedule.prefixPotential who time := by
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
  simp only [Schedule.profile,
    quittingProfileLiveRoot_quittingRootSequenceProfile_zero]
  exact schedule.pureTimeTerminalValue_eq_one_add_prefixPotential who time

/-! ## Deflated gaps -/

/-- Literal atom carried by one date of the infinite calendar. -/
def Schedule.atom (schedule : Schedule) (time : ℕ) : Atom where
  owner := schedule.owner time
  hazard := schedule.hazard time
  mass := schedule.mass time

/-- Recursive deflated gap initialized from a supplied slack vector. -/
def Schedule.gap (schedule : Schedule) (slack : Player → ℝ)
    (who : Player) : ℕ → ℝ
  | 0 => slack who
  | time + 1 => gapStep who (schedule.atom time)
      (schedule.gap slack who time)

/-- The recursive gap is exactly own survival times prefix slack. -/
theorem Schedule.gap_eq_ownSurvival_mul
    (schedule : Schedule) (slack : Player → ℝ)
    (who : Player) (time : ℕ) :
    schedule.gap slack who time =
      schedule.ownSurvival who time *
        (slack who - schedule.prefixPotential who time) := by
  induction time with
  | zero => simp [Schedule.gap, Schedule.ownSurvival,
      Schedule.prefixPotential]
  | succ time ih =>
      rw [Schedule.gap, ih, Schedule.ownSurvival,
        Schedule.prefixPotential_succ]
      have hmass := schedule.mass_eq_own_mul_deleted_mul_hazard who time
      unfold Schedule.deletedMass Schedule.atom
      generalize howner : schedule.owner time = owner at hmass ⊢
      fin_cases who <;> fin_cases owner <;>
        simp [gapStep, partner] at hmass ⊢ <;> ring_nf at hmass ⊢ <;>
        linarith

/-! ## Literal exploitability data -/

/-- Literal maximum all-behavior terminal exploitability of the calendar. -/
def Schedule.exploitability (schedule : Schedule) : ℝ :=
  quittingTerminalExploitability boundaryReward schedule.profile

theorem Schedule.exploitability_nonneg (schedule : Schedule) :
    0 ≤ schedule.exploitability := by
  unfold Schedule.exploitability quittingTerminalExploitability
  exact (le_max_left 0 _).trans
    (QuittingBoundaryHolonomy.le_finitePlayerMax
      (fun who ↦ max 0
        (quittingContinuationBestResponseValue boundaryReward
          schedule.profile who -
          quittingTerminalPayoff boundaryReward schedule.profile who)) 0)

theorem Schedule.terminalGain_le_exploitability
    (schedule : Schedule) (who : Player) :
    quittingContinuationBestResponseValue boundaryReward schedule.profile who -
        quittingTerminalPayoff boundaryReward schedule.profile who ≤
      schedule.exploitability := by
  unfold Schedule.exploitability quittingTerminalExploitability
  exact (le_max_right 0 _).trans
    (QuittingBoundaryHolonomy.le_finitePlayerMax
      (fun player ↦ max 0
        (quittingContinuationBestResponseValue boundaryReward
          schedule.profile player -
          quittingTerminalPayoff boundaryReward schedule.profile player)) who)

/-- Every finite pure quitting time lies below prescribed payoff plus literal
exploitability. -/
theorem Schedule.one_add_prefixPotential_le_payoff_add_exploitability
    (schedule : Schedule) (who : Player) (time : ℕ) :
    1 + schedule.prefixPotential who time ≤
      quittingTerminalPayoff boundaryReward schedule.profile who +
        schedule.exploitability := by
  rw [← schedule.terminalPayoff_update_pureTime_eq who time]
  have hdeviation : quittingTerminalPayoff boundaryReward
      (Function.update schedule.profile who
        (quittingPureTimeBehaviorStrategy boundaryReward who (some time))) who ≤
      quittingContinuationBestResponseValue boundaryReward schedule.profile who := by
    unfold quittingContinuationBestResponseValue
    exact le_csSup
      (bddAbove_range_quittingTerminalPayoff_update
        boundaryReward schedule.profile who)
      ⟨quittingPureTimeBehaviorStrategy boundaryReward who (some time), rfl⟩
  linarith [schedule.terminalGain_le_exploitability who]

/-- Singleton floor deviations force every prescribed coordinate above
`1 - E`. -/
theorem Schedule.singletonFloor
    (schedule : Schedule) (who : Player) :
    1 - schedule.exploitability ≤ prescribedPayoff schedule.ownerMass who := by
  rw [← schedule.terminalPayoff_eq_prescribedPayoff]
  have hzero := schedule.one_add_prefixPotential_le_payoff_add_exploitability
    who 0
  simp [Schedule.prefixPotential] at hzero
  linarith

/-- Exploitability-inflated singleton slack. -/
def Schedule.slack (schedule : Schedule) (who : Player) : ℝ :=
  prescribedPayoff schedule.ownerMass who - 1 + schedule.exploitability

theorem Schedule.gap_slack_nonneg
    (schedule : Schedule) (who : Player) (time : ℕ) :
    0 ≤ schedule.gap schedule.slack who time := by
  rw [schedule.gap_eq_ownSurvival_mul]
  apply mul_nonneg (schedule.ownSurvival_nonneg who time)
  have hcap := schedule.one_add_prefixPotential_le_payoff_add_exploitability
    who time
  rw [schedule.terminalPayoff_eq_prescribedPayoff] at hcap
  unfold Schedule.slack
  linarith

/-- Own-clock friction at one date. -/
def Schedule.frictionTerm
    (schedule : Schedule) (who : Player) (time : ℕ) : ℝ :=
  frictionStep who (schedule.atom time)
    (schedule.gap schedule.slack who time)

/-- Signed on-path singleton mass at one date. -/
def Schedule.signedMassTerm
    (schedule : Schedule) (who : Player) (time : ℕ) : ℝ :=
  signedMassStep who (schedule.atom time)

theorem Schedule.frictionTerm_nonneg
    (schedule : Schedule) (who : Player) (time : ℕ) :
    0 ≤ schedule.frictionTerm who time := by
  unfold Schedule.frictionTerm frictionStep Schedule.atom
  split
  · exact mul_nonneg (schedule.gap_slack_nonneg who time)
      (schedule.hazard_nonneg time)
  · exact le_rfl

theorem Schedule.summable_signedMassTerm
    (schedule : Schedule) (who : Player) :
    Summable (schedule.signedMassTerm who) := by
  apply Summable.of_norm_bounded (schedule.summable_mass.mul_left 3)
  intro time
  have hmass := schedule.mass_nonneg time
  generalize howner : schedule.owner time = owner
  fin_cases who <;> fin_cases owner <;>
    simp [Schedule.signedMassTerm, Schedule.atom, signedMassStep, partner,
      abs_of_nonneg hmass, howner] <;> nlinarith

theorem Schedule.gap_add_sum_frictionTerm
    (schedule : Schedule) (who : Player) (time : ℕ) :
    schedule.gap schedule.slack who time +
        ∑ offset ∈ Finset.range time, schedule.frictionTerm who offset =
      schedule.slack who +
        ∑ offset ∈ Finset.range time,
          schedule.signedMassTerm who offset := by
  induction time with
  | zero => simp [Schedule.gap]
  | succ time ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hstep := gapStep_add_frictionStep who (schedule.atom time)
        (schedule.gap schedule.slack who time)
      change schedule.gap schedule.slack who (time + 1) +
          schedule.frictionTerm who time =
        schedule.gap schedule.slack who time +
          schedule.signedMassTerm who time at hstep
      linarith

theorem Schedule.sum_abs_signedMassTerm_le_three
    (schedule : Schedule) (who : Player) (time : ℕ) :
    ∑ offset ∈ Finset.range time, |schedule.signedMassTerm who offset| ≤ 3 := by
  calc
    ∑ offset ∈ Finset.range time, |schedule.signedMassTerm who offset| ≤
        ∑ offset ∈ Finset.range time, 3 * schedule.mass offset := by
          apply Finset.sum_le_sum
          intro offset _
          have hmass := schedule.mass_nonneg offset
          generalize howner : schedule.owner offset = owner
          fin_cases who <;> fin_cases owner <;>
            simp [Schedule.signedMassTerm, Schedule.atom, signedMassStep,
              partner, abs_of_nonneg hmass, howner] <;> nlinarith
    _ = 3 * (1 - schedule.survival time) := by
      rw [← Finset.mul_sum, schedule.sum_mass_eq_one_sub_survival]
    _ ≤ 3 := by nlinarith [schedule.survival_nonneg time]

theorem Schedule.summable_frictionTerm
    (schedule : Schedule) (who : Player) :
    Summable (schedule.frictionTerm who) := by
  apply summable_of_sum_range_le (c := schedule.slack who + 3)
    (fun time ↦ schedule.frictionTerm_nonneg who time)
  intro time
  have hidentity := schedule.gap_add_sum_frictionTerm who time
  have hgap := schedule.gap_slack_nonneg who time
  have hsigned :
      ∑ offset ∈ Finset.range time, schedule.signedMassTerm who offset ≤
        ∑ offset ∈ Finset.range time,
          |schedule.signedMassTerm who offset| := by
    apply Finset.sum_le_sum
    intro offset _
    exact le_abs_self _
  have habs := schedule.sum_abs_signedMassTerm_le_three who time
  linarith

private theorem signedMassTerm_eq_mass_sub_ownerTerms
    (schedule : Schedule) (who : Player) (time : ℕ) :
    schedule.signedMassTerm who time =
      schedule.mass time - schedule.ownerMassTerm who time -
        4 * schedule.ownerMassTerm (partner who) time := by
  generalize howner : schedule.owner time = owner
  fin_cases who <;> fin_cases owner <;>
    simp [Schedule.signedMassTerm, Schedule.atom, signedMassStep,
      Schedule.ownerMassTerm, partner, howner] <;> ring

theorem Schedule.tsum_signedMassTerm_eq
    (schedule : Schedule) (who : Player) :
    ∑' time, schedule.signedMassTerm who time =
      (∑' time, schedule.mass time) -
        prescribedPayoff schedule.ownerMass who := by
  simp_rw [signedMassTerm_eq_mass_sub_ownerTerms]
  rw [(schedule.summable_mass.sub
      (schedule.summable_ownerMassTerm who)).tsum_sub
        ((schedule.summable_ownerMassTerm (partner who)).mul_left 4),
    schedule.summable_mass.tsum_sub
      (schedule.summable_ownerMassTerm who), tsum_mul_left]
  unfold prescribedPayoff Schedule.ownerMass
  ring

private def Schedule.allOwnerMassTerm
    (schedule : Schedule) (time : ℕ) : ℝ :=
  schedule.ownerMassTerm 0 time + schedule.ownerMassTerm 1 time +
    schedule.ownerMassTerm 2 time + schedule.ownerMassTerm 3 time

private theorem Schedule.allOwnerMassTerm_eq_mass
    (schedule : Schedule) (time : ℕ) :
    schedule.allOwnerMassTerm time = schedule.mass time := by
  generalize howner : schedule.owner time = owner
  fin_cases owner <;> simp [Schedule.allOwnerMassTerm,
    Schedule.ownerMassTerm, howner]

theorem Schedule.total_ownerMass_eq_tsum_mass (schedule : Schedule) :
    totalMass schedule.ownerMass = ∑' time, schedule.mass time := by
  unfold totalMass Schedule.ownerMass
  simp only [Fin.sum_univ_four]
  rw [← (schedule.summable_ownerMassTerm 0).tsum_add
      (schedule.summable_ownerMassTerm 1),
    ← ((schedule.summable_ownerMassTerm 0).add
      (schedule.summable_ownerMassTerm 1)).tsum_add
        (schedule.summable_ownerMassTerm 2),
    ← (((schedule.summable_ownerMassTerm 0).add
      (schedule.summable_ownerMassTerm 1)).add
        (schedule.summable_ownerMassTerm 2)).tsum_add
          (schedule.summable_ownerMassTerm 3)]
  change (∑' time, schedule.allOwnerMassTerm time) = _
  apply tsum_congr
  exact schedule.allOwnerMassTerm_eq_mass

theorem Schedule.total_ownerMass_le_one (schedule : Schedule) :
    totalMass schedule.ownerMass ≤ 1 := by
  rw [schedule.total_ownerMass_eq_tsum_mass]
  exact schedule.summable_mass.tsum_le_of_sum_range_le fun time ↦ by
    rw [schedule.sum_mass_eq_one_sub_survival]
    exact sub_le_self 1 (schedule.survival_nonneg time)

/-- **Infinite budget consequence.**  Every player's total own-clock
friction is bounded by literal terminal exploitability. -/
theorem Schedule.tsum_frictionTerm_le_exploitability
    (schedule : Schedule) (who : Player) :
    (∑' time, schedule.frictionTerm who time) ≤
      schedule.exploitability := by
  have hfriction := schedule.summable_frictionTerm who
  have hsigned := schedule.summable_signedMassTerm who
  have hlimit : Tendsto (fun time ↦
      (∑ offset ∈ Finset.range time, schedule.frictionTerm who offset) -
        (schedule.slack who +
          ∑ offset ∈ Finset.range time,
            schedule.signedMassTerm who offset)) atTop
      (nhds ((∑' time, schedule.frictionTerm who time) -
        (schedule.slack who +
          ∑' time, schedule.signedMassTerm who time))) :=
    hfriction.hasSum.tendsto_sum_nat.sub
      (tendsto_const_nhds.add hsigned.hasSum.tendsto_sum_nat)
  have hle : (∑' time, schedule.frictionTerm who time) -
      (schedule.slack who +
        ∑' time, schedule.signedMassTerm who time) ≤ 0 := by
    apply le_of_tendsto hlimit
    filter_upwards [] with time
    have hidentity := schedule.gap_add_sum_frictionTerm who time
    have hgap := schedule.gap_slack_nonneg who time
    linarith
  rw [schedule.tsum_signedMassTerm_eq] at hle
  have htotal := schedule.total_ownerMass_le_one
  rw [schedule.total_ownerMass_eq_tsum_mass] at htotal
  unfold Schedule.slack at hle
  linarith

/-! ## Infinite tail potential -/

/-- Remaining on-path owner mass after a finite prefix. -/
def Schedule.remainingMass
    (schedule : Schedule) (owner : Player) (time : ℕ) : ℝ :=
  schedule.ownerMass owner -
    ∑ offset ∈ Finset.range time, schedule.ownerMassTerm owner offset

theorem Schedule.remainingMass_zero
    (schedule : Schedule) (owner : Player) :
    schedule.remainingMass owner 0 = schedule.ownerMass owner := by
  simp [Schedule.remainingMass]

theorem Schedule.remainingMass_succ
    (schedule : Schedule) (owner : Player) (time : ℕ) :
    schedule.remainingMass owner (time + 1) =
      schedule.remainingMass owner time - schedule.ownerMassTerm owner time := by
  simp [Schedule.remainingMass, Finset.sum_range_succ]
  ring

theorem Schedule.remainingMass_nonneg
    (schedule : Schedule) (owner : Player) (time : ℕ) :
    0 ≤ schedule.remainingMass owner time := by
  unfold Schedule.remainingMass Schedule.ownerMass
  exact sub_nonneg.mpr
    ((schedule.summable_ownerMassTerm owner).sum_le_tsum
      (Finset.range time) fun offset _ ↦ by
        unfold Schedule.ownerMassTerm
        split <;> simp_all [schedule.mass_nonneg offset])

theorem Schedule.tendsto_remainingMass_zero
    (schedule : Schedule) (owner : Player) :
    Tendsto (schedule.remainingMass owner) atTop (nhds 0) := by
  change Tendsto (fun time ↦ schedule.ownerMass owner -
    ∑ offset ∈ Finset.range time, schedule.ownerMassTerm owner offset)
    atTop (nhds 0)
  have hlimit : Tendsto (fun time ↦
      schedule.ownerMass owner -
        ∑ offset ∈ Finset.range time,
          schedule.ownerMassTerm owner offset) atTop
      (nhds (schedule.ownerMass owner - schedule.ownerMass owner)) :=
    tendsto_const_nhds.sub
      (schedule.summable_ownerMassTerm owner).hasSum.tendsto_sum_nat
  simpa using hlimit

/-- Remaining mass vector at a boundary. -/
def Schedule.remainingMassVector
    (schedule : Schedule) (time : ℕ) : PairMass :=
  fun owner ↦ schedule.remainingMass owner time

theorem Schedule.remainingMassVector_zero (schedule : Schedule) :
    schedule.remainingMassVector 0 = schedule.ownerMass := by
  funext owner
  exact schedule.remainingMass_zero owner

/-- Infinite tail coefficient charged at a date. -/
def Schedule.tailCoefficientAt
    (schedule : Schedule) (who : Player) (time : ℕ) : ℝ :=
  tailCoefficient (schedule.remainingMassVector time) who

private theorem Schedule.remainingSignedMass_eq_neg_tailCoefficient
    (schedule : Schedule) (who : Player) (time : ℕ) :
    (∑' offset, schedule.signedMassTerm who offset) -
        ∑ offset ∈ Finset.range time, schedule.signedMassTerm who offset =
      -schedule.tailCoefficientAt who time := by
  have hprefixSigned :
      ∑ offset ∈ Finset.range time, schedule.signedMassTerm who offset =
        (∑ offset ∈ Finset.range time, schedule.mass offset) -
          (∑ offset ∈ Finset.range time,
            schedule.ownerMassTerm who offset) -
          4 * ∑ offset ∈ Finset.range time,
            schedule.ownerMassTerm (partner who) offset := by
    simp_rw [signedMassTerm_eq_mass_sub_ownerTerms]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.mul_sum]
  have hprefixMass :
      ∑ offset ∈ Finset.range time, schedule.mass offset =
        (∑ offset ∈ Finset.range time,
          schedule.ownerMassTerm 0 offset) +
        (∑ offset ∈ Finset.range time,
          schedule.ownerMassTerm 1 offset) +
        (∑ offset ∈ Finset.range time,
          schedule.ownerMassTerm 2 offset) +
        (∑ offset ∈ Finset.range time,
          schedule.ownerMassTerm 3 offset) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro offset _
    exact (schedule.allOwnerMassTerm_eq_mass offset).symm
  have htotalMass := schedule.total_ownerMass_eq_tsum_mass
  unfold totalMass Schedule.ownerMass at htotalMass
  simp only [Fin.sum_univ_four] at htotalMass
  rw [schedule.tsum_signedMassTerm_eq, hprefixSigned,
    ← htotalMass, hprefixMass]
  unfold Schedule.tailCoefficientAt tailCoefficient oppositeMass
    totalMass Schedule.remainingMassVector Schedule.remainingMass
    prescribedPayoff Schedule.ownerMass
  simp only [Fin.sum_univ_four]
  fin_cases who <;> simp [partner] <;> ring

/-- Limit of the deflated gap obtained directly from the two convergent
series in the finite telescope. -/
def Schedule.gapLimit (schedule : Schedule) (who : Player) : ℝ :=
  schedule.slack who + ∑' time, schedule.signedMassTerm who time -
    ∑' time, schedule.frictionTerm who time

theorem Schedule.tendsto_gap_gapLimit
    (schedule : Schedule) (who : Player) :
    Tendsto (schedule.gap schedule.slack who) atTop
      (nhds (schedule.gapLimit who)) := by
  have hsigned := (schedule.summable_signedMassTerm who).hasSum.tendsto_sum_nat
  have hfriction := (schedule.summable_frictionTerm who).hasSum.tendsto_sum_nat
  have hlimit : Tendsto (fun time ↦
      schedule.slack who +
          ∑ offset ∈ Finset.range time,
            schedule.signedMassTerm who offset -
        ∑ offset ∈ Finset.range time,
          schedule.frictionTerm who offset) atTop
      (nhds (schedule.gapLimit who)) := by
    exact (tendsto_const_nhds.add hsigned).sub hfriction
  apply hlimit.congr'
  filter_upwards [] with time
  have hidentity := schedule.gap_add_sum_frictionTerm who time
  linarith

theorem Schedule.gapLimit_nonneg
    (schedule : Schedule) (who : Player) :
    0 ≤ schedule.gapLimit who := by
  apply ge_of_tendsto (schedule.tendsto_gap_gapLimit who)
  filter_upwards [] with time
  exact schedule.gap_slack_nonneg who time

theorem Schedule.remainingFriction_nonneg
    (schedule : Schedule) (who : Player) (time : ℕ) :
    0 ≤ (∑' offset, schedule.frictionTerm who offset) -
      ∑ offset ∈ Finset.range time, schedule.frictionTerm who offset := by
  exact sub_nonneg.mpr
    ((schedule.summable_frictionTerm who).sum_le_tsum
      (Finset.range time) fun offset _ ↦
        schedule.frictionTerm_nonneg who offset)

/-- The current deflated gap dominates the signed coefficient of all
remaining on-path mass. -/
theorem Schedule.tailCoefficientAt_le_gap
    (schedule : Schedule) (who : Player) (time : ℕ) :
    schedule.tailCoefficientAt who time ≤
      schedule.gap schedule.slack who time := by
  have hidentity := schedule.gap_add_sum_frictionTerm who time
  have hsigned := schedule.remainingSignedMass_eq_neg_tailCoefficient who time
  have hlimit := schedule.gapLimit_nonneg who
  have hfriction := schedule.remainingFriction_nonneg who time
  unfold Schedule.gapLimit at hlimit
  linarith

/-- Signed quadratic charge contributed by one calendar date. -/
def Schedule.chargeTerm (schedule : Schedule) (time : ℕ) : ℝ :=
  schedule.tailCoefficientAt (schedule.owner time) time * schedule.mass time

/-- One date's quadratic charge is bounded by the friction paid on the
active owner's clock. -/
theorem Schedule.chargeTerm_le_ownerFriction
    (schedule : Schedule) (time : ℕ) :
    schedule.chargeTerm time ≤
      schedule.frictionTerm (schedule.owner time) time := by
  have hmass0 := schedule.mass_nonneg time
  have hhazard0 := schedule.hazard_nonneg time
  have hmass := schedule.mass_le_hazard time
  have hgap0 := schedule.gap_slack_nonneg (schedule.owner time) time
  have hcoefficient := schedule.tailCoefficientAt_le_gap
    (schedule.owner time) time
  unfold Schedule.chargeTerm Schedule.frictionTerm frictionStep Schedule.atom
  simp only [if_pos]
  by_cases hcoefficient0 :
      0 ≤ schedule.tailCoefficientAt (schedule.owner time) time
  · calc
      schedule.tailCoefficientAt (schedule.owner time) time *
          schedule.mass time ≤
          schedule.gap schedule.slack (schedule.owner time) time *
            schedule.mass time :=
        mul_le_mul_of_nonneg_right hcoefficient hmass0
      _ ≤ schedule.gap schedule.slack (schedule.owner time) time *
          schedule.hazard time :=
        mul_le_mul_of_nonneg_left hmass hgap0
  · have hcoefficientNonpos :
        schedule.tailCoefficientAt (schedule.owner time) time ≤ 0 :=
      le_of_not_ge hcoefficient0
    exact (mul_nonpos_of_nonpos_of_nonneg hcoefficientNonpos hmass0).trans
      (mul_nonneg hgap0 hhazard0)

/-- The signed charge is exactly the one-step decrease of the quadratic
remaining-mass potential. -/
theorem Schedule.quadraticCharge_remainingMass_sub_succ
    (schedule : Schedule) (time : ℕ) :
    quadraticCharge (schedule.remainingMassVector time) -
        quadraticCharge (schedule.remainingMassVector (time + 1)) =
      schedule.chargeTerm time := by
  generalize howner : schedule.owner time = owner
  fin_cases owner <;>
    simp [Schedule.chargeTerm, Schedule.tailCoefficientAt,
      Schedule.remainingMassVector, schedule.remainingMass_succ,
      Schedule.ownerMassTerm, howner, quadraticCharge,
      firstPairMass, secondPairMass, tailCoefficient, oppositeMass,
      totalMass, partner, Fin.sum_univ_four] <;> ring

theorem Schedule.remainingMass_le_ownerMass
    (schedule : Schedule) (owner : Player) (time : ℕ) :
    schedule.remainingMass owner time ≤ schedule.ownerMass owner := by
  unfold Schedule.remainingMass
  exact sub_le_self _ (Finset.sum_nonneg fun offset _ ↦ by
    unfold Schedule.ownerMassTerm
    split <;> simp_all [schedule.mass_nonneg offset])

theorem Schedule.abs_tailCoefficientAt_le_three
    (schedule : Schedule) (who : Player) (time : ℕ) :
    |schedule.tailCoefficientAt who time| ≤ 3 := by
  have htotal := schedule.total_ownerMass_le_one
  unfold totalMass at htotal
  simp only [Fin.sum_univ_four] at htotal
  have hr0 := schedule.remainingMass_nonneg 0 time
  have hr1 := schedule.remainingMass_nonneg 1 time
  have hr2 := schedule.remainingMass_nonneg 2 time
  have hr3 := schedule.remainingMass_nonneg 3 time
  have hu0 := schedule.remainingMass_le_ownerMass 0 time
  have hu1 := schedule.remainingMass_le_ownerMass 1 time
  have hu2 := schedule.remainingMass_le_ownerMass 2 time
  have hu3 := schedule.remainingMass_le_ownerMass 3 time
  unfold Schedule.tailCoefficientAt tailCoefficient oppositeMass totalMass
    Schedule.remainingMassVector
  simp only [Fin.sum_univ_four]
  fin_cases who <;> simp [partner, abs_le] <;> constructor <;> nlinarith

theorem Schedule.summable_chargeTerm (schedule : Schedule) :
    Summable schedule.chargeTerm := by
  apply Summable.of_norm_bounded (schedule.summable_mass.mul_left 3)
  intro time
  rw [Real.norm_eq_abs, Schedule.chargeTerm, abs_mul]
  have habs := schedule.abs_tailCoefficientAt_le_three
    (schedule.owner time) time
  rw [abs_of_nonneg (schedule.mass_nonneg time)]
  exact mul_le_mul_of_nonneg_right habs (schedule.mass_nonneg time)

theorem Schedule.sum_chargeTerm_eq_potential_sub
    (schedule : Schedule) (time : ℕ) :
    ∑ offset ∈ Finset.range time, schedule.chargeTerm offset =
      quadraticCharge schedule.ownerMass -
        quadraticCharge (schedule.remainingMassVector time) := by
  induction time with
  | zero => simp [schedule.remainingMassVector_zero]
  | succ time ih =>
      rw [Finset.sum_range_succ, ih]
      have hstep := schedule.quadraticCharge_remainingMass_sub_succ time
      linarith

theorem Schedule.tendsto_quadraticCharge_remainingMass_zero
    (schedule : Schedule) :
    Tendsto (fun time ↦ quadraticCharge (schedule.remainingMassVector time))
      atTop (nhds 0) := by
  have h0 := schedule.tendsto_remainingMass_zero 0
  have h1 := schedule.tendsto_remainingMass_zero 1
  have h2 := schedule.tendsto_remainingMass_zero 2
  have h3 := schedule.tendsto_remainingMass_zero 3
  have h01 : Tendsto (fun time ↦
      3 * schedule.remainingMass 0 time *
        schedule.remainingMass 1 time) atTop (nhds 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds.mul h0).mul h1
  have h23 : Tendsto (fun time ↦
      3 * schedule.remainingMass 2 time *
        schedule.remainingMass 3 time) atTop (nhds 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds.mul h2).mul h3
  have hcross : Tendsto (fun time ↦
      (schedule.remainingMass 0 time + schedule.remainingMass 1 time) *
        (schedule.remainingMass 2 time +
          schedule.remainingMass 3 time)) atTop (nhds 0) := by
    simpa only [zero_add, zero_mul] using (h0.add h1).mul (h2.add h3)
  simpa [quadraticCharge, firstPairMass, secondPairMass,
    Schedule.remainingMassVector] using (h01.add h23).sub hcross

theorem Schedule.hasSum_chargeTerm (schedule : Schedule) :
    HasSum schedule.chargeTerm (quadraticCharge schedule.ownerMass) := by
  apply (schedule.summable_chargeTerm.hasSum_iff_tendsto_nat).2
  have hlimit : Tendsto (fun time ↦
      quadraticCharge schedule.ownerMass -
        quadraticCharge (schedule.remainingMassVector time)) atTop
      (nhds (quadraticCharge schedule.ownerMass)) := by
    simpa using tendsto_const_nhds.sub
      schedule.tendsto_quadraticCharge_remainingMass_zero
  apply hlimit.congr'
  filter_upwards [] with time
  exact (schedule.sum_chargeTerm_eq_potential_sub time).symm

theorem Schedule.ownerFriction_le_sum_frictionTerm
    (schedule : Schedule) (time : ℕ) :
    schedule.frictionTerm (schedule.owner time) time ≤
      ∑ who, schedule.frictionTerm who time := by
  have h0 := schedule.frictionTerm_nonneg 0 time
  have h1 := schedule.frictionTerm_nonneg 1 time
  have h2 := schedule.frictionTerm_nonneg 2 time
  have h3 := schedule.frictionTerm_nonneg 3 time
  simp only [Fin.sum_univ_four]
  generalize howner : schedule.owner time = owner
  fin_cases owner <;> simp <;> linarith

theorem Schedule.sum_chargeTerm_le_four_exploitability
    (schedule : Schedule) (time : ℕ) :
    ∑ offset ∈ Finset.range time, schedule.chargeTerm offset ≤
      4 * schedule.exploitability := by
  calc
    ∑ offset ∈ Finset.range time, schedule.chargeTerm offset ≤
        ∑ offset ∈ Finset.range time,
          schedule.frictionTerm (schedule.owner offset) offset := by
      exact Finset.sum_le_sum fun offset _ ↦
        schedule.chargeTerm_le_ownerFriction offset
    _ ≤ ∑ offset ∈ Finset.range time,
          ∑ who, schedule.frictionTerm who offset := by
      exact Finset.sum_le_sum fun offset _ ↦
        schedule.ownerFriction_le_sum_frictionTerm offset
    _ = ∑ who, ∑ offset ∈ Finset.range time,
          schedule.frictionTerm who offset := by
      exact Finset.sum_comm
    _ ≤ ∑ _who : Player, schedule.exploitability := by
      apply Finset.sum_le_sum
      intro who _
      exact ((schedule.summable_frictionTerm who).sum_le_tsum
        (Finset.range time) fun offset _ ↦
          schedule.frictionTerm_nonneg who offset).trans
            (schedule.tsum_frictionTerm_le_exploitability who)
    _ = 4 * schedule.exploitability := by
      simp

/-- The quadratic charge interface consumed by the finite algebraic floor. -/
def Schedule.SuppliesQuadraticChargeBound (schedule : Schedule) : Prop :=
  quadraticCharge schedule.ownerMass ≤ 4 * schedule.exploitability

/-- Every literal solo-hazard calendar supplies the quadratic charge bound. -/
theorem Schedule.suppliesQuadraticChargeBound (schedule : Schedule) :
    schedule.SuppliesQuadraticChargeBound := by
  apply le_of_tendsto schedule.hasSum_chargeTerm.tendsto_sum_nat
  filter_upwards [] with time
  exact schedule.sum_chargeTerm_le_four_exploitability time

/-- **Semantic floor conditional only on the infinite friction producer.** -/
theorem Schedule.explicitFloor_of_suppliesQuadraticChargeBound
    (schedule : Schedule)
    (hcharge : schedule.SuppliesQuadraticChargeBound) :
    1 ≤ 14 * schedule.exploitability ^ 2 +
      67 * schedule.exploitability := by
  apply explicitFloor_of_errorData schedule.exploitability
    schedule.exploitability_nonneg
  intro _
  exact ⟨schedule.ownerMass, schedule.ownerMass_nonneg,
    schedule.total_ownerMass_le_one, schedule.singletonFloor, hcharge⟩

theorem Schedule.one_over_sixtyEight_lt_exploitability
    (schedule : Schedule)
    (hcharge : schedule.SuppliesQuadraticChargeBound) :
    1 / 68 < schedule.exploitability :=
  one_over_sixtyEight_lt_of_explicitFloor schedule.exploitability_nonneg
    (schedule.explicitFloor_of_suppliesQuadraticChargeBound hcharge)

/-- Exact quadratic lower constraint for literal solo-hazard calendars. -/
theorem Schedule.literalExploitability_explicitFloor (schedule : Schedule) :
    1 ≤ 14 * schedule.exploitability ^ 2 +
      67 * schedule.exploitability :=
  schedule.explicitFloor_of_suppliesQuadraticChargeBound
    schedule.suppliesQuadraticChargeBound

/-- **Semantic quantitative solo-hazard no-go.**  Every arbitrary infinite
solo-hazard calendar has literal all-behavior terminal exploitability strictly
larger than `1 / 68`. -/
theorem Schedule.one_over_sixtyEight_lt_literal_exploitability
    (schedule : Schedule) :
    1 / 68 < schedule.exploitability :=
  schedule.one_over_sixtyEight_lt_exploitability
    schedule.suppliesQuadraticChargeBound

end SoloHazardLedger
end SolanVieilleBoundary
end GameTheory

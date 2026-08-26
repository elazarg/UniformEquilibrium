/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.FiniteDeadlineNashDebtBounds
import UniformEquilibrium.Diagnostics.Quitting.FiniteDeadlineTimingGame
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFiniteDeadlineNashEscalation
import UniformEquilibrium.Quitting.Boundary.Exceptional.BellmanTail
import UniformEquilibrium.Quitting.Cycles.PhaseSwitchProfile
import UniformEquilibrium.Quitting.Terminal.OpponentTightTerminalSemanticRealization
import UniformEquilibrium.ProofView.Concepts.Existence.NashExistenceMixed

/-!
# Two-date timing Nash terminal debt

Every finite quitting game has a mixed Nash equilibrium in the timing game
whose pure actions are date zero, date one, and Never. Its literal behavioral
realization preserves the planned stopping laws, is Continue-only from date
two onward, and has unrestricted behavioral terminal debt at most half a
uniform terminal-reward bound.

The proof first packages the timing Nash equilibrium as a
`QuittingFiniteDeadlineNashProfile`. It then compares a late quit with Never,
date one, and date zero. The resulting three scalar bounds have common worst
case `bound / 2`.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def quittingTwoDateRoots
    (first second : ι → PMF Bool) : ℕ → ι → PMF Bool
  | 0 => first
  | 1 => second
  | _ => quittingAllContinueRoot

def quittingTwoDateRootProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : ι → PMF Bool) :
    (quittingGame reward).BehaviorProfile :=
  quittingRootSequenceProfile reward (quittingTwoDateRoots first second) 0

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingTwoDateRoots_zero
    (first second : ι → PMF Bool) :
    quittingTwoDateRoots first second 0 = first := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingTwoDateRoots_one
    (first second : ι → PMF Bool) :
    quittingTwoDateRoots first second 1 = second := rfl

omit [DecidableEq ι] in
theorem quittingTwoDateRoots_eq_allContinue_of_two_le
    (first second : ι → PMF Bool) {time : ℕ} (htime : 2 ≤ time) :
    quittingTwoDateRoots first second time = quittingAllContinueRoot := by
  cases time with
  | zero => omega
  | succ time =>
      cases time with
      | zero => omega
      | succ time => rfl

theorem quittingTwoDateRootProfile_isFiniteDeadline
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : ι → PMF Bool)
    (hpure : ∀ (who : ι) (quitTime : Option ℕ),
      (quitTime = none ∨ ∃ time < 2, quitTime = some time) →
        quittingTerminalPayoff reward
            (Function.update
              (quittingTwoDateRootProfile reward first second) who
              (quittingPureTimeBehaviorStrategy reward who quitTime)) who ≤
          quittingTerminalPayoff reward
            (quittingTwoDateRootProfile reward first second) who) :
    QuittingFiniteDeadlineNashProfile reward
      (quittingTwoDateRootProfile reward first second) 2 := by
  constructor
  · intro time htime
    rw [quittingTwoDateRootProfile,
      quittingProfileLiveRoot_quittingRootSequenceProfile_zero]
    exact quittingTwoDateRoots_eq_allContinue_of_two_le first second htime
  · exact hpure

private theorem twoDate_scalar_bound
    (bound solo debt neverMass zeroMass oneMass : ℝ)
    (hbound : 0 ≤ bound) (hsolo0 : 0 < solo) (hsolo : solo ≤ bound)
    (hzeroMass : 0 ≤ zeroMass)
    (hsum : neverMass + zeroMass + oneMass = 1)
    (hnever : debt ≤ neverMass * solo)
    (hone : debt ≤ 2 * bound * oneMass)
    (hzero : debt ≤
      2 * bound * zeroMass + (bound - solo) * oneMass) :
    debt ≤ bound / 2 := by
  by_contra h
  have hgt : bound / 2 < debt := lt_of_not_ge h
  have hboundPos : 0 < bound := hsolo0.trans_le hsolo
  have hsoloMul : solo * solo ≤ bound * solo :=
    mul_le_mul_of_nonneg_right hsolo hsolo0.le
  nlinarith [mul_pos (sub_pos.mpr hgt) hsolo0,
    mul_pos (sub_pos.mpr hgt) hboundPos,
    mul_nonneg hzeroMass hboundPos.le]

private theorem twoDate_neverValue_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : ι → PMF Bool) (who : ι) :
    quittingTerminalPayoff reward
        (Function.update (quittingTwoDateRootProfile reward first second) who
          (quittingPureTimeBehaviorStrategy reward who none)) who =
      quittingFixedOpponentsContinueReward reward
          (quittingTwoDateRoots first second) who 0 +
        quittingFixedOpponentsContinueMass
            (quittingTwoDateRoots first second) who 0 *
          quittingFixedOpponentsContinueReward reward
            (quittingTwoDateRoots first second) who 1 := by
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    quittingTwoDateRootProfile,
    quittingProfileLiveRoot_quittingRootSequenceProfile_zero,
    quittingRootSequencePureTimeTerminalValue_none_succ_eq_fixedOpponents,
    quittingRootSequencePureTimeTerminalValue_none_succ_eq_fixedOpponents]
  have htail : quittingRootSequencePureTimeTerminalValue reward
      (quittingTwoDateRoots first second) who none 2 = 0 := by
    apply quittingRootSequencePureTimeTerminalValue_none_eq_zero_of_allContinue_from
    intro time htime
    exact quittingTwoDateRoots_eq_allContinue_of_two_le first second htime
  rw [htail, mul_zero, add_zero]

private theorem twoDate_timeZeroValue_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : ι → PMF Bool) (who : ι) :
    quittingTerminalPayoff reward
        (Function.update (quittingTwoDateRootProfile reward first second) who
          (quittingPureTimeBehaviorStrategy reward who (some 0))) who =
      quittingFixedOpponentsQuitValue reward
        (quittingTwoDateRoots first second) who 0 := by
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    quittingTwoDateRootProfile,
    quittingProfileLiveRoot_quittingRootSequenceProfile_zero]
  exact quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents
    reward (quittingTwoDateRoots first second) who 0

private theorem twoDate_timeOneValue_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : ι → PMF Bool) (who : ι) :
    quittingTerminalPayoff reward
        (Function.update (quittingTwoDateRootProfile reward first second) who
          (quittingPureTimeBehaviorStrategy reward who (some 1))) who =
      quittingFixedOpponentsContinueReward reward
          (quittingTwoDateRoots first second) who 0 +
        quittingFixedOpponentsContinueMass
            (quittingTwoDateRoots first second) who 0 *
          quittingFixedOpponentsQuitValue reward
            (quittingTwoDateRoots first second) who 1 := by
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    quittingTwoDateRootProfile,
    quittingProfileLiveRoot_quittingRootSequenceProfile_zero]
  have htail : quittingRootSequenceHazardTerminalValue reward
      (quittingTwoDateRoots first second) who
        (quittingPureTimeHazard (some 1)) 1 =
      quittingFixedOpponentsQuitValue reward
        (quittingTwoDateRoots first second) who 1 := by
    exact quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents
      reward (quittingTwoDateRoots first second) who 1
  unfold quittingRootSequencePureTimeTerminalValue
  rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
  simp [quittingPureTimeHazard_some_of_ne (by omega : 0 ≠ 1), htail]

private theorem twoDate_opponentSurvival_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : ι → PMF Bool) (who : ι) :
    quittingFiniteDeadlineOpponentSurvival reward
        (quittingTwoDateRootProfile reward first second) 2 who =
      quittingFixedOpponentsContinueMass
          (quittingTwoDateRoots first second) who 0 *
        quittingFixedOpponentsContinueMass
          (quittingTwoDateRoots first second) who 1 := by
  rw [quittingFiniteDeadlineOpponentSurvival, quittingTwoDateRootProfile,
    quittingProfileLiveRoot_quittingRootSequenceProfile_zero]
  simp [quittingOpponentSurvivalWeight, Finset.prod_range_succ]

/-- Scalar data retained by the two-date proof. `neverMass`, `zeroMass`, and
`oneMass` are respectively the opponent events: survive both dates, absorb at
date zero, and survive date zero then absorb at date one. -/
def TwoDatePhaseMassDebtCertificate
    (bound solo debt neverMass zeroMass oneMass : ℝ) : Prop :=
  (solo ≤ 0 → debt = 0) ∧
    (0 < solo →
      debt ≤ neverMass * solo ∧
      debt ≤ 2 * bound * oneMass ∧
      debt ≤ 2 * bound * zeroMass + (bound - solo) * oneMass)

/-- A literal two-root profile that is Nash against times zero, one, and
Never retains the exact three phase-mass debt inequalities. -/
theorem quittingTerminalDeviationDebt_twoDateRootProfile_dataSensitive
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : ι → PMF Bool) (who : ι) {bound : ℝ}
    (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (certificate : QuittingFiniteDeadlineNashProfile reward
      (quittingTwoDateRootProfile reward first second) 2) :
    let roots := quittingTwoDateRoots first second
    let profile := quittingTwoDateRootProfile reward first second
    let debt := quittingTerminalDeviationDebt reward profile who
    let solo := reward (quittingSingletonTerminal who) who
    let firstMass := quittingFixedOpponentsContinueMass roots who 0
    let secondMass := quittingFixedOpponentsContinueMass roots who 1
    TwoDatePhaseMassDebtCertificate bound solo debt
      (firstMass * secondMass) (1 - firstMass)
      (firstMass * (1 - secondMass)) := by
  let roots := quittingTwoDateRoots first second
  let profile := quittingTwoDateRootProfile reward first second
  let debt := quittingTerminalDeviationDebt reward profile who
  let prescribed := quittingTerminalPayoff reward profile who
  let neverValue := quittingTerminalPayoff reward
    (Function.update profile who
      (quittingPureTimeBehaviorStrategy reward who none)) who
  let solo := reward (quittingSingletonTerminal who) who
  let firstMass := quittingFixedOpponentsContinueMass roots who 0
  let secondMass := quittingFixedOpponentsContinueMass roots who 1
  let allNeverMass := firstMass * secondMass
  let zeroMass := 1 - firstMass
  let oneMass := firstMass * (1 - secondMass)
  let lateValue := neverValue + allNeverMass * solo
  have hdebt0 : 0 ≤ debt :=
    quittingTerminalDeviationDebt_nonneg reward profile who
  have hfirst0 : 0 ≤ firstMass :=
    quittingFixedOpponentsContinueMass_nonneg roots who 0
  have hfirst1 : firstMass ≤ 1 :=
    quittingFixedOpponentsContinueMass_le_one roots who 0
  have hsecond0 : 0 ≤ secondMass :=
    quittingFixedOpponentsContinueMass_nonneg roots who 1
  have hsecond1 : secondMass ≤ 1 :=
    quittingFixedOpponentsContinueMass_le_one roots who 1
  have hzeroMass0 : 0 ≤ zeroMass := by dsimp only [zeroMass]; linarith
  change TwoDatePhaseMassDebtCertificate bound solo debt
    allNeverMass zeroMass oneMass
  unfold TwoDatePhaseMassDebtCertificate
  constructor
  · intro hsolo
    have hescape := certificate.semanticDebt_le_escapeCharge who
    have hescapeZero :
        quittingFiniteDeadlineEscapeCharge reward profile 2 who = 0 := by
      simp [quittingFiniteDeadlineEscapeCharge, solo, max_eq_left hsolo]
    rw [hescapeZero] at hescape
    exact le_antisymm hescape hdebt0
  · intro hsolo0
    have hsoloBound : solo ≤ bound :=
      le_of_abs_le (hreward (quittingSingletonTerminal who) who)
    have hbest : quittingContinuationBestResponseValue reward profile who ≤
        max prescribed lateValue := by
      have hcap := certificate.bestResponseValue_le_max_late who hsolo0.le
      rw [twoDate_opponentSurvival_eq reward first second who] at hcap
      exact hcap
    have hnever : debt ≤ allNeverMass * solo := by
      have hescape := certificate.semanticDebt_le_escapeCharge who
      rw [show quittingFiniteDeadlineEscapeCharge reward profile 2 who =
          allNeverMass * solo by
        unfold quittingFiniteDeadlineEscapeCharge
        rw [max_eq_right hsolo0.le,
          twoDate_opponentSurvival_eq reward first second who]] at hescape
      exact hescape
    have hpureOne : quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who (some 1))) who ≤
        prescribed := by
      exact certificate.pureTime_le who (some 1)
        (Or.inr ⟨1, by omega, rfl⟩)
    have hpureZero : quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who (some 0))) who ≤
        prescribed := by
      exact certificate.pureTime_le who (some 0)
        (Or.inr ⟨0, by omega, rfl⟩)
    have hstageOne :
        quittingFixedOpponentsContinueReward reward roots who 1 +
              secondMass * solo -
            quittingFixedOpponentsQuitValue reward roots who 1 ≤
          2 * bound * (1 - secondMass) := by
      exact quittingFixedOpponentsContinue_add_solo_sub_quit_le
        reward roots who 1 hbound hreward
    have hlateOne : lateValue -
          quittingTerminalPayoff reward
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy reward who (some 1))) who ≤
        2 * bound * oneMass := by
      dsimp only [lateValue, neverValue, allNeverMass, oneMass, firstMass,
        secondMass, roots, profile] at hstageOne ⊢
      rw [twoDate_neverValue_eq reward first second who,
        twoDate_timeOneValue_eq reward first second who]
      nlinarith [mul_nonneg hfirst0
        (sub_nonneg.mpr hsecond1)]
    have hcontinueOne :
        quittingFixedOpponentsContinueReward reward roots who 1 ≤
          bound * (1 - secondMass) := by
      exact quittingFixedOpponentsContinueReward_le
        reward roots who 1 hbound hreward
    have hstageZero :
        quittingFixedOpponentsContinueReward reward roots who 0 +
              firstMass * solo -
            quittingFixedOpponentsQuitValue reward roots who 0 ≤
          2 * bound * (1 - firstMass) := by
      exact quittingFixedOpponentsContinue_add_solo_sub_quit_le
        reward roots who 0 hbound hreward
    have hcontinueScaled : firstMass *
          quittingFixedOpponentsContinueReward reward roots who 1 ≤
        firstMass * (bound * (1 - secondMass)) :=
      mul_le_mul_of_nonneg_left hcontinueOne hfirst0
    have hlateZero : lateValue -
          quittingTerminalPayoff reward
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy reward who (some 0))) who ≤
        2 * bound * zeroMass + (bound - solo) * oneMass := by
      dsimp only [lateValue, neverValue, allNeverMass, zeroMass, oneMass,
        firstMass, secondMass, roots, profile] at hstageZero hcontinueScaled ⊢
      rw [twoDate_neverValue_eq reward first second who,
        twoDate_timeZeroValue_eq reward first second who]
      nlinarith
    have hone : debt ≤ 2 * bound * oneMass := by
      by_cases hlate : lateValue ≤ prescribed
      · change quittingContinuationBestResponseValue reward profile who -
          quittingTerminalPayoff reward profile who ≤ _
        have : quittingContinuationBestResponseValue reward profile who ≤
            prescribed := hbest.trans (max_eq_left hlate).le
        have hright : 0 ≤ 2 * bound * oneMass := by
          dsimp only [oneMass]
          positivity
        linarith
      · have hlatePrescribed : prescribed < lateValue := lt_of_not_ge hlate
        change quittingContinuationBestResponseValue reward profile who -
          quittingTerminalPayoff reward profile who ≤ _
        rw [max_eq_right hlatePrescribed.le] at hbest
        linarith
    have hzero : debt ≤
        2 * bound * zeroMass + (bound - solo) * oneMass := by
      by_cases hlate : lateValue ≤ prescribed
      · change quittingContinuationBestResponseValue reward profile who -
          quittingTerminalPayoff reward profile who ≤ _
        have hcap : quittingContinuationBestResponseValue reward profile who ≤
            prescribed := hbest.trans (max_eq_left hlate).le
        have hright : 0 ≤
            2 * bound * zeroMass + (bound - solo) * oneMass := by
          have : 0 ≤ oneMass := by dsimp only [oneMass]; positivity
          positivity
        linarith
      · have hlatePrescribed : prescribed < lateValue := lt_of_not_ge hlate
        change quittingContinuationBestResponseValue reward profile who -
          quittingTerminalPayoff reward profile who ≤ _
        rw [max_eq_right hlatePrescribed.le] at hbest
        linarith
    exact ⟨hnever, hone, hzero⟩

/-- The three phase-mass inequalities have common worst case `bound / 2`. -/
theorem quittingTerminalDeviationDebt_twoDateRootProfile_le_half
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : ι → PMF Bool) (who : ι) {bound : ℝ}
    (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (certificate : QuittingFiniteDeadlineNashProfile reward
      (quittingTwoDateRootProfile reward first second) 2) :
    quittingTerminalDeviationDebt reward
        (quittingTwoDateRootProfile reward first second) who ≤ bound / 2 := by
  let roots := quittingTwoDateRoots first second
  let profile := quittingTwoDateRootProfile reward first second
  let debt := quittingTerminalDeviationDebt reward profile who
  let solo := reward (quittingSingletonTerminal who) who
  let firstMass := quittingFixedOpponentsContinueMass roots who 0
  let secondMass := quittingFixedOpponentsContinueMass roots who 1
  let allNeverMass := firstMass * secondMass
  let zeroMass := 1 - firstMass
  let oneMass := firstMass * (1 - secondMass)
  have hcertificate :=
    quittingTerminalDeviationDebt_twoDateRootProfile_dataSensitive
      reward first second who hbound hreward certificate
  change debt ≤ bound / 2
  change TwoDatePhaseMassDebtCertificate bound solo debt
    allNeverMass zeroMass oneMass at hcertificate
  unfold TwoDatePhaseMassDebtCertificate at hcertificate
  by_cases hsolo : solo ≤ 0
  · rw [hcertificate.1 hsolo]
    positivity
  · have hsolo0 : 0 < solo := lt_of_not_ge hsolo
    obtain ⟨hnever, hone, hzero⟩ := hcertificate.2 hsolo0
    have hsoloBound : solo ≤ bound :=
      le_of_abs_le (hreward (quittingSingletonTerminal who) who)
    have hfirst0 : 0 ≤ firstMass :=
      quittingFixedOpponentsContinueMass_nonneg roots who 0
    have hfirst1 : firstMass ≤ 1 :=
      quittingFixedOpponentsContinueMass_le_one roots who 0
    have hsecond0 : 0 ≤ secondMass :=
      quittingFixedOpponentsContinueMass_nonneg roots who 1
    have hsecond1 : secondMass ≤ 1 :=
      quittingFixedOpponentsContinueMass_le_one roots who 1
    have hzeroMass0 : 0 ≤ zeroMass := by
      dsimp only [zeroMass]
      linarith
    have hmassSum : allNeverMass + zeroMass + oneMass = 1 := by
      dsimp only [allNeverMass, zeroMass, oneMass]
      ring
    exact twoDate_scalar_bound bound solo debt allNeverMass zeroMass oneMass
      hbound hsolo0 hsoloBound hzeroMass0 hmassSum hnever hone hzero

/-! ## Three-action timing-game producer -/

/-- Planned action in the hard-tail timing game: date zero, date one, or
Never. -/
abbrev QuittingTwoDateTimingAction := QuittingFiniteDeadlineTimingAction 2

/-- Read a finite timing-game action as a complete stopping time. -/
abbrev quittingTwoDateTimingActionTime :
    QuittingTwoDateTimingAction → Math.Probability.CompactStoppingTime :=
  quittingFiniteDeadlineTimingActionTime

/-- The finite strategic-form timing game whose actions are `0`, `1`, and
Never and whose pure payoffs are the literal deterministic stopping profile
payoffs. -/
abbrev quittingTwoDateTimingGame
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : KernelGame ι :=
  quittingFiniteDeadlineTimingGame reward 2

/-- Complete stopping law obtained by mapping a mixed timing action to its
literal date or Never. -/
abbrev quittingTwoDateTimingLaw
    (mixed : PMF QuittingTwoDateTimingAction) :
    Math.Probability.CompactStoppingLaw :=
  quittingFiniteDeadlineTimingLaw mixed

/-- Literal behavioral-hazard realization of independent mixed planned-time
laws. -/
abbrev quittingTwoDateTimingProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mixed : ι → PMF QuittingTwoDateTimingAction) :
    (quittingGame reward).BehaviorProfile :=
  quittingFiniteDeadlineTimingProfile reward 2 mixed

/-- The behavioral realization of a two-date timing law has the timing
game's mixed expected payoff. -/
theorem quittingTerminalPayoff_twoDateTimingProfile_eq_mixedEU
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mixed : ι → PMF QuittingTwoDateTimingAction) (who : ι) :
    quittingTerminalPayoff reward
        (quittingTwoDateTimingProfile reward mixed) who =
      (quittingTwoDateTimingGame reward).mixedExtension.eu mixed who :=
  quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU
    reward 2 mixed who

/-- A pure two-date timing deviation has the same payoff in the behavioral
realization and in the timing game's mixed extension. -/
theorem quittingTwoDateTimingProfile_update_pureTime_eq_mixedEU
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mixed : ι → PMF QuittingTwoDateTimingAction)
    (who : ι) (action : QuittingTwoDateTimingAction) :
    quittingTerminalPayoff reward
        (Function.update
          (quittingTwoDateTimingProfile reward mixed) who
          (quittingPureTimeBehaviorStrategy reward who
            (quittingTwoDateTimingActionTime action))) who =
      (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update mixed who (PMF.pure action)) who :=
  quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU
    reward 2 mixed who action

theorem quittingTwoDateTimingLaw_some_eq_zero_of_two_le
    (mixed : PMF QuittingTwoDateTimingAction) {time : ℕ}
    (htime : 2 ≤ time) :
    (quittingTwoDateTimingLaw mixed).toPMF (WithTop.some time) = 0 :=
  quittingFiniteDeadlineTimingLaw_some_eq_zero_of_le mixed htime

omit [DecidableEq ι] in
theorem quittingTwoDateTimingProfile_liveRoot_eq_allContinue_of_two_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mixed : ι → PMF QuittingTwoDateTimingAction)
    {time : ℕ} (htime : 2 ≤ time) :
    quittingProfileLiveRoot reward
        (quittingTwoDateTimingProfile reward mixed) time =
      quittingAllContinueRoot :=
  quittingFiniteDeadlineTimingProfile_liveRoot_eq_allContinue_of_le
    reward 2 mixed htime

omit [DecidableEq ι] in
private theorem quittingTwoDateTimingProfile_eq_twoDateRootProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mixed : ι → PMF QuittingTwoDateTimingAction) :
    quittingTwoDateTimingProfile reward mixed =
      quittingTwoDateRootProfile reward
        (quittingProfileLiveRoot reward
          (quittingTwoDateTimingProfile reward mixed) 0)
        (quittingProfileLiveRoot reward
          (quittingTwoDateTimingProfile reward mixed) 1) := by
  funext who time history
  cases time with
  | zero =>
      rfl
  | succ time =>
      cases time with
      | zero =>
          rfl
      | succ time =>
          change quittingProfileLiveRoot reward
              (quittingTwoDateTimingProfile reward mixed) (time + 2) who =
            quittingAllContinueRoot who
          exact congrFun
            (quittingTwoDateTimingProfile_liveRoot_eq_allContinue_of_two_le
              reward mixed (by omega)) who

/-- A mixed Nash equilibrium of the three-action timing game realizes a
literal finite-deadline Nash profile. -/
theorem quittingTwoDateTimingProfile_isFiniteDeadline
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mixed : ι → PMF QuittingTwoDateTimingAction)
    (hnash : (quittingTwoDateTimingGame reward).mixedExtension.IsNash mixed) :
    QuittingFiniteDeadlineNashProfile reward
      (quittingTwoDateTimingProfile reward mixed) 2 :=
  quittingFiniteDeadlineTimingProfile_isFiniteDeadline reward 2 mixed hnash

/-- A mixed timing Nash realization retains the exact phase-mass certificate
for the two live roots selected by its stopping laws. -/
theorem quittingTerminalDeviationDebt_twoDateTimingProfile_dataSensitive
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mixed : ι → PMF QuittingTwoDateTimingAction) (who : ι)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hnash : (quittingTwoDateTimingGame reward).mixedExtension.IsNash mixed) :
    let profile := quittingTwoDateTimingProfile reward mixed
    let first := quittingProfileLiveRoot reward profile 0
    let second := quittingProfileLiveRoot reward profile 1
    let roots := quittingTwoDateRoots first second
    let solo := reward (quittingSingletonTerminal who) who
    let debt := quittingTerminalDeviationDebt reward profile who
    let firstMass := quittingFixedOpponentsContinueMass roots who 0
    let secondMass := quittingFixedOpponentsContinueMass roots who 1
    TwoDatePhaseMassDebtCertificate bound solo debt
      (firstMass * secondMass) (1 - firstMass)
      (firstMass * (1 - secondMass)) := by
  let profile := quittingTwoDateTimingProfile reward mixed
  let first := quittingProfileLiveRoot reward profile 0
  let second := quittingProfileLiveRoot reward profile 1
  have hprofile : profile =
      quittingTwoDateRootProfile reward first second := by
    exact quittingTwoDateTimingProfile_eq_twoDateRootProfile reward mixed
  have hcertificate := quittingTwoDateTimingProfile_isFiniteDeadline
    reward mixed hnash
  change TwoDatePhaseMassDebtCertificate bound
    (reward (quittingSingletonTerminal who) who)
    (quittingTerminalDeviationDebt reward profile who)
    (quittingFixedOpponentsContinueMass
        (quittingTwoDateRoots first second) who 0 *
      quittingFixedOpponentsContinueMass
        (quittingTwoDateRoots first second) who 1)
    (1 - quittingFixedOpponentsContinueMass
      (quittingTwoDateRoots first second) who 0)
    (quittingFixedOpponentsContinueMass
        (quittingTwoDateRoots first second) who 0 *
      (1 - quittingFixedOpponentsContinueMass
        (quittingTwoDateRoots first second) who 1))
  change QuittingFiniteDeadlineNashProfile reward profile 2 at hcertificate
  rw [hprofile] at hcertificate ⊢
  exact quittingTerminalDeviationDebt_twoDateRootProfile_dataSensitive
    reward first second who hbound hreward hcertificate

/-- The literal realization of a three-action timing Nash equilibrium has
unrestricted behavioral terminal debt at most half the reward bound. -/
theorem quittingTerminalDeviationDebt_twoDateTimingProfile_le_half
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mixed : ι → PMF QuittingTwoDateTimingAction) (who : ι)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hnash : (quittingTwoDateTimingGame reward).mixedExtension.IsNash mixed) :
    quittingTerminalDeviationDebt reward
        (quittingTwoDateTimingProfile reward mixed) who ≤ bound / 2 := by
  let first := quittingProfileLiveRoot reward
    (quittingTwoDateTimingProfile reward mixed) 0
  let second := quittingProfileLiveRoot reward
    (quittingTwoDateTimingProfile reward mixed) 1
  have hprofile : quittingTwoDateTimingProfile reward mixed =
      quittingTwoDateRootProfile reward first second := by
    exact quittingTwoDateTimingProfile_eq_twoDateRootProfile reward mixed
  have hcertificate := quittingTwoDateTimingProfile_isFiniteDeadline
    reward mixed hnash
  rw [hprofile] at hcertificate ⊢
  exact quittingTerminalDeviationDebt_twoDateRootProfile_le_half
    reward first second who hbound hreward hcertificate

/-- Every finite quitting game has a mixed timing Nash equilibrium on dates
zero, one, and Never whose literal realization has coordinatewise terminal
debt at most half the reward bound. -/
theorem exists_twoDateTimingNash_terminalDebt_le_half
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    ∃ mixed : ι → PMF QuittingTwoDateTimingAction,
      (quittingTwoDateTimingGame reward).mixedExtension.IsNash mixed ∧
        QuittingFiniteDeadlineNashProfile reward
          (quittingTwoDateTimingProfile reward mixed) 2 ∧
        ∀ who,
          0 ≤ quittingTerminalDeviationDebt reward
              (quittingTwoDateTimingProfile reward mixed) who ∧
            quittingTerminalDeviationDebt reward
                (quittingTwoDateTimingProfile reward mixed) who ≤ bound / 2 := by
  letI : ∀ player,
      Finite ((quittingTwoDateTimingGame reward).Strategy player) := by
    intro player
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame
      KernelGame.ofPureEU
    infer_instance
  letI : ∀ player,
      Nonempty ((quittingTwoDateTimingGame reward).Strategy player) := by
    intro player
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame
      KernelGame.ofPureEU
    infer_instance
  letI : Finite (quittingTwoDateTimingGame reward).Outcome := by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame
      KernelGame.ofPureEU
    infer_instance
  obtain ⟨mixed, hnash⟩ :=
    (quittingTwoDateTimingGame reward).mixed_nash_exists
  refine ⟨mixed, hnash,
    quittingTwoDateTimingProfile_isFiniteDeadline reward mixed hnash,
    fun who => ⟨quittingTerminalDeviationDebt_nonneg reward
      (quittingTwoDateTimingProfile reward mixed) who, ?_⟩⟩
  exact quittingTerminalDeviationDebt_twoDateTimingProfile_le_half
    reward mixed who hbound hreward hnash

/-- Every finite quitting game has a literal two-date timing profile that is
`bound / 2`-Nash against all behavioral deviations. -/
theorem exists_twoDateTimingNash_isεAsymptoticNash_half
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    ∃ mixed : ι → PMF QuittingTwoDateTimingAction,
      (quittingTwoDateTimingGame reward).mixedExtension.IsNash mixed ∧
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) (bound / 2)
          (quittingTwoDateTimingProfile reward mixed) := by
  obtain ⟨mixed, hnash, _hcertificate, hdebt⟩ :=
    exists_twoDateTimingNash_terminalDebt_le_half reward hbound hreward
  refine ⟨mixed, hnash, ?_⟩
  intro who deviation
  have hdeviation :=
    quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward (quittingTwoDateTimingProfile reward mixed) who deviation
  have hdebtBound := (hdebt who).2
  unfold quittingTerminalDeviationDebt at hdebtBound
  linarith

end GameTheory

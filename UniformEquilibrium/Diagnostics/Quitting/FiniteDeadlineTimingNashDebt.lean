/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.FiniteDeadlineNashDebtBounds
import UniformEquilibrium.Diagnostics.Quitting.FiniteDeadlineTimingGame

/-!
# Universal finite-deadline timing Nash debt bounds

For every positive finite deadline, this module constructs a mixed Nash
equilibrium of the hard-tail timing game, realizes its planned times as
literal behavioral hazards, and bounds every unrestricted behavioral terminal
debt coordinate.

At normalized singleton reward `x`, the exact scalar envelope is

`x * (K + 1 - (K - 1) * x) / (K + 1 + x)`.

It is at most `1 / 4 + 2 / K`. At three dates it is strictly below `24 / 59`,
the rational threshold needed by the normalized Fin4 hierarchy through level
59. Every theorem selects a fresh Nash equilibrium of the complete declared
timing game; no fixed earlier timing prefix is preserved.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem finiteDeadline_normalized_scalar_bound
    (deadline : ℕ) (hdeadline : 0 < deadline)
    (x debt allNever : ℝ)
    (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hnever : debt ≤ allNever * x)
    (hdates : (deadline : ℝ) * debt ≤
      ((deadline : ℝ) + 1 - ((deadline : ℝ) - 1) * x) *
        (1 - allNever)) :
    debt ≤
      x * ((deadline : ℝ) + 1 - ((deadline : ℝ) - 1) * x) /
        ((deadline : ℝ) + 1 + x) := by
  let A := (deadline : ℝ) + 1 - ((deadline : ℝ) - 1) * x
  have hdeadlineReal : 1 ≤ (deadline : ℝ) := by exact_mod_cast hdeadline
  have hA : 0 < A := by
    dsimp only [A]
    nlinarith
  have hdenom : 0 < (deadline : ℝ) + 1 + x := by positivity
  apply (le_div_iff₀ hdenom).2
  have hfirst : (deadline : ℝ) * x * debt ≤
      A * (x * (1 - allNever)) := by
    have := mul_le_mul_of_nonneg_left hdates hx0.le
    change x * ((deadline : ℝ) * debt) ≤
      x * (A * (1 - allNever)) at this
    nlinarith
  have hsecond : A * (x * (1 - allNever)) ≤ A * (x - debt) := by
    apply mul_le_mul_of_nonneg_left _ hA.le
    nlinarith
  dsimp only [A] at hfirst hsecond ⊢
  nlinarith

private theorem quittingPureDeadlineValue_sub_solo_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (start fuel : ℕ) {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hend : roots (start + fuel) = quittingAllContinueRoot) :
    quittingRootSequencePureTimeTerminalValue reward roots who
          (some (start + fuel)) start -
        reward (quittingSingletonTerminal who) who ≤
      (bound - reward (quittingSingletonTerminal who) who) *
        (1 - quittingOpponentSurvivalWeight roots who start fuel) := by
  induction fuel generalizing start with
  | zero =>
      simp only [Nat.add_zero] at hend ⊢
      rw [quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents]
      unfold quittingFixedOpponentsQuitValue
      rw [hend]
      have hquit := quittingRootQuitPayoff_allContinueRoot
        reward (0 : Payoff ι) who
      unfold quittingRootQuitPayoff at hquit
      unfold quittingRootAbsorbingContribution
      rw [hquit]
      simp [quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      let solo := reward (quittingSingletonTerminal who) who
      let continueMass := quittingFixedOpponentsContinueMass roots who start
      have hsolo : solo ≤ bound :=
        le_of_abs_le (hreward (quittingSingletonTerminal who) who)
      have hcontinue0 : 0 ≤ continueMass :=
        quittingFixedOpponentsContinueMass_nonneg roots who start
      have hcontinue1 : continueMass ≤ 1 :=
        quittingFixedOpponentsContinueMass_le_one roots who start
      have htail := ih (start := start + 1) (by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hend)
      have hindex : start + 1 + fuel = start + (fuel + 1) := by omega
      rw [hindex] at htail
      have hcontinue := quittingFixedOpponentsContinueReward_le
        reward roots who start hbound hreward
      have hne : start ≠ start + (fuel + 1) := by omega
      have hvalue :
          quittingRootSequencePureTimeTerminalValue reward roots who
              (some (start + (fuel + 1))) start =
            quittingFixedOpponentsContinueReward reward roots who start +
              continueMass *
                quittingRootSequencePureTimeTerminalValue reward roots who
                  (some (start + (fuel + 1))) (start + 1) := by
        unfold quittingRootSequencePureTimeTerminalValue
        rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman,
          quittingPureTimeHazard_some_of_ne hne]
        simp [continueMass]
      rw [hvalue, quittingOpponentSurvivalWeight_succ_left]
      dsimp only [solo, continueMass] at htail hcontinue ⊢
      have hscaled := mul_le_mul_of_nonneg_left htail hcontinue0
      nlinarith

private theorem quittingPureTimeDifference_transport
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) :
    ∀ start fuel late,
      start + fuel ≤ late →
      quittingRootSequencePureTimeTerminalValue reward roots who
            (some late) start -
          quittingRootSequencePureTimeTerminalValue reward roots who
            (some (start + fuel)) start =
        quittingOpponentSurvivalWeight roots who start fuel *
          (quittingRootSequencePureTimeTerminalValue reward roots who
                (some late) (start + fuel) -
            quittingRootSequencePureTimeTerminalValue reward roots who
              (some (start + fuel)) (start + fuel)) := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      intro late _
      simp [quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      intro late hlate
      have hendpoint : start + (fuel + 1) ≤ late := hlate
      have hlateNe : start ≠ late := by omega
      have hendpointNe : start ≠ start + (fuel + 1) := by omega
      have hlateValue :
          quittingRootSequencePureTimeTerminalValue reward roots who
              (some late) start =
            quittingFixedOpponentsContinueReward reward roots who start +
              quittingFixedOpponentsContinueMass roots who start *
                quittingRootSequencePureTimeTerminalValue reward roots who
                  (some late) (start + 1) := by
        unfold quittingRootSequencePureTimeTerminalValue
        rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman,
          quittingPureTimeHazard_some_of_ne hlateNe]
        simp
      have hendpointValue :
          quittingRootSequencePureTimeTerminalValue reward roots who
              (some (start + (fuel + 1))) start =
            quittingFixedOpponentsContinueReward reward roots who start +
              quittingFixedOpponentsContinueMass roots who start *
                quittingRootSequencePureTimeTerminalValue reward roots who
                  (some (start + (fuel + 1))) (start + 1) := by
        unfold quittingRootSequencePureTimeTerminalValue
        rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman,
          quittingPureTimeHazard_some_of_ne hendpointNe]
        simp
      have htail := ih (start := start + 1) late (by omega)
      have hindex : start + 1 + fuel = start + (fuel + 1) := by omega
      rw [hindex] at htail
      rw [hlateValue, hendpointValue,
        quittingOpponentSurvivalWeight_succ_left]
      calc
        _ = quittingFixedOpponentsContinueMass roots who start *
              (quittingRootSequencePureTimeTerminalValue reward roots who
                  (some late) (start + 1) -
                quittingRootSequencePureTimeTerminalValue reward roots who
                  (some (start + (fuel + 1))) (start + 1)) := by ring
        _ = quittingFixedOpponentsContinueMass roots who start *
              (quittingOpponentSurvivalWeight roots who (start + 1) fuel *
                (quittingRootSequencePureTimeTerminalValue reward roots who
                    (some late) (start + (fuel + 1)) -
                  quittingRootSequencePureTimeTerminalValue reward roots who
                    (some (start + (fuel + 1)))
                    (start + (fuel + 1)))) := by rw [htail]
        _ = _ := by ring

private theorem quittingPureDeadlineValue_sub_date_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (deadline time : ℕ) (htime : time < deadline)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (htail : ∀ stage, deadline ≤ stage →
      roots stage = quittingAllContinueRoot) :
    quittingRootSequencePureTimeTerminalValue reward roots who
          (some deadline) 0 -
        quittingRootSequencePureTimeTerminalValue reward roots who
          (some time) 0 ≤
      2 * bound * quittingOpponentSurvivalWeight roots who 0 time *
          (1 - quittingFixedOpponentsContinueMass roots who time) +
        (bound - reward (quittingSingletonTerminal who) who) *
          (quittingOpponentSurvivalWeight roots who 0 (time + 1) -
            quittingOpponentSurvivalWeight roots who 0 deadline) := by
  let solo := reward (quittingSingletonTerminal who) who
  let continueMass := quittingFixedOpponentsContinueMass roots who time
  let prefixWeight := quittingOpponentSurvivalWeight roots who 0 time
  let nextWeight := quittingOpponentSurvivalWeight roots who 0 (time + 1)
  let finalWeight := quittingOpponentSurvivalWeight roots who 0 deadline
  let tailFuel := deadline - (time + 1)
  let tailWeight := quittingOpponentSurvivalWeight roots who (time + 1) tailFuel
  have hsum : time + 1 + tailFuel = deadline := by
    dsimp only [tailFuel]
    omega
  have hcontinue0 : 0 ≤ continueMass :=
    quittingFixedOpponentsContinueMass_nonneg roots who time
  have hprefix0 : 0 ≤ prefixWeight :=
    quittingOpponentSurvivalWeight_nonneg roots who 0 time
  have htailBound := quittingPureDeadlineValue_sub_solo_le
    reward roots who (time + 1) tailFuel hbound hreward (by
      rw [hsum]
      exact htail deadline le_rfl)
  rw [hsum] at htailBound
  have hstage := quittingFixedOpponentsContinue_add_solo_sub_quit_le
    reward roots who time hbound hreward
  have hne : time ≠ deadline := by omega
  have hlateValue :
      quittingRootSequencePureTimeTerminalValue reward roots who
          (some deadline) time =
        quittingFixedOpponentsContinueReward reward roots who time +
          continueMass *
            quittingRootSequencePureTimeTerminalValue reward roots who
              (some deadline) (time + 1) := by
    unfold quittingRootSequencePureTimeTerminalValue
    rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman,
      quittingPureTimeHazard_some_of_ne hne]
    simp [continueMass]
  have hcurrentValue :
      quittingRootSequencePureTimeTerminalValue reward roots who
          (some time) time =
        quittingFixedOpponentsQuitValue reward roots who time :=
    quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents
      reward roots who time
  have htailScaled := mul_le_mul_of_nonneg_left htailBound hcontinue0
  have hlocal :
      quittingRootSequencePureTimeTerminalValue reward roots who
            (some deadline) time -
          quittingRootSequencePureTimeTerminalValue reward roots who
            (some time) time ≤
        2 * bound * (1 - continueMass) +
          (bound - solo) * continueMass * (1 - tailWeight) := by
    dsimp only [solo, continueMass, tailWeight] at hstage htailScaled ⊢
    rw [hlateValue, hcurrentValue]
    nlinarith
  have htransport := quittingPureTimeDifference_transport
    reward roots who 0 time deadline (by omega)
  simp only [Nat.zero_add] at htransport
  have hscaled := mul_le_mul_of_nonneg_left hlocal hprefix0
  rw [← htransport] at hscaled
  have hnext : nextWeight = prefixWeight * continueMass := by
    dsimp only [nextWeight, prefixWeight, continueMass]
    simpa only [Nat.zero_add] using
      quittingOpponentSurvivalWeight_succ roots who 0 time
  have hfinal : finalWeight = nextWeight * tailWeight := by
    dsimp only [finalWeight, nextWeight, tailWeight]
    rw [← hsum]
    simpa only [Nat.zero_add] using
      quittingOpponentSurvivalWeight_add roots who 0 (time + 1) tailFuel
  have hid : prefixWeight *
        ((bound - solo) * continueMass * (1 - tailWeight)) =
      (bound - solo) * (nextWeight - finalWeight) := by
    rw [hfinal, hnext]
    ring
  calc
    _ ≤ prefixWeight *
        (2 * bound * (1 - continueMass) +
          (bound - solo) * continueMass * (1 - tailWeight)) := hscaled
    _ = 2 * bound * prefixWeight * (1 - continueMass) +
        (bound - solo) * (nextWeight - finalWeight) := by
      rw [mul_add, hid]
      ring

private theorem sum_quittingOpponentSurvivalWeight_succ_sub_final_le
    (roots : ℕ → ι → PMF Bool) (who : ι) (deadline : ℕ) :
    (∑ time ∈ Finset.range deadline,
        (quittingOpponentSurvivalWeight roots who 0 (time + 1) -
          quittingOpponentSurvivalWeight roots who 0 deadline)) ≤
      ((deadline : ℝ) - 1) *
        (1 - quittingOpponentSurvivalWeight roots who 0 deadline) := by
  cases deadline with
  | zero => simp [quittingOpponentSurvivalWeight]
  | succ fuel =>
      rw [Finset.sum_range_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      have hsum :
          (∑ time ∈ Finset.range fuel,
              (quittingOpponentSurvivalWeight roots who 0 (time + 1) -
                quittingOpponentSurvivalWeight roots who 0 (fuel + 1))) ≤
            ∑ _time ∈ Finset.range fuel,
              (1 - quittingOpponentSurvivalWeight roots who 0 (fuel + 1)) := by
        apply Finset.sum_le_sum
        intro time _
        have hweight := quittingOpponentSurvivalWeight_le_one
          roots who 0 (time + 1)
        linarith
      have hsum' :
          (∑ time ∈ Finset.range fuel,
              (quittingOpponentSurvivalWeight roots who 0 (time + 1) -
                quittingOpponentSurvivalWeight roots who 0 (fuel + 1))) ≤
            (fuel : ℝ) *
              (1 - quittingOpponentSurvivalWeight roots who 0 (fuel + 1)) := by
        calc
          _ ≤ ∑ _time ∈ Finset.range fuel,
              (1 - quittingOpponentSurvivalWeight roots who 0 (fuel + 1)) :=
            hsum
          _ = _ := by
            simp [Finset.sum_const, nsmul_eq_mul]
            ring
      convert hsum' using 1 <;> ring

/-- A positive singleton row charges terminal debt to one selected date's
opponent absorption and the remaining opponent-survival drop. -/
theorem QuittingFiniteDeadlineNashProfile.debt_le_date_charge
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile} {deadline : ℕ}
    (certificate : QuittingFiniteDeadlineNashProfile reward profile deadline)
    (who : ι) (time : ℕ) (htime : time < deadline)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hsolo : 0 ≤ reward (quittingSingletonTerminal who) who) :
    quittingTerminalDeviationDebt reward profile who ≤
      2 * bound *
          quittingOpponentSurvivalWeight
            (quittingProfileLiveRoot reward profile) who 0 time *
          (1 - quittingFixedOpponentsContinueMass
            (quittingProfileLiveRoot reward profile) who time) +
        (bound - reward (quittingSingletonTerminal who) who) *
          (quittingOpponentSurvivalWeight
              (quittingProfileLiveRoot reward profile) who 0 (time + 1) -
            quittingOpponentSurvivalWeight
              (quittingProfileLiveRoot reward profile) who 0 deadline) := by
  let roots := quittingProfileLiveRoot reward profile
  let prescribed := quittingTerminalPayoff reward profile who
  let lateValue := quittingTerminalPayoff reward
    (Function.update profile who
      (quittingPureTimeBehaviorStrategy reward who (some deadline))) who
  let dateValue := quittingTerminalPayoff reward
    (Function.update profile who
      (quittingPureTimeBehaviorStrategy reward who (some time))) who
  let debt := quittingTerminalDeviationDebt reward profile who
  let right := 2 * bound *
          quittingOpponentSurvivalWeight roots who 0 time *
          (1 - quittingFixedOpponentsContinueMass roots who time) +
        (bound - reward (quittingSingletonTerminal who) who) *
          (quittingOpponentSurvivalWeight roots who 0 (time + 1) -
            quittingOpponentSurvivalWeight roots who 0 deadline)
  have hlateExact :=
    quittingRootSequencePureTimeTerminalValue_late_sub_none_eq
      reward roots who deadline deadline le_rfl certificate.allContinue_from
  have hlateEq : lateValue =
      quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who none)) who +
        quittingFiniteDeadlineOpponentSurvival reward profile deadline who *
          reward (quittingSingletonTerminal who) who := by
    dsimp only [lateValue, roots, quittingFiniteDeadlineOpponentSurvival]
    rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
      quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
    linarith
  have hbest := certificate.bestResponseValue_le_max_late who hsolo
  rw [← hlateEq] at hbest
  have hdateNash : dateValue ≤ prescribed := by
    exact certificate.pureTime_le who (some time)
      (Or.inr ⟨time, htime, rfl⟩)
  have hdateBound := quittingPureDeadlineValue_sub_date_le
    reward roots who deadline time htime hbound hreward certificate.allContinue_from
  have hdateBound' : lateValue - dateValue ≤ right := by
    dsimp only [lateValue, dateValue, right, roots]
    rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
      quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
    exact hdateBound
  have hsoloBound : reward (quittingSingletonTerminal who) who ≤ bound :=
    le_of_abs_le (hreward (quittingSingletonTerminal who) who)
  have hweightDiff : 0 ≤
      quittingOpponentSurvivalWeight roots who 0 (time + 1) -
        quittingOpponentSurvivalWeight roots who 0 deadline := by
    exact sub_nonneg.mpr (antitone_quittingOpponentSurvivalWeight
      roots who 0 (by omega))
  have hright0 : 0 ≤ right := by
    dsimp only [right]
    have hweight0 := quittingOpponentSurvivalWeight_nonneg roots who 0 time
    have hcontinue1 :=
      quittingFixedOpponentsContinueMass_le_one roots who time
    positivity
  by_cases hlate : lateValue ≤ prescribed
  · have hcap : quittingContinuationBestResponseValue reward profile who ≤
        prescribed := hbest.trans (max_eq_left hlate).le
    unfold quittingTerminalDeviationDebt
    exact (sub_nonpos.mpr hcap).trans hright0
  · have hprescribedLate : prescribed < lateValue := lt_of_not_ge hlate
    rw [max_eq_right hprescribedLate.le] at hbest
    unfold quittingTerminalDeviationDebt
    linarith

/-- The scalar finite-deadline debt envelope from the universal timing-game
summation. -/
def finiteDeadlineNashDebtFactor (deadline : ℕ) (x : ℝ) : ℝ :=
  x * ((deadline : ℝ) + 1 - ((deadline : ℝ) - 1) * x) /
    ((deadline : ℝ) + 1 + x)

/-- A positive coordinate debt of a finite-deadline Nash profile lies below
the exact scalar envelope at its normalized singleton reward. -/
theorem QuittingFiniteDeadlineNashProfile.exists_debt_div_le_factor
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile} {deadline : ℕ}
    (certificate : QuittingFiniteDeadlineNashProfile reward profile deadline)
    (hdeadline : 0 < deadline) (who : ι)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hdebt : 0 < quittingTerminalDeviationDebt reward profile who) :
    ∃ x : ℝ,
      x = reward (quittingSingletonTerminal who) who / bound ∧
      0 < x ∧ x ≤ 1 ∧
      quittingTerminalDeviationDebt reward profile who / bound ≤
        finiteDeadlineNashDebtFactor deadline x := by
  let roots := quittingProfileLiveRoot reward profile
  let debt := quittingTerminalDeviationDebt reward profile who
  let solo := reward (quittingSingletonTerminal who) who
  let allNever := quittingOpponentSurvivalWeight roots who 0 deadline
  have hsolo : 0 < solo := by
    by_contra hnsolo
    have hsoloNonpos : solo ≤ 0 := le_of_not_gt hnsolo
    have hescape := certificate.semanticDebt_le_escapeCharge who
    have hcharge : quittingFiniteDeadlineEscapeCharge
        reward profile deadline who = 0 := by
      simp [quittingFiniteDeadlineEscapeCharge, solo, max_eq_left hsoloNonpos]
    rw [hcharge] at hescape
    exact (not_lt_of_ge hescape) hdebt
  have hsoloBound : solo ≤ bound :=
    le_of_abs_le (hreward (quittingSingletonTerminal who) who)
  have hboundPos : 0 < bound := hsolo.trans_le hsoloBound
  have hallNever0 : 0 ≤ allNever :=
    quittingOpponentSurvivalWeight_nonneg roots who 0 deadline
  have hallNever1 : allNever ≤ 1 :=
    quittingOpponentSurvivalWeight_le_one roots who 0 deadline
  have hnever : debt ≤ allNever * solo := by
    have hescape := certificate.semanticDebt_le_escapeCharge who
    rw [show quittingFiniteDeadlineEscapeCharge reward profile deadline who =
        allNever * solo by
      unfold quittingFiniteDeadlineEscapeCharge
      rw [max_eq_right hsolo.le]
      rfl] at hescape
    exact hescape
  have hdate : ∀ time ∈ Finset.range deadline, debt ≤
      2 * bound * quittingOpponentSurvivalWeight roots who 0 time *
          (1 - quittingFixedOpponentsContinueMass roots who time) +
        (bound - solo) *
          (quittingOpponentSurvivalWeight roots who 0 (time + 1) -
            allNever) := by
    intro time htime
    exact certificate.debt_le_date_charge who time
      (Finset.mem_range.mp htime) hbound hreward hsolo.le
  have hsumDate : (∑ time ∈ Finset.range deadline, debt) ≤
      ∑ time ∈ Finset.range deadline,
        (2 * bound * quittingOpponentSurvivalWeight roots who 0 time *
            (1 - quittingFixedOpponentsContinueMass roots who time) +
          (bound - solo) *
            (quittingOpponentSurvivalWeight roots who 0 (time + 1) -
              allNever)) := by
    exact Finset.sum_le_sum hdate
  have hfirst :
      (∑ time ∈ Finset.range deadline,
          quittingOpponentSurvivalWeight roots who 0 time *
            (1 - quittingFixedOpponentsContinueMass roots who time)) =
        1 - allNever := by
    simpa only [Nat.zero_add, allNever] using
      sum_quittingOpponentSurvivalWeight_mul_one_sub_continueMass
        roots who 0 deadline
  have hsecond :
      (∑ time ∈ Finset.range deadline,
          (quittingOpponentSurvivalWeight roots who 0 (time + 1) -
            allNever)) ≤
        ((deadline : ℝ) - 1) * (1 - allNever) := by
    exact sum_quittingOpponentSurvivalWeight_succ_sub_final_le
      roots who deadline
  have hsecondScaled := mul_le_mul_of_nonneg_left hsecond
    (sub_nonneg.mpr hsoloBound)
  have htotal : (deadline : ℝ) * debt ≤
      (2 * bound + (bound - solo) * ((deadline : ℝ) - 1)) *
        (1 - allNever) := by
    calc
      (deadline : ℝ) * debt =
          ∑ _time ∈ Finset.range deadline, debt := by simp
      _ ≤ ∑ time ∈ Finset.range deadline,
          (2 * bound * quittingOpponentSurvivalWeight roots who 0 time *
              (1 - quittingFixedOpponentsContinueMass roots who time) +
            (bound - solo) *
              (quittingOpponentSurvivalWeight roots who 0 (time + 1) -
                allNever)) := hsumDate
      _ = 2 * bound *
            (∑ time ∈ Finset.range deadline,
              quittingOpponentSurvivalWeight roots who 0 time *
                (1 - quittingFixedOpponentsContinueMass roots who time)) +
          (bound - solo) *
            (∑ time ∈ Finset.range deadline,
              (quittingOpponentSurvivalWeight roots who 0 (time + 1) -
                allNever)) := by
        rw [Finset.sum_add_distrib]
        simp_rw [mul_assoc]
        simp_rw [← Finset.mul_sum]
      _ ≤ 2 * bound * (1 - allNever) +
          (bound - solo) * ((deadline : ℝ) - 1) *
            (1 - allNever) := by
        rw [hfirst]
        linarith
      _ = _ := by ring
  let x := solo / bound
  let normalizedDebt := debt / bound
  have hx0 : 0 < x := div_pos hsolo hboundPos
  have hx1 : x ≤ 1 := (div_le_one hboundPos).2 hsoloBound
  have hx : bound * x = solo := by
    dsimp only [x]
    field_simp
  have hnormalizedDebt : bound * normalizedDebt = debt := by
    dsimp only [normalizedDebt]
    field_simp
  have hneverNormalized : normalizedDebt ≤ allNever * x := by
    nlinarith
  have hdatesNormalized : (deadline : ℝ) * normalizedDebt ≤
      ((deadline : ℝ) + 1 - ((deadline : ℝ) - 1) * x) *
        (1 - allNever) := by
    have hfactor :
        2 * bound + (bound - solo) * ((deadline : ℝ) - 1) =
          bound *
            ((deadline : ℝ) + 1 - ((deadline : ℝ) - 1) * x) := by
      nlinarith
    rw [hfactor] at htotal
    nlinarith
  refine ⟨x, rfl, hx0, hx1, ?_⟩
  change normalizedDebt ≤ finiteDeadlineNashDebtFactor deadline x
  unfold finiteDeadlineNashDebtFactor
  exact finiteDeadline_normalized_scalar_bound deadline hdeadline x
    normalizedDebt allNever hx0 hx1 hneverNormalized hdatesNormalized

/-- A nonpositive singleton self-reward forces exact zero unrestricted debt
for every finite-deadline Nash profile. -/
theorem QuittingFiniteDeadlineNashProfile.debt_eq_zero_of_solo_nonpos
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile} {deadline : ℕ}
    (certificate : QuittingFiniteDeadlineNashProfile reward profile deadline)
    (who : ι)
    (hsolo : reward (quittingSingletonTerminal who) who ≤ 0) :
    quittingTerminalDeviationDebt reward profile who = 0 := by
  apply le_antisymm
  · have hescape := certificate.semanticDebt_le_escapeCharge who
    rw [quittingFiniteDeadlineEscapeCharge, max_eq_left hsolo, mul_zero] at hescape
    exact hescape
  · exact quittingTerminalDeviationDebt_nonneg reward profile who

/-- The exact scalar factor is nonnegative throughout its normalized
singleton-reward domain. -/
theorem finiteDeadlineNashDebtFactor_nonneg
    (deadline : ℕ) (hdeadline : 0 < deadline)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ finiteDeadlineNashDebtFactor deadline x := by
  have hdeadlineReal : (1 : ℝ) ≤ deadline := by
    exact_mod_cast hdeadline
  have hnumerator : 0 ≤
      (deadline : ℝ) + 1 - ((deadline : ℝ) - 1) * x := by
    nlinarith [mul_nonneg
      (sub_nonneg.mpr hdeadlineReal) (sub_nonneg.mpr hx1)]
  have hdenominator : 0 < (deadline : ℝ) + 1 + x := by positivity
  unfold finiteDeadlineNashDebtFactor
  exact div_nonneg (mul_nonneg hx0 hnumerator) hdenominator.le

/-! ## Exact one- and two-date scalar maxima -/

/-- The one-date scalar envelope is at most `2 / 3` on its normalized
singleton-reward domain. -/
theorem finiteDeadlineNashDebtFactor_one_le_two_thirds
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    finiteDeadlineNashDebtFactor 1 x ≤ 2 / 3 := by
  unfold finiteDeadlineNashDebtFactor
  norm_num only [Nat.cast_one]
  apply (div_le_iff₀ (by linarith : 0 < 2 + x)).2
  nlinarith

/-- The endpoint `x = 1` attains the exact one-date maximum `2 / 3`. -/
theorem finiteDeadlineNashDebtFactor_one_at_one :
    finiteDeadlineNashDebtFactor 1 1 = 2 / 3 := by
  norm_num [finiteDeadlineNashDebtFactor]

/-- The two-date scalar envelope is at most `1 / 2` on its normalized
singleton-reward domain. -/
theorem finiteDeadlineNashDebtFactor_two_le_half
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    finiteDeadlineNashDebtFactor 2 x ≤ 1 / 2 := by
  unfold finiteDeadlineNashDebtFactor
  norm_num only [Nat.cast_ofNat]
  apply (div_le_iff₀ (by linarith : 0 < 3 + x)).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (by linarith : 0 ≤ 3 - 2 * x)]

/-- The endpoint `x = 1` attains the exact two-date maximum `1 / 2`. -/
theorem finiteDeadlineNashDebtFactor_two_at_one :
    finiteDeadlineNashDebtFactor 2 1 = 1 / 2 := by
  norm_num [finiteDeadlineNashDebtFactor]

/-! ## Exact three-date scalar maximum -/

/-- The unique normalized singleton ratio attaining the three-date scalar
envelope. -/
def finiteDeadlineNashDebtFactorThreeMaximizer : ℝ :=
  -4 + 2 * Real.sqrt 6

/-- The exact maximum of the three-date scalar envelope on `[0,1]`. -/
def finiteDeadlineNashDebtFactorThreeMaximum : ℝ :=
  20 - 8 * Real.sqrt 6

private theorem sqrtSix_sq : (Real.sqrt 6) ^ 2 = (6 : ℝ) := by
  norm_num

theorem finiteDeadlineNashDebtFactorThreeMaximizer_mem_Icc :
    finiteDeadlineNashDebtFactorThreeMaximizer ∈ Set.Icc (0 : ℝ) 1 := by
  have hs0 := Real.sqrt_nonneg 6
  have hs2 := sqrtSix_sq
  unfold finiteDeadlineNashDebtFactorThreeMaximizer
  constructor <;> nlinarith

theorem finiteDeadlineNashDebtFactor_three_at_maximizer :
    finiteDeadlineNashDebtFactor 3
        finiteDeadlineNashDebtFactorThreeMaximizer =
      finiteDeadlineNashDebtFactorThreeMaximum := by
  have hspos : 0 < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
  have hs2 := sqrtSix_sq
  unfold finiteDeadlineNashDebtFactor finiteDeadlineNashDebtFactorThreeMaximizer
    finiteDeadlineNashDebtFactorThreeMaximum
  norm_num only [Nat.cast_ofNat]
  field_simp [ne_of_gt hspos]
  nlinarith

/-- Exact square-gap identity behind the three-date maximum. -/
theorem finiteDeadlineNashDebtFactorThreeMaximum_sub_factor
    (x : ℝ) (hx0 : 0 ≤ x) :
    finiteDeadlineNashDebtFactorThreeMaximum -
        finiteDeadlineNashDebtFactor 3 x =
      2 * (x - finiteDeadlineNashDebtFactorThreeMaximizer) ^ 2 / (4 + x) := by
  have hden : 4 + x ≠ 0 := ne_of_gt (by linarith)
  have hs2 := sqrtSix_sq
  unfold finiteDeadlineNashDebtFactor finiteDeadlineNashDebtFactorThreeMaximizer
    finiteDeadlineNashDebtFactorThreeMaximum
  norm_num only [Nat.cast_ofNat]
  field_simp [hden]
  nlinarith

theorem finiteDeadlineNashDebtFactor_three_le_exactMaximum
    (x : ℝ) (hx0 : 0 ≤ x) :
    finiteDeadlineNashDebtFactor 3 x ≤
      finiteDeadlineNashDebtFactorThreeMaximum := by
  have hgap := finiteDeadlineNashDebtFactorThreeMaximum_sub_factor x hx0
  have hden : 0 ≤ 4 + x := by linarith
  have hnonneg : 0 ≤
      2 * (x - finiteDeadlineNashDebtFactorThreeMaximizer) ^ 2 / (4 + x) :=
    div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hden
  linarith

theorem finiteDeadlineNashDebtFactor_three_eq_exactMaximum_iff
    (x : ℝ) (hx0 : 0 ≤ x) :
    finiteDeadlineNashDebtFactor 3 x =
        finiteDeadlineNashDebtFactorThreeMaximum ↔
      x = finiteDeadlineNashDebtFactorThreeMaximizer := by
  have hden : 0 < 4 + x := by linarith
  constructor
  · intro heq
    have hzero : finiteDeadlineNashDebtFactorThreeMaximum -
        finiteDeadlineNashDebtFactor 3 x = 0 := by linarith
    rw [finiteDeadlineNashDebtFactorThreeMaximum_sub_factor x hx0] at hzero
    have hnumerator :
        2 * (x - finiteDeadlineNashDebtFactorThreeMaximizer) ^ 2 = 0 :=
      (div_eq_zero_iff.mp hzero).resolve_right hden.ne'
    have hsquare : (x - finiteDeadlineNashDebtFactorThreeMaximizer) ^ 2 = 0 := by
      exact (mul_eq_zero.mp hnumerator).resolve_left (by norm_num)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
  · rintro rfl
    exact finiteDeadlineNashDebtFactor_three_at_maximizer

theorem finiteDeadlineNashDebtFactorThreeMaximum_nonneg :
    0 ≤ finiteDeadlineNashDebtFactorThreeMaximum := by
  rw [← finiteDeadlineNashDebtFactor_three_at_maximizer]
  exact finiteDeadlineNashDebtFactor_nonneg 3 (by omega)
    finiteDeadlineNashDebtFactorThreeMaximizer
    finiteDeadlineNashDebtFactorThreeMaximizer_mem_Icc.1
    finiteDeadlineNashDebtFactorThreeMaximizer_mem_Icc.2

theorem finiteDeadlineNashDebtFactorThreeMaximum_lt_five_twelfths :
    finiteDeadlineNashDebtFactorThreeMaximum < 5 / 12 := by
  have hs0 := Real.sqrt_nonneg 6
  have hs2 := sqrtSix_sq
  unfold finiteDeadlineNashDebtFactorThreeMaximum
  nlinarith

/-- Maximal table-sensitive finite-deadline debt certificate. At a positive
singleton row the reward bound is positive and the normalized debt lies
below the exact factor evaluated at the literal ratio `solo / bound`. -/
theorem QuittingFiniteDeadlineNashProfile.debt_div_le_factor_at_solo_ratio
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile} {deadline : ℕ}
    (certificate : QuittingFiniteDeadlineNashProfile reward profile deadline)
    (hdeadline : 0 < deadline) (who : ι)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hsolo : 0 < reward (quittingSingletonTerminal who) who) :
    0 < bound ∧
      quittingTerminalDeviationDebt reward profile who / bound ≤
        finiteDeadlineNashDebtFactor deadline
          (reward (quittingSingletonTerminal who) who / bound) := by
  let solo := reward (quittingSingletonTerminal who) who
  let debt := quittingTerminalDeviationDebt reward profile who
  have hsoloBound : solo ≤ bound :=
    le_of_abs_le (hreward (quittingSingletonTerminal who) who)
  have hboundPos : 0 < bound := hsolo.trans_le hsoloBound
  refine ⟨hboundPos, ?_⟩
  have hx0 : 0 ≤ solo / bound := (div_pos hsolo hboundPos).le
  have hx1 : solo / bound ≤ 1 := (div_le_one hboundPos).2 hsoloBound
  by_cases hdebt : 0 < debt
  · obtain ⟨x, hx, _hx0, _hx1, hfactor⟩ :=
      certificate.exists_debt_div_le_factor
        hdeadline who hbound hreward hdebt
    simpa only [solo, hx] using hfactor
  · have hdebtZero : debt = 0 := by
      apply le_antisymm (le_of_not_gt hdebt)
      exact quittingTerminalDeviationDebt_nonneg reward profile who
    rw [show quittingTerminalDeviationDebt reward profile who = 0 by
      exact hdebtZero, zero_div]
    exact finiteDeadlineNashDebtFactor_nonneg
      deadline hdeadline (solo / bound) hx0 hx1

/-- Every three-date finite-timing Nash certificate has unrestricted
behavioral debt at most the exact scalar maximum times the reward bound. -/
theorem QuittingFiniteDeadlineNashProfile.debt_le_three_exactMaximum
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    (certificate : QuittingFiniteDeadlineNashProfile reward profile 3)
    (who : ι) {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    quittingTerminalDeviationDebt reward profile who ≤
      bound * finiteDeadlineNashDebtFactorThreeMaximum := by
  let solo := reward (quittingSingletonTerminal who) who
  by_cases hsolo : 0 < solo
  · obtain ⟨hboundPos, hfactor⟩ :=
      certificate.debt_div_le_factor_at_solo_ratio
        (by omega) who hbound hreward hsolo
    have hx0 : 0 ≤ solo / bound := (div_pos hsolo hboundPos).le
    have hfactorMax := finiteDeadlineNashDebtFactor_three_le_exactMaximum
      (solo / bound) hx0
    have hmul := mul_le_mul_of_nonneg_left
      (hfactor.trans hfactorMax) hbound
    rw [mul_div_cancel₀ _ hboundPos.ne'] at hmul
    exact hmul
  · have hdebtZero := certificate.debt_eq_zero_of_solo_nonpos who
      (show solo ≤ 0 by exact le_of_not_gt hsolo)
    rw [hdebtZero]
    exact mul_nonneg hbound finiteDeadlineNashDebtFactorThreeMaximum_nonneg

/-- The exact scalar envelope is at most the asymptotic quarter ceiling plus
`2 / deadline`. -/
theorem finiteDeadlineNashDebtFactor_le_quarter_add_two_div
    (deadline : ℕ) (hdeadline : 0 < deadline)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    finiteDeadlineNashDebtFactor deadline x ≤
      1 / 4 + 2 / (deadline : ℝ) := by
  let k := (deadline : ℝ)
  let denominator := k + 1 + x
  let first := x * (1 - x)
  let second := x * (1 + x)
  have hk : 0 < k := by
    dsimp only [k]
    exact_mod_cast hdeadline
  have hdenominator : 0 < denominator := by
    dsimp only [denominator, k]
    positivity
  have hkDenominator : k ≤ denominator := by
    dsimp only [denominator]
    linarith
  have hfirst0 : 0 ≤ first := by
    dsimp only [first]
    positivity
  have hsecond0 : 0 ≤ second := by
    dsimp only [second]
    positivity
  have hfirstFraction : k * first / denominator ≤ first := by
    apply (div_le_iff₀ hdenominator).2
    have := mul_nonneg hfirst0 (sub_nonneg.mpr hkDenominator)
    nlinarith
  have hsecondFraction : second / denominator ≤ second / k :=
    div_le_div_of_nonneg_left hsecond0 hk hkDenominator
  have hdecomposition : finiteDeadlineNashDebtFactor deadline x =
      k * first / denominator + second / denominator := by
    unfold finiteDeadlineNashDebtFactor
    dsimp only [k, denominator, first, second]
    ring
  have henvelope : finiteDeadlineNashDebtFactor deadline x ≤
      first + second / k := by
    rw [hdecomposition]
    exact add_le_add hfirstFraction hsecondFraction
  have hfirstQuarter : first ≤ 1 / 4 := by
    dsimp only [first]
    nlinarith [sq_nonneg (x - 1 / 2)]
  have hsecondTwo : second ≤ 2 := by
    dsimp only [second]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (by linarith : 0 ≤ 2 + x)]
  have hsecondDiv : second / k ≤ 2 / k :=
    (div_le_div_iff_of_pos_right hk).2 hsecondTwo
  dsimp only [k] at henvelope hsecondDiv
  linarith

/-- Every finite-deadline Nash profile has unrestricted behavioral debt at
most the universal quarter ceiling plus `2 / deadline`. -/
theorem QuittingFiniteDeadlineNashProfile.debt_le_quarter_add_two_div
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile} {deadline : ℕ}
    (certificate : QuittingFiniteDeadlineNashProfile reward profile deadline)
    (hdeadline : 0 < deadline) (who : ι)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    quittingTerminalDeviationDebt reward profile who ≤
      bound * (1 / 4 + 2 / (deadline : ℝ)) := by
  let debt := quittingTerminalDeviationDebt reward profile who
  by_cases hdebt : debt ≤ 0
  · exact hdebt.trans (mul_nonneg hbound (by positivity))
  · have hdebtPos : 0 < debt := lt_of_not_ge hdebt
    obtain ⟨x, _hx, hx0, hx1, hfactor⟩ :=
      certificate.exists_debt_div_le_factor
        hdeadline who hbound hreward hdebtPos
    have hfactorBound := finiteDeadlineNashDebtFactor_le_quarter_add_two_div
      deadline hdeadline x hx0.le hx1
    have hboundPos : 0 < bound := by
      by_contra hboundNotPos
      have hboundZero : bound = 0 := le_antisymm (le_of_not_gt hboundNotPos) hbound
      have hrewardZero : ∀ terminal player, reward terminal player = 0 := by
        intro terminal player
        have := hreward terminal player
        rw [hboundZero] at this
        exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
      have hsoloZero : reward (quittingSingletonTerminal who) who = 0 :=
        hrewardZero (quittingSingletonTerminal who) who
      have hescape := certificate.semanticDebt_le_escapeCharge who
      rw [quittingFiniteDeadlineEscapeCharge, hsoloZero, max_self,
        mul_zero] at hescape
      exact (not_lt_of_ge hescape) hdebtPos
    have hmul := mul_le_mul_of_nonneg_left
      (hfactor.trans hfactorBound) hbound
    dsimp only [debt] at hdebtPos ⊢
    rw [mul_div_cancel₀ _ hboundPos.ne'] at hmul
    exact hmul

/-- The three-date scalar envelope is strictly below the rational `24 / 59`
threshold needed by the normalized Fin4 hierarchy. -/
theorem finiteDeadlineNashDebtFactor_three_lt_twentyFour_div_fiftyNine
    (x : ℝ) (hx0 : 0 < x) :
    finiteDeadlineNashDebtFactor 3 x < 24 / 59 := by
  unfold finiteDeadlineNashDebtFactor
  norm_num only [Nat.cast_ofNat]
  apply (div_lt_iff₀ (by linarith : 0 < 4 + x)).2
  have hsquare : 0 < 59 * x ^ 2 - 106 * x + 48 := by
    nlinarith [sq_nonneg (59 * x - 53)]
  nlinarith

/-- Every three-date Nash profile has unrestricted behavioral debt at most
the rational `24 / 59` multiple of the reward bound. -/
theorem QuittingFiniteDeadlineNashProfile.debt_le_three_twentyFour_div_fiftyNine
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    (certificate : QuittingFiniteDeadlineNashProfile reward profile 3)
    (who : ι) {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    quittingTerminalDeviationDebt reward profile who ≤ bound * (24 / 59) := by
  let debt := quittingTerminalDeviationDebt reward profile who
  by_cases hdebt : debt ≤ 0
  · exact hdebt.trans (mul_nonneg hbound (by positivity))
  · have hdebtPos : 0 < debt := lt_of_not_ge hdebt
    obtain ⟨x, _hx, hx0, _hx1, hfactor⟩ :=
      certificate.exists_debt_div_le_factor
        (by omega) who hbound hreward hdebtPos
    have hfactorBound : finiteDeadlineNashDebtFactor 3 x ≤ 24 / 59 :=
      (finiteDeadlineNashDebtFactor_three_lt_twentyFour_div_fiftyNine
        x hx0).le
    have hboundPos : 0 < bound := by
      by_contra hboundNotPos
      have hboundZero : bound = 0 := le_antisymm (le_of_not_gt hboundNotPos) hbound
      have hrewardZero : ∀ terminal player, reward terminal player = 0 := by
        intro terminal player
        have := hreward terminal player
        rw [hboundZero] at this
        exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
      have hsoloZero : reward (quittingSingletonTerminal who) who = 0 :=
        hrewardZero (quittingSingletonTerminal who) who
      have hescape := certificate.semanticDebt_le_escapeCharge who
      rw [quittingFiniteDeadlineEscapeCharge, hsoloZero, max_self,
        mul_zero] at hescape
      exact (not_lt_of_ge hescape) hdebtPos
    have hmul := mul_le_mul_of_nonneg_left
      (hfactor.trans hfactorBound) hbound
    dsimp only [debt] at hdebtPos ⊢
    rw [mul_div_cancel₀ _ hboundPos.ne'] at hmul
    exact hmul

/-- A finite timing Nash realization satisfies the universal quarter-ceiling
debt bound against all behavioral deviations. -/
theorem quittingTerminalDeviationDebt_finiteDeadlineTimingProfile_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ) (hdeadline : 0 < deadline)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hnash : (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.IsNash
      mixed) :
    quittingTerminalDeviationDebt reward
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) who ≤
      bound * (1 / 4 + 2 / (deadline : ℝ)) := by
  exact (quittingFiniteDeadlineTimingProfile_isFiniteDeadline
    reward deadline mixed hnash).debt_le_quarter_add_two_div
      hdeadline who hbound hreward

/-- Every positive finite deadline has a literal timing Nash realization
with the universal coordinatewise terminal-debt bound. -/
theorem exists_finiteDeadlineTimingNash_terminalDebt_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ) (hdeadline : 0 < deadline)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline),
      (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.IsNash
          mixed ∧
        QuittingFiniteDeadlineNashProfile reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) deadline ∧
        ∀ who,
          0 ≤ quittingTerminalDeviationDebt reward
              (quittingFiniteDeadlineTimingProfile reward deadline mixed) who ∧
            quittingTerminalDeviationDebt reward
                (quittingFiniteDeadlineTimingProfile reward deadline mixed) who ≤
              bound * (1 / 4 + 2 / (deadline : ℝ)) := by
  letI : ∀ player,
      Finite ((quittingFiniteDeadlineTimingGame reward deadline).Strategy
        player) := by
    intro player
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  letI : ∀ player,
      Nonempty ((quittingFiniteDeadlineTimingGame reward deadline).Strategy
        player) := by
    intro player
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  letI : Finite (quittingFiniteDeadlineTimingGame reward deadline).Outcome := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  obtain ⟨mixed, hnash⟩ :=
    (quittingFiniteDeadlineTimingGame reward deadline).mixed_nash_exists
  refine ⟨mixed, hnash,
    quittingFiniteDeadlineTimingProfile_isFiniteDeadline
      reward deadline mixed hnash,
    fun who => ⟨quittingTerminalDeviationDebt_nonneg reward
      (quittingFiniteDeadlineTimingProfile reward deadline mixed) who, ?_⟩⟩
  exact quittingTerminalDeviationDebt_finiteDeadlineTimingProfile_le
    reward deadline hdeadline mixed who hbound hreward hnash

/-- Every finite quitting game has a literal three-date timing Nash profile
whose unrestricted behavioral debt is bounded by the exact scalar maximum. -/
theorem exists_threeDateTimingNash_terminalDebt_le_exactMaximum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction 3),
      (quittingFiniteDeadlineTimingGame reward 3).mixedExtension.IsNash mixed ∧
        QuittingFiniteDeadlineNashProfile reward
          (quittingFiniteDeadlineTimingProfile reward 3 mixed) 3 ∧
        ∀ who,
          0 ≤ quittingTerminalDeviationDebt reward
              (quittingFiniteDeadlineTimingProfile reward 3 mixed) who ∧
            quittingTerminalDeviationDebt reward
                (quittingFiniteDeadlineTimingProfile reward 3 mixed) who ≤
              bound * finiteDeadlineNashDebtFactorThreeMaximum := by
  obtain ⟨mixed, hnash, hcertificate, _hdebt⟩ :=
    exists_finiteDeadlineTimingNash_terminalDebt_le
      reward 3 (by omega) hbound hreward
  refine ⟨mixed, hnash, hcertificate, fun who ↦ ⟨
    quittingTerminalDeviationDebt_nonneg reward
      (quittingFiniteDeadlineTimingProfile reward 3 mixed) who, ?_⟩⟩
  exact hcertificate.debt_le_three_exactMaximum who hbound hreward

/-- Every finite quitting game has a literal three-date timing Nash profile
whose unrestricted behavioral debt is at most `24 / 59` of the reward bound. -/
theorem exists_threeDateTimingNash_terminalDebt_le_twentyFour_div_fiftyNine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction 3),
      (quittingFiniteDeadlineTimingGame reward 3).mixedExtension.IsNash mixed ∧
        QuittingFiniteDeadlineNashProfile reward
          (quittingFiniteDeadlineTimingProfile reward 3 mixed) 3 ∧
        ∀ who,
          0 ≤ quittingTerminalDeviationDebt reward
              (quittingFiniteDeadlineTimingProfile reward 3 mixed) who ∧
            quittingTerminalDeviationDebt reward
                (quittingFiniteDeadlineTimingProfile reward 3 mixed) who ≤
              bound * (24 / 59) := by
  obtain ⟨mixed, hnash, hcertificate, _hdebt⟩ :=
    exists_finiteDeadlineTimingNash_terminalDebt_le
      reward 3 (by omega) hbound hreward
  refine ⟨mixed, hnash, hcertificate, fun who => ⟨
    quittingTerminalDeviationDebt_nonneg reward
      (quittingFiniteDeadlineTimingProfile reward 3 mixed) who, ?_⟩⟩
  exact hcertificate.debt_le_three_twentyFour_div_fiftyNine
    who hbound hreward

end GameTheory

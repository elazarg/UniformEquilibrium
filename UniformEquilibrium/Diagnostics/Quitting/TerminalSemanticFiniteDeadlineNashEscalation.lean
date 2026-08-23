/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticGlobalDebtBarrierCertificate
import UniformEquilibrium.Quitting.Paths.OutsiderNeverGluing
import UniformEquilibrium.Quitting.Terminal.TargetTail.FiniteChainTerminalCompiler
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-!
# Escalating a finite-deadline stopping equilibrium

A mixed equilibrium of the finite normal form in which every player chooses a
quit date before one common deadline, or chooses Never, has a literal
behavioral realization.  This file isolates the exact properties of that
realization that matter downstream:

* every live root is all-Continue from the deadline onward; and
* no permitted pure quit date, including Never, improves on the prescribed
  terminal payoff.

The only extra deviations in the unrestricted quitting game are later quit
dates.  Against the all-Continue suffix, their gain is the probability of
reaching the deadline on the opponents' clock times the positive part of the
player's singleton reward.  Pure-time extremality then controls every
behavioral deviation.  This gives playerwise semantic-debt bounds, their
aggregate, and a quantitative necessary condition for any global semantic
debt barrier.

The predicate below is a consumer interface.  It does not itself construct a
mixed equilibrium of the finite normal form or its behavioral realization.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame Math.Probability
open TerminalSemanticGlobalDebtBarrierCertificate

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A literal behavioral profile has the strategic properties supplied by a
mixed Nash equilibrium of the stopping-time game with finite dates strictly
before `deadline` and one Never action.

The first field is the support statement after behavioral realization.  The
second is Nash optimality against every action of the finite normal form. -/
structure QuittingFiniteDeadlineNashProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ) : Prop where
  allContinue_from : ∀ time, deadline ≤ time →
    quittingProfileLiveRoot reward profile time =
      (quittingAllContinueRoot : ι → PMF Bool)
  pureTime_le : ∀ (who : ι) (quitTime : Option ℕ),
    (quitTime = none ∨ ∃ time < deadline, quitTime = some time) →
      quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who quitTime)) who ≤
        quittingTerminalPayoff reward profile who

/-- The opponents' probability of jointly reaching the deadline, read on the
literal live-root sequence. -/
def quittingFiniteDeadlineOpponentSurvival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ) (who : ι) : ℝ :=
  quittingOpponentSurvivalWeight
    (quittingProfileLiveRoot reward profile) who 0 deadline

/-- The sole unrestricted-game charge left by a finite-deadline Nash
certificate: opponent survival to the deadline times the positive part of the
player's singleton reward. -/
def quittingFiniteDeadlineEscapeCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ) (who : ι) : ℝ :=
  quittingFiniteDeadlineOpponentSurvival reward profile deadline who *
    max 0 (reward (quittingSingletonTerminal who) who)

theorem quittingFiniteDeadlineOpponentSurvival_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ) (who : ι) :
    0 ≤ quittingFiniteDeadlineOpponentSurvival reward profile deadline who :=
  quittingOpponentSurvivalWeight_nonneg
    (quittingProfileLiveRoot reward profile) who 0 deadline

theorem quittingFiniteDeadlineOpponentSurvival_le_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ) (who : ι) :
    quittingFiniteDeadlineOpponentSurvival reward profile deadline who ≤ 1 :=
  quittingOpponentSurvivalWeight_le_one
    (quittingProfileLiveRoot reward profile) who 0 deadline

theorem quittingFiniteDeadlineEscapeCharge_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ) (who : ι) :
    0 ≤ quittingFiniteDeadlineEscapeCharge reward profile deadline who :=
  mul_nonneg
    (quittingFiniteDeadlineOpponentSurvival_nonneg reward profile deadline who)
    (le_max_left 0 _)

/-- Literal Never has value zero from any suffix on which every root is
all-Continue. -/
theorem quittingRootSequencePureTimeTerminalValue_none_eq_zero_of_allContinue_from
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (cutoff : ℕ)
    (htail : ∀ time, cutoff ≤ time →
      roots time = (quittingAllContinueRoot : ι → PMF Bool)) :
    quittingRootSequencePureTimeTerminalValue reward roots who none cutoff = 0 := by
  unfold quittingRootSequencePureTimeTerminalValue
    quittingRootSequenceHazardTerminalValue
  apply quittingRootSequenceTerminalValue_eq_zero_of_allContinue_from
  intro time htime
  unfold quittingRootSequenceUpdate
  rw [htail time htime, quittingPureTimeHazard_none]
  exact Function.update_eq_self who
    (quittingAllContinueRoot : ι → PMF Bool)

/-- Exact late-quit gain over Never on an all-Continue tail.  The only new
outcome is the player's singleton, weighted by opponent survival to the late
date. -/
theorem quittingRootSequencePureTimeTerminalValue_late_sub_none_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (deadline time : ℕ)
    (htime : deadline ≤ time)
    (htail : ∀ stage, deadline ≤ stage →
      roots stage = (quittingAllContinueRoot : ι → PMF Bool)) :
    quittingRootSequencePureTimeTerminalValue reward roots who (some time) 0 -
        quittingRootSequencePureTimeTerminalValue reward roots who none 0 =
      quittingOpponentSurvivalWeight roots who 0 time *
        reward (quittingSingletonTerminal who) who := by
  rw [show time = 0 + time by omega,
    quittingRootSequencePureTimeTerminalValue_some_sub_none_eq]
  have hnever : quittingRootSequencePureTimeTerminalValue reward roots who none
      (time + 1) = 0 :=
    quittingRootSequencePureTimeTerminalValue_none_eq_zero_of_allContinue_from
      reward roots who (time + 1) (fun stage hstage =>
        htail stage (le_trans htime (by omega)))
  simp only [Nat.zero_add]
  rw [htail time htime, hnever]
  simp

/-- A late pure quit gains at most the deadline escape charge.  Survival to a
later date is no larger than survival to the deadline. -/
theorem quittingRootSequencePureTimeTerminalValue_late_le_none_add_charge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (deadline time : ℕ)
    (htime : deadline ≤ time)
    (htail : ∀ stage, deadline ≤ stage →
      roots stage = (quittingAllContinueRoot : ι → PMF Bool)) :
    quittingRootSequencePureTimeTerminalValue reward roots who (some time) 0 ≤
      quittingRootSequencePureTimeTerminalValue reward roots who none 0 +
        quittingOpponentSurvivalWeight roots who 0 deadline *
          max 0 (reward (quittingSingletonTerminal who) who) := by
  have hexact := quittingRootSequencePureTimeTerminalValue_late_sub_none_eq
    reward roots who deadline time htime htail
  have hsurvival0 := quittingOpponentSurvivalWeight_nonneg roots who 0 time
  have hsurvivalMono : quittingOpponentSurvivalWeight roots who 0 time ≤
      quittingOpponentSurvivalWeight roots who 0 deadline :=
    antitone_quittingOpponentSurvivalWeight roots who 0 htime
  have hfirst : quittingOpponentSurvivalWeight roots who 0 time *
        reward (quittingSingletonTerminal who) who ≤
      quittingOpponentSurvivalWeight roots who 0 time *
        max 0 (reward (quittingSingletonTerminal who) who) :=
    mul_le_mul_of_nonneg_left (le_max_right 0 _) hsurvival0
  have hsecond : quittingOpponentSurvivalWeight roots who 0 time *
        max 0 (reward (quittingSingletonTerminal who) who) ≤
      quittingOpponentSurvivalWeight roots who 0 deadline *
        max 0 (reward (quittingSingletonTerminal who) who) :=
    mul_le_mul_of_nonneg_right hsurvivalMono (le_max_left 0 _)
  linarith

/-- Every pure quit time, including Never, is controlled by the prescribed
payoff plus the deadline escape charge. -/
theorem QuittingFiniteDeadlineNashProfile.pureTime_le_add_escapeCharge
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile} {deadline : ℕ}
    (certificate : QuittingFiniteDeadlineNashProfile reward profile deadline)
    (who : ι) (quitTime : Option ℕ) :
    quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who quitTime)) who ≤
      quittingTerminalPayoff reward profile who +
        quittingFiniteDeadlineEscapeCharge reward profile deadline who := by
  let roots := quittingProfileLiveRoot reward profile
  have hcharge := quittingFiniteDeadlineEscapeCharge_nonneg
    reward profile deadline who
  cases quitTime with
  | none =>
      exact (certificate.pureTime_le who none (Or.inl rfl)).trans
        (le_add_of_nonneg_right hcharge)
  | some time =>
      by_cases htime : time < deadline
      · exact (certificate.pureTime_le who (some time)
          (Or.inr ⟨time, htime, rfl⟩)).trans
          (le_add_of_nonneg_right hcharge)
      · have hlate :=
          quittingRootSequencePureTimeTerminalValue_late_le_none_add_charge
            reward roots who deadline time (Nat.le_of_not_gt htime)
            certificate.allContinue_from
        rw [← quittingTerminalPayoff_update_pureTimeBehaviorStrategy
            reward profile who (some time),
          ← quittingTerminalPayoff_update_pureTimeBehaviorStrategy
            reward profile who none] at hlate
        have hnever := certificate.pureTime_le who none (Or.inl rfl)
        dsimp only [quittingFiniteDeadlineEscapeCharge,
          quittingFiniteDeadlineOpponentSurvival] at hlate ⊢
        linarith

/-- The finite-deadline certificate bounds the full behavioral
best-response envelope, not merely pure stopping times. -/
theorem QuittingFiniteDeadlineNashProfile.bestResponseValue_le_add_escapeCharge
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile} {deadline : ℕ}
    (certificate : QuittingFiniteDeadlineNashProfile reward profile deadline)
    (who : ι) :
    quittingContinuationBestResponseValue reward profile who ≤
      quittingTerminalPayoff reward profile who +
        quittingFiniteDeadlineEscapeCharge reward profile deadline who := by
  rw [quittingContinuationBestResponseValue]
  let values : Set ℝ := Set.range fun deviation :
      (quittingGame reward).BehaviorStrategy who =>
    quittingTerminalPayoff reward (Function.update profile who deviation) who
  have hvalues : values.Nonempty :=
    ⟨quittingTerminalPayoff reward (Function.update profile who (profile who)) who,
      ⟨profile who, rfl⟩⟩
  apply csSup_le hvalues
  rintro _ ⟨deviation, rfl⟩
  calc
    quittingTerminalPayoff reward (Function.update profile who deviation) who ≤
        sSup (Set.range fun quitTime : Option ℕ =>
          quittingTerminalPayoff reward
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy reward who quitTime)) who) :=
      quittingTerminalPayoff_update_le_sSup_pureTimeBehaviorStrategy
        reward profile who deviation
    _ ≤ quittingTerminalPayoff reward profile who +
          quittingFiniteDeadlineEscapeCharge reward profile deadline who := by
      apply csSup_le
      · exact ⟨_, ⟨none, rfl⟩⟩
      · rintro _ ⟨quitTime, rfl⟩
        exact certificate.pureTime_le_add_escapeCharge who quitTime

/-- Playerwise semantic debt is no larger than the corresponding deadline
escape charge. -/
theorem QuittingFiniteDeadlineNashProfile.semanticDebt_le_escapeCharge
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile} {deadline : ℕ}
    (certificate : QuittingFiniteDeadlineNashProfile reward profile deadline)
    (who : ι) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who ≤
      quittingFiniteDeadlineEscapeCharge reward profile deadline who := by
  have hbest := certificate.bestResponseValue_le_add_escapeCharge who
  change quittingContinuationBestResponseValue reward profile who -
      quittingTerminalPayoff reward profile who ≤ _
  linarith

/-- Aggregate semantic debt is bounded by the sum of all deadline escape
charges, retaining the player-specific survival factors. -/
theorem QuittingFiniteDeadlineNashProfile.semanticDebtSum_le_sum_escapeCharge
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile} {deadline : ℕ}
    (certificate : QuittingFiniteDeadlineNashProfile reward profile deadline) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile) ≤
      ∑ who, quittingFiniteDeadlineEscapeCharge reward profile deadline who := by
  unfold quittingTerminalSemanticDebtSum
  exact Finset.sum_le_sum fun who _ => certificate.semanticDebt_le_escapeCharge who

/-- A finite-deadline certificate is an unrestricted terminal approximate
Nash profile at the largest deadline escape charge. -/
theorem QuittingFiniteDeadlineNashProfile.isεAsymptoticNash
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile} {deadline : ℕ}
    [Nonempty ι]
    (certificate : QuittingFiniteDeadlineNashProfile reward profile deadline) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward)
      (Finset.univ.sup' Finset.univ_nonempty fun who =>
        quittingFiniteDeadlineEscapeCharge reward profile deadline who)
      profile := by
  intro who deviation
  have hbest := quittingTerminalPayoff_update_le_continuationBestResponseValue
    reward profile who deviation
  have hcharge := certificate.bestResponseValue_le_add_escapeCharge who
  have hmax : quittingFiniteDeadlineEscapeCharge reward profile deadline who ≤
      Finset.univ.sup' Finset.univ_nonempty fun player =>
        quittingFiniteDeadlineEscapeCharge reward profile deadline player :=
    Finset.le_sup'
      (fun player =>
        quittingFiniteDeadlineEscapeCharge reward profile deadline player)
      (Finset.mem_univ who)
  linarith

/-- If every singleton self-reward is nonpositive, a finite-deadline Nash
certificate is already an exact unrestricted terminal Nash profile. -/
theorem QuittingFiniteDeadlineNashProfile.isZeroAsymptoticNash_of_singleton_nonpos
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile} {deadline : ℕ}
    (certificate : QuittingFiniteDeadlineNashProfile reward profile deadline)
    (hsolo : ∀ who, reward (quittingSingletonTerminal who) who ≤ 0) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0 profile := by
  intro who deviation
  have hbest := quittingTerminalPayoff_update_le_continuationBestResponseValue
    reward profile who deviation
  have hcharge := certificate.bestResponseValue_le_add_escapeCharge who
  have hzero : quittingFiniteDeadlineEscapeCharge reward profile deadline who = 0 := by
    simp [quittingFiniteDeadlineEscapeCharge, max_eq_left (hsolo who)]
  rw [hzero, add_zero] at hcharge
  simpa only [add_zero] using hbest.trans hcharge

/-- The exact terminal profile from the preceding theorem supplies its own
terminal payoff vector as a uniform-equilibrium payoff. -/
theorem QuittingFiniteDeadlineNashProfile.isUniformEquilibriumPayoff_of_singleton_nonpos
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile} {deadline : ℕ}
    (certificate : QuittingFiniteDeadlineNashProfile reward profile deadline)
    (hsolo : ∀ who, reward (quittingSingletonTerminal who) who ≤ 0) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingTerminalPayoff reward profile) :=
  quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact reward profile
    (certificate.isZeroAsymptoticNash_of_singleton_nonpos hsolo)

/-- A family of finite-deadline Nash profiles whose maximal escape charge
vanishes and whose terminal payoffs converge to one target produces that
target as a uniform-equilibrium payoff. -/
theorem quittingGame_isUniformEquilibriumPayoff_of_finiteDeadlineNash_tendsto
    [Nonempty ι]
    {index : Type} {filter : Filter index} [filter.NeBot]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι)
    (profiles : index → (quittingGame reward).BehaviorProfile)
    (deadlines : index → ℕ)
    (certificates : ∀ n, QuittingFiniteDeadlineNashProfile reward
      (profiles n) (deadlines n))
    (hcharge : Tendsto (fun n =>
      Finset.univ.sup' Finset.univ_nonempty fun who =>
        quittingFiniteDeadlineEscapeCharge reward (profiles n)
          (deadlines n) who) filter (nhds 0))
    (htarget : Tendsto (fun n => quittingTerminalPayoff reward (profiles n))
      filter (nhds target)) :
    (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  apply quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto
    reward target _ profiles hcharge
  · exact Filter.Frequently.of_forall fun n => certificates n |>.isεAsymptoticNash
  · exact htarget

/-- Target-free form: finite-deadline Nash profiles with arbitrarily small
maximal escape charge are enough for existence of some uniform-equilibrium
payoff.  Compact terminal-payoff selection is delegated to the standard
terminal-to-uniform theorem. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_finiteDeadlineNash
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hproducer : ∀ ε : ℝ, 0 < ε →
      ∃ deadline : ℕ,
      ∃ profile : (quittingGame reward).BehaviorProfile,
      ∃ _certificate : QuittingFiniteDeadlineNashProfile reward profile deadline,
        Finset.univ.sup' Finset.univ_nonempty (fun who =>
          quittingFiniteDeadlineEscapeCharge reward profile deadline who) ≤ ε) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
  intro ε hε
  obtain ⟨deadline, profile, certificate, hcharge⟩ := hproducer ε hε
  exact ⟨profile, certificate.isεAsymptoticNash.mono hcharge⟩

namespace TerminalSemanticGlobalDebtBarrierCertificate.Certificate

/-- Every certified global semantic-debt floor is bounded by the exact
finite-deadline escape bill of any supplied finite-deadline Nash profile. -/
theorem floor_le_sum_finiteDeadlineEscapeCharge
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile} {deadline : ℕ} {delta : ℝ}
    (barrier : Certificate reward delta)
    (certificate : QuittingFiniteDeadlineNashProfile reward profile deadline) :
    delta ≤
      ∑ who, quittingFiniteDeadlineEscapeCharge reward profile deadline who := by
  exact (globalDebtFloor_of_certificate reward delta barrier
    (quittingTerminalSemanticPair reward profile)
    (quittingTerminalSemanticPair_mem_carrier reward profile)).trans
      certificate.semanticDebtSum_le_sum_escapeCharge

/-- A positive global floor forces at least one player to retain a definite
opponent-survival probability at every supplied finite-deadline Nash profile.
The denominator is the total positive singleton self-reward. -/
theorem exists_floor_div_sumPositiveSingleton_le_deadlineSurvival
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile} {deadline : ℕ} {delta : ℝ}
    (barrier : Certificate reward delta) (hdelta : 0 < delta)
    (certificate : QuittingFiniteDeadlineNashProfile reward profile deadline) :
    ∃ who,
      delta / (∑ player, max 0
          (reward (quittingSingletonTerminal player) player)) ≤
        quittingFiniteDeadlineOpponentSurvival reward profile deadline who := by
  letI : Nonempty ι := barrier.nonempty_of_pos hdelta
  let singletonBill : ℝ :=
    ∑ player, max 0 (reward (quittingSingletonTerminal player) player)
  have hbill : 0 < singletonBill := by
    have hceiling := barrier.floor_le_sum_positiveSingleton
    dsimp only [singletonBill]
    linarith
  let largestSurvival : ℝ :=
    Finset.univ.sup' Finset.univ_nonempty fun who =>
      quittingFiniteDeadlineOpponentSurvival reward profile deadline who
  have hsurvival : ∀ who,
      quittingFiniteDeadlineOpponentSurvival reward profile deadline who ≤
        largestSurvival := by
    intro who
    exact Finset.le_sup'
      (fun player =>
        quittingFiniteDeadlineOpponentSurvival reward profile deadline player)
      (Finset.mem_univ who)
  have hbillUpper :
      (∑ who, quittingFiniteDeadlineEscapeCharge reward profile deadline who) ≤
        largestSurvival * singletonBill := by
    dsimp only [quittingFiniteDeadlineEscapeCharge, singletonBill]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun who _ =>
      mul_le_mul_of_nonneg_right (hsurvival who) (le_max_left 0 _)
  have hlower : delta ≤ largestSurvival * singletonBill :=
    (floor_le_sum_finiteDeadlineEscapeCharge
      barrier certificate).trans hbillUpper
  have hratio : delta / singletonBill ≤ largestSurvival :=
    (div_le_iff₀ hbill).2 (by simpa [mul_comm] using hlower)
  obtain ⟨who, _, hwho⟩ := Finset.exists_mem_eq_sup'
    Finset.univ_nonempty
    (fun player =>
      quittingFiniteDeadlineOpponentSurvival reward profile deadline player)
  refine ⟨who, ?_⟩
  rw [← hwho]
  exact hratio

end TerminalSemanticGlobalDebtBarrierCertificate.Certificate

end GameTheory

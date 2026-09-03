/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality
import UniformEquilibrium.Quitting.Paths.OutsiderNeverGluing

/-!
# Complete behavioral caps before a sure opponent deadline

If a named opponent quits surely at one live date, then every later pure quit
time is outcome-equivalent to `Never`.  Pure-time extremality therefore makes
the complete behavioral best-response cap attain its value at `Never` or at
one deterministic date no later than that sure-exit date.

This is counterfactual complete-cap semantics: only the named opponent is
forced to exit.  No bounded-clock or deadline condition is imposed on the
other players' strategies.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- If one opponent quits surely at `deadline`, then quitting strictly after
that date has exactly the same terminal payoff as `Never`. -/
theorem quittingTerminalPayoff_pureTime_eq_never_of_sureOpponentAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    {who opponent : ι} {deadline time : ℕ} (hne : opponent ≠ who)
    (hsure : quittingProfileLiveRoot reward profile deadline opponent =
      PMF.pure true)
    (hlate : deadline < time) :
    quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who (some time))) who =
      quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who none)) who := by
  let roots := quittingProfileLiveRoot reward profile
  have hweight : quittingOpponentSurvivalWeight roots who 0 time = 0 := by
    unfold quittingOpponentSurvivalWeight
    apply Finset.prod_eq_zero (show deadline ∈ Finset.range time by simpa)
    unfold quittingFixedOpponentsContinueMass
    apply quittingStationaryContinueMass_of_sureQuitter
      (quitter := opponent)
    simp only [Nat.zero_add]
    rw [Function.update_of_ne hne]
    exact hsure
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
  have htransport :=
    quittingRootSequencePureTimeTerminalValue_some_sub_none_eq
      reward roots who 0 time
  simp only [Nat.zero_add, hweight, zero_mul] at htransport
  exact sub_eq_zero.mp htransport

/-- A sure opponent exit at `deadline` makes the complete behavioral cap
attainable by `Never` or by one deterministic quit time at most `deadline`.
The selected time and the exact cap equality are returned together. -/
theorem exists_pureTime_le_deadline_or_never_terminalPayoff_eq_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    {who opponent : ι} (deadline : ℕ) (hne : opponent ≠ who)
    (hsure : quittingProfileLiveRoot reward profile deadline opponent =
      PMF.pure true) :
    ∃ choice : Option ℕ,
      (choice = none ∨ ∃ time ≤ deadline, choice = some time) ∧
        quittingTerminalPayoff reward
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy reward who choice)) who =
          quittingContinuationBestResponseValue reward profile who := by
  let value : Option ℕ → ℝ := fun choice =>
    quittingTerminalPayoff reward
      (Function.update profile who
        (quittingPureTimeBehaviorStrategy reward who choice)) who
  let candidates : Finset (Option ℕ) :=
    insert none ((Finset.range (deadline + 1)).image some)
  have hcandidates : candidates.Nonempty :=
    ⟨none, Finset.mem_insert_self none _⟩
  obtain ⟨choice, hchoice, hmax⟩ :=
    Finset.exists_max_image candidates value hcandidates
  refine ⟨choice, ?_, ?_⟩
  · simp only [candidates, Finset.mem_insert, Finset.mem_image] at hchoice
    rcases hchoice with hnone | ⟨time, htime, htimeEq⟩
    · exact Or.inl hnone
    · right
      refine ⟨time, ?_, htimeEq.symm⟩
      simp only [Finset.mem_range] at htime
      omega
  · change value choice = quittingContinuationBestResponseValue reward profile who
    rw [quittingContinuationBestResponseValue,
      sSup_range_quittingTerminalPayoff_update_eq_pureTime]
    change value choice = sSup (Set.range value)
    apply le_antisymm
    · apply le_csSup
      · refine (bddAbove_range_quittingTerminalPayoff_update
          reward profile who).mono ?_
        rintro _ ⟨candidate, rfl⟩
        exact ⟨quittingPureTimeBehaviorStrategy reward who candidate, rfl⟩
      · exact ⟨choice, rfl⟩
    · apply csSup_le (Set.range_nonempty value)
      rintro _ ⟨candidate, rfl⟩
      by_cases hcandidate : candidate = none
      · subst candidate
        exact hmax none (Finset.mem_insert_self none _)
      · obtain ⟨time, rfl⟩ := Option.ne_none_iff_exists.mp hcandidate
        by_cases htime : time ≤ deadline
        · apply hmax (some time)
          simp only [candidates, Finset.mem_insert, Finset.mem_image]
          right
          refine ⟨time, ?_, rfl⟩
          simpa only [Finset.mem_range, Nat.succ_eq_add_one] using
            Nat.lt_succ_of_le htime
        · have heq : value (some time) = value none := by
            dsimp only [value]
            exact quittingTerminalPayoff_pureTime_eq_never_of_sureOpponentAt
              reward profile hne hsure (Nat.lt_of_not_ge htime)
          rw [heq]
          exact hmax none (Finset.mem_insert_self none _)

/-- Replacing one opponent by a deterministic quit time supplies the literal
sure-exit premise for finite cap selection of every other player. -/
theorem exists_pureTime_le_deadline_or_never_terminalPayoff_eq_cap_of_opponentPureTime
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    {who opponent : ι} (deadline : ℕ) (hne : opponent ≠ who) :
    ∃ choice : Option ℕ,
      (choice = none ∨ ∃ time ≤ deadline, choice = some time) ∧
        quittingTerminalPayoff reward
            (Function.update
              (Function.update profile opponent
                (quittingPureTimeBehaviorStrategy reward opponent
                  (some deadline)))
              who (quittingPureTimeBehaviorStrategy reward who choice)) who =
          quittingContinuationBestResponseValue reward
            (Function.update profile opponent
              (quittingPureTimeBehaviorStrategy reward opponent
                (some deadline))) who := by
  apply exists_pureTime_le_deadline_or_never_terminalPayoff_eq_cap
    reward
      (Function.update profile opponent
        (quittingPureTimeBehaviorStrategy reward opponent (some deadline)))
      deadline hne
  rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate]
  unfold quittingRootSequenceUpdate
  simp [quittingBehaviorLiveHazard,
    quittingPureTimeBehaviorStrategy, quittingPureTimeHazard]

end GameTheory

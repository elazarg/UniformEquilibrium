/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import Research.Quitting.NearMinimumRetainedTailTimingNashIdentity
import UniformEquilibrium.Diagnostics.Quitting.FiniteDeadlineTimingRecursion

/-!
# Retained-tail finite timing recursion

This module supplies the exact normal-form recursion omitted by the zero-tail
finite timing game.  Every pure timing declaration is executed for the finite
word and resumes one fixed actual behavioral tail on joint `Never`.  The mixed
evaluator is definitionally the expected payoff of that literal graft.

The final compiler starts from an actual mixed Nash law with positive `Never`
mass in every marginal.  It does not assume a supplied credible root stack.
No approximate-Nash, behavioral-Nash, Fin4 chronology, or punishment adapter
is asserted here.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Literal pure payoff of one retained-tail finite timing declaration. -/
def quittingRetainedTailTimingPurePayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (choices : ι → QuittingFiniteDeadlineTimingAction deadline)
    (who : ι) : ℝ :=
  quittingTerminalPayoff reward
    (quittingRetainedTailFiniteTimingGraft reward
      (quittingRetainedTailPureTimingRootStack deadline choices) tail) who

/-- Expected retained-tail payoff under independent mixed timing laws. -/
def quittingRetainedTailTimingMixedPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) : ℝ :=
  Math.Probability.expect (pmfPi mixed) fun choices =>
    quittingRetainedTailTimingPurePayoff reward tail deadline choices who

omit [DecidableEq ι] in
/-- The retained-tail normal-form mixed EU is exactly the expectation of the
literal behavioral graft, with no semantic replacement of the terminal tail. -/
theorem quittingRetainedTailFiniteTimingGame_mixedEU_eq_mixedPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) :
    (quittingRetainedTailFiniteTimingGame reward deadline tail).mixedExtension.eu
        mixed who =
      quittingRetainedTailTimingMixedPayoff reward tail deadline mixed who := by
  letI : Finite
      (quittingRetainedTailFiniteTimingGame reward deadline tail).Outcome :=
    quittingRetainedTailFiniteTimingGame_finiteOutcome reward deadline tail
  rw [(quittingRetainedTailFiniteTimingGame reward deadline tail).mixedExtension_eu]
  unfold quittingRetainedTailTimingMixedPayoff
    quittingRetainedTailTimingPurePayoff quittingRetainedTailFiniteTimingGame
  simp only [KernelGame.eu_ofPureEU]
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- The current root and shifted choices split the literal pure root word. -/
theorem quittingRetainedTailPureTimingRootStack_succ
    (deadline : ℕ)
    (choices : ι → QuittingFiniteDeadlineTimingAction (deadline + 1)) :
    quittingRetainedTailPureTimingRootStack (deadline + 1) choices =
      timingChoicesRoot choices ::
        quittingRetainedTailPureTimingRootStack deadline
          (timingChoicesTail choices) := by
  unfold quittingRetainedTailPureTimingRootStack
  rw [List.ofFn_succ]
  congr 1
  · funext who
    unfold timingChoicesRoot
    cases hchoice : choices who with
    | none => rfl
    | some time =>
        cases time using Fin.cases with
        | zero => rfl
        | succ later => rfl
  · apply congrArg List.ofFn
    funext date
    funext who
    apply congrArg PMF.pure
    cases hchoice : choices who with
    | none => simp [hchoice, timingChoicesTail, timingActionTail]
    | some time =>
        cases time using Fin.cases with
        | zero =>
            have htail : timingChoicesTail choices who = none := by
              unfold timingChoicesTail
              rw [hchoice]
              rfl
            rw [htail]
            have hleft : (0 : Fin (deadline + 1)) ≠ date.succ := by
              intro heq
              have := congrArg Fin.val heq
              simp at this
            have hright : (none : Option (Fin deadline)) ≠ some date := by
              intro heq
              cases heq
            simp [hleft, hright]
        | succ later => simp [hchoice, timingChoicesTail, timingActionTail]

omit [DecidableEq ι] in
/-- At deadline zero the retained timing payoff is the prescribed payoff of
the actual retained tail. -/
theorem quittingRetainedTailTimingMixedPayoff_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction 0))
    (who : ι) :
    quittingRetainedTailTimingMixedPayoff reward tail 0 mixed who =
      quittingTerminalPayoff reward tail who := by
  have hmixed : mixed = fun _ => PMF.pure none := by
    funext player
    exact Math.ProbabilityMassFunction.eq_pure_of_subsingleton _ none
  rw [hmixed]
  unfold quittingRetainedTailTimingMixedPayoff
  rw [pmfPi_pure]
  simp [quittingRetainedTailTimingPurePayoff,
    quittingRetainedTailPureTimingRootStack,
    quittingRetainedTailFiniteTimingGraft]

omit [DecidableEq ι] in
/-- Bellman peeling for a deterministic retained-tail timing declaration. -/
theorem quittingRetainedTailTimingPurePayoff_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (choices : ι → QuittingFiniteDeadlineTimingAction (deadline + 1))
    (who : ι) :
    quittingRetainedTailTimingPurePayoff reward tail (deadline + 1) choices who =
      quittingRootPayoff reward
        (fun player => quittingRetainedTailTimingPurePayoff reward tail deadline
          (timingChoicesTail choices) player)
        (fun player => timingActionCurrent (choices player)) who := by
  unfold quittingRetainedTailTimingPurePayoff
    quittingRetainedTailFiniteTimingGraft
  rw [quittingRetainedTailPureTimingRootStack_succ,
    quittingLiteralRootStackProfile_cons,
    quittingTerminalPayoff_rootThenContinuation_eq]
  unfold quittingRootExpectedPayoff timingChoicesRoot
  rw [pmfPi_pure]
  simp only [Math.Probability.expect_pure]

omit [DecidableEq ι] in
/-- Conditional on a supported current action, the retained pure payoff
averages to the current root payoff with the independently conditioned
retained tails as continuation. -/
theorem expect_conditional_quittingRetainedTailTimingPurePayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
    (now : ι → Bool)
    (hnow : pmfPi (fun who =>
      pushforward (mixed who) timingActionCurrent) now ≠ 0)
    (who : ι) :
    Math.Probability.expect
        (pmfPi fun player =>
          condOn (mixed player) timingActionCurrent (now player))
        (fun choices => quittingRetainedTailTimingPurePayoff reward tail
          (deadline + 1) choices who) =
      quittingRootPayoff reward
        (fun player => quittingRetainedTailTimingMixedPayoff reward tail deadline
          (fun other => timingLawTail (mixed other)) player)
        now who := by
  let conditional : PMF
      (ι → QuittingFiniteDeadlineTimingAction (deadline + 1)) :=
    pmfPi fun player =>
      condOn (mixed player) timingActionCurrent (now player)
  have hcurrent : ∀ {choices : ι →
      QuittingFiniteDeadlineTimingAction (deadline + 1)},
      choices ∈ conditional.support →
        (fun player => timingActionCurrent (choices player)) = now := by
    intro choices hchoices
    funext player
    have hnowPlayer :
        pushforward (mixed player) timingActionCurrent (now player) ≠ 0 :=
      pmfPi_coord_ne_zero_of_ne_zero
        (fun other => pushforward (mixed other) timingActionCurrent)
        now hnow player
    have hchoicePlayer :
        condOn (mixed player) timingActionCurrent (now player)
            (choices player) ≠ 0 :=
      pmfPi_coord_ne_zero_of_ne_zero
        (fun other => condOn (mixed other) timingActionCurrent (now other))
        choices (by simpa only [PMF.mem_support_iff] using hchoices) player
    exact condOn_support_project (mixed player) timingActionCurrent
      (now player) hnowPlayer
      (by simpa only [PMF.mem_support_iff] using hchoicePlayer)
  by_cases hquit : (quittingQuitters now).Nonempty
  · calc
      Math.Probability.expect conditional
          (fun choices => quittingRetainedTailTimingPurePayoff reward tail
            (deadline + 1) choices who) =
        Math.Probability.expect conditional
          (fun _ => reward ⟨quittingQuitters now, hquit⟩ who) := by
            apply Math.ProbabilityMassFunction.expect_congr_on_support
            intro choices hchoices
            rw [quittingRetainedTailTimingPurePayoff_succ,
              hcurrent hchoices]
            simp [quittingRootPayoff, hquit]
      _ = reward ⟨quittingQuitters now, hquit⟩ who :=
        Math.Probability.expect_const conditional _
      _ = quittingRootPayoff reward
          (fun player => quittingRetainedTailTimingMixedPayoff reward tail
            deadline (fun other => timingLawTail (mixed other)) player)
          now who := by simp [quittingRootPayoff, hquit]
  · have hnowAll : now = quittingAllContinueAction :=
      eq_quittingAllContinueAction_of_quittingQuitters_not_nonempty now hquit
    have hmap : pushforward conditional timingChoicesTail =
        pmfPi (fun player => timingLawTail (mixed player)) := by
      unfold conditional timingChoicesTail timingLawTail
      rw [hnowAll, pmfPi_push_coordwise]
      rfl
    calc
      Math.Probability.expect conditional
          (fun choices => quittingRetainedTailTimingPurePayoff reward tail
            (deadline + 1) choices who) =
        Math.Probability.expect conditional
          (fun choices => quittingRetainedTailTimingPurePayoff reward tail
            deadline (timingChoicesTail choices) who) := by
              apply Math.ProbabilityMassFunction.expect_congr_on_support
              intro choices hchoices
              rw [quittingRetainedTailTimingPurePayoff_succ,
                hcurrent hchoices, hnowAll]
              simp [quittingRootPayoff]
      _ = Math.Probability.expect
          (pushforward conditional timingChoicesTail)
          (fun choices => quittingRetainedTailTimingPurePayoff reward tail
            deadline choices who) := by
              unfold pushforward
              exact (Math.Probability.expect_map timingChoicesTail conditional
                (fun choices => quittingRetainedTailTimingPurePayoff reward tail
                  deadline choices who)).symm
      _ = quittingRetainedTailTimingMixedPayoff reward tail deadline
          (fun player => timingLawTail (mixed player)) who := by
            rw [hmap]
            rfl
      _ = quittingRootPayoff reward
          (fun player => quittingRetainedTailTimingMixedPayoff reward tail
            deadline (fun other => timingLawTail (mixed other)) player)
          now who := by
            rw [hnowAll]
            simp [quittingRootPayoff]

/-- Bellman peeling for arbitrary independent retained-tail timing laws. -/
theorem quittingRetainedTailTimingMixedPayoff_bellman
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
    (who : ι) :
    quittingRetainedTailTimingMixedPayoff reward tail (deadline + 1) mixed who =
      quittingRootExpectedPayoff reward
        (fun player => quittingRetainedTailTimingMixedPayoff reward tail deadline
          (fun other => timingLawTail (mixed other)) player)
        (fun player => pushforward (mixed player) timingActionCurrent) who := by
  unfold quittingRetainedTailTimingMixedPayoff
  rw [pmfPi_disintegrate_timingCurrent,
    Math.Probability.expect_bind]
  unfold quittingRootExpectedPayoff
  apply Math.ProbabilityMassFunction.expect_congr_on_support
  intro now hnow
  exact expect_conditional_quittingRetainedTailTimingPurePayoff
    reward tail deadline mixed now
      (by simpa only [PMF.mem_support_iff] using hnow) who

/-- Replacing one conditional timing tail changes retained payoff by the
shorter retained-game gain times the common current Continue reach. -/
theorem quittingRetainedTailTimingMixedPayoff_withTail_sub
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
    (who : ι)
    (replacement : PMF (QuittingFiniteDeadlineTimingAction deadline))
    (hcontinue : pushforward (mixed who) timingActionCurrent false ≠ 0) :
    quittingRetainedTailTimingMixedPayoff reward tail (deadline + 1)
          (timingMixedWithTail mixed who replacement) who -
        quittingRetainedTailTimingMixedPayoff reward tail (deadline + 1)
          mixed who =
      quittingStationaryContinueMass
          (fun player => pushforward (mixed player) timingActionCurrent) *
        (quittingRetainedTailTimingMixedPayoff reward tail deadline
            (Function.update (fun player => timingLawTail (mixed player))
              who replacement) who -
          quittingRetainedTailTimingMixedPayoff reward tail deadline
            (fun player => timingLawTail (mixed player)) who) := by
  rw [quittingRetainedTailTimingMixedPayoff_bellman,
    quittingRetainedTailTimingMixedPayoff_bellman,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    timingMixedWithTail_current,
    timingMixedWithTail_tail mixed who replacement hcontinue]
  ring

/-- Positive current reach transfers ordinary Nash equilibrium to the
coordinatewise conditioned retained-tail game. -/
theorem retainedTimingLawTail_isNash_of_isNash_of_positiveContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
    (hnash : (quittingRetainedTailFiniteTimingGame reward
      (deadline + 1) tail).mixedExtension.IsNash mixed)
    (hcontinue : ∀ who,
      pushforward (mixed who) timingActionCurrent false ≠ 0) :
    (quittingRetainedTailFiniteTimingGame reward
      deadline tail).mixedExtension.IsNash
        (fun who => timingLawTail (mixed who)) := by
  intro who replacement
  have hnashSplice := hnash who
    (timingLawWithTail (mixed who) replacement)
  have htransport := quittingRetainedTailTimingMixedPayoff_withTail_sub
    reward tail deadline mixed who replacement (hcontinue who)
  rw [← quittingRetainedTailFiniteTimingGame_mixedEU_eq_mixedPayoff
      reward tail (deadline + 1) mixed who,
    ← quittingRetainedTailFiniteTimingGame_mixedEU_eq_mixedPayoff
      reward tail (deadline + 1)
        (timingMixedWithTail mixed who replacement) who] at htransport
  change (quittingRetainedTailFiniteTimingGame reward
      (deadline + 1) tail).mixedExtension.eu mixed who ≥
    (quittingRetainedTailFiniteTimingGame reward
      (deadline + 1) tail).mixedExtension.eu
        (timingMixedWithTail mixed who replacement) who at hnashSplice
  have hreach := timingCurrentRoot_continueMass_pos deadline mixed hcontinue
  rw [quittingRetainedTailFiniteTimingGame_mixedEU_eq_mixedPayoff,
    quittingRetainedTailFiniteTimingGame_mixedEU_eq_mixedPayoff]
  by_contra htailGain
  have htailPos : 0 <
      quittingRetainedTailTimingMixedPayoff reward tail deadline
          (Function.update (fun player => timingLawTail (mixed player))
            who replacement) who -
        quittingRetainedTailTimingMixedPayoff reward tail deadline
          (fun player => timingLawTail (mixed player)) who :=
    sub_pos.mpr (lt_of_not_ge htailGain)
  have hmulPos := mul_pos hreach htailPos
  have hwholeNonpos :
      (quittingRetainedTailFiniteTimingGame reward
          (deadline + 1) tail).mixedExtension.eu
            (timingMixedWithTail mixed who replacement) who -
        (quittingRetainedTailFiniteTimingGame reward
          (deadline + 1) tail).mixedExtension.eu mixed who ≤ 0 :=
    sub_nonpos.mpr hnashSplice
  have hmulNonpos :
      quittingStationaryContinueMass
          (fun player => pushforward (mixed player) timingActionCurrent) *
        (quittingRetainedTailTimingMixedPayoff reward tail deadline
            (Function.update (fun player => timingLawTail (mixed player))
              who replacement) who -
          quittingRetainedTailTimingMixedPayoff reward tail deadline
            (fun player => timingLawTail (mixed player)) who) ≤ 0 := by
    rw [← htransport]
    exact hwholeNonpos
  exact (not_lt_of_ge hmulNonpos) hmulPos

/-- Pure current stopping is the current root's Quit endpoint in the retained
Bellman decomposition. -/
theorem quittingRetainedTailTimingMixedPayoff_update_current_eq_quitPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
    (who : ι) :
    quittingRetainedTailTimingMixedPayoff reward tail (deadline + 1)
        (Function.update mixed who
          (PMF.pure (some (0 : Fin (deadline + 1))))) who =
      quittingRootQuitPayoff reward
        (fun player => quittingRetainedTailTimingMixedPayoff reward tail deadline
          (fun other => timingLawTail (mixed other)) player)
        (fun player => pushforward (mixed player) timingActionCurrent) who := by
  rw [quittingRetainedTailTimingMixedPayoff_bellman]
  let root : ι → PMF Bool := fun player =>
    pushforward (mixed player) timingActionCurrent
  let updated := Function.update mixed who
    (PMF.pure (some (0 : Fin (deadline + 1))))
  have hroot :
      (fun player => pushforward (updated player) timingActionCurrent) =
        Function.update root who (PMF.pure true) := by
    funext player
    by_cases hplayer : player = who
    · subst player
      rw [Function.update_self]
      unfold updated pushforward
      rw [Function.update_self, PMF.pure_map]
      rfl
    · unfold updated root
      rw [Function.update_of_ne hplayer, Function.update_of_ne hplayer]
  rw [hroot]
  unfold quittingRootQuitPayoff
  exact quittingRootQuitPayoff_tail_irrel reward _ _ root who

/-- Forcing current Continue while retaining the conditioned timing tail is
the current root's Continue endpoint. -/
theorem quittingRetainedTailTimingMixedPayoff_update_liftedTail_eq_continuePayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
    (who : ι) :
    quittingRetainedTailTimingMixedPayoff reward tail (deadline + 1)
        (Function.update mixed who
          ((timingLawTail (mixed who)).map timingActionLift)) who =
      quittingRootContinuePayoff reward
        (fun player => quittingRetainedTailTimingMixedPayoff reward tail deadline
          (fun other => timingLawTail (mixed other)) player)
        (fun player => pushforward (mixed player) timingActionCurrent) who := by
  rw [quittingRetainedTailTimingMixedPayoff_bellman]
  let root : ι → PMF Bool := fun player =>
    pushforward (mixed player) timingActionCurrent
  let tails : ι → PMF (QuittingFiniteDeadlineTimingAction deadline) :=
    fun player => timingLawTail (mixed player)
  have hroot :
      (fun player => pushforward
        (Function.update mixed who
          ((timingLawTail (mixed who)).map timingActionLift) player)
        timingActionCurrent) =
      Function.update root who (PMF.pure false) := by
    funext player
    by_cases hplayer : player = who
    · subst player
      rw [Function.update_self, Function.update_self]
      exact map_liftedTail_current _
    · unfold root
      rw [Function.update_of_ne hplayer, Function.update_of_ne hplayer]
  have htail :
      (fun player => timingLawTail
        (Function.update mixed who
          ((timingLawTail (mixed who)).map timingActionLift) player)) =
      tails := by
    rw [timingLawTail_update, timingLawTail_map_lifted]
    exact Function.update_eq_self who tails
  rw [hroot, htail]
  rfl

/-- The current Boolean marginal of a retained-tail mixed timing Nash law is
an exact endpoint Nash root against the actual conditioned retained payoff. -/
theorem retainedTimingCurrentRoot_isZeroEndpointNash_of_isNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
    (hnash : (quittingRetainedTailFiniteTimingGame reward
      (deadline + 1) tail).mixedExtension.IsNash mixed) :
    IsεQuittingRootEndpointNash reward
      (fun player => quittingRetainedTailTimingMixedPayoff reward tail deadline
        (fun other => timingLawTail (mixed other)) player)
      0 (fun player => pushforward (mixed player) timingActionCurrent) := by
  rw [isεQuittingRootEndpointNash_iff_purePayoff_le]
  intro who
  constructor
  · have hquit := hnash who
      (PMF.pure (some (0 : Fin (deadline + 1))))
    rw [quittingRetainedTailFiniteTimingGame_mixedEU_eq_mixedPayoff,
      quittingRetainedTailFiniteTimingGame_mixedEU_eq_mixedPayoff] at hquit
    calc
      quittingRootQuitPayoff reward
          (fun player => quittingRetainedTailTimingMixedPayoff reward tail
            deadline (fun other => timingLawTail (mixed other)) player)
          (fun player => pushforward (mixed player) timingActionCurrent) who =
        quittingRetainedTailTimingMixedPayoff reward tail (deadline + 1)
          (Function.update mixed who
            (PMF.pure (some (0 : Fin (deadline + 1))))) who :=
        (quittingRetainedTailTimingMixedPayoff_update_current_eq_quitPayoff
          reward tail deadline mixed who).symm
      _ ≤ quittingRetainedTailTimingMixedPayoff reward tail (deadline + 1)
          mixed who := hquit
      _ = quittingRootSuccessorPayoff reward
          (fun player => quittingRetainedTailTimingMixedPayoff reward tail
            deadline (fun other => timingLawTail (mixed other)) player)
          (fun player => pushforward (mixed player) timingActionCurrent) who :=
        quittingRetainedTailTimingMixedPayoff_bellman
          reward tail deadline mixed who
      _ ≤ _ := by simp
  · have hcontinue := hnash who
      ((timingLawTail (mixed who)).map timingActionLift)
    rw [quittingRetainedTailFiniteTimingGame_mixedEU_eq_mixedPayoff,
      quittingRetainedTailFiniteTimingGame_mixedEU_eq_mixedPayoff] at hcontinue
    calc
      quittingRootContinuePayoff reward
          (fun player => quittingRetainedTailTimingMixedPayoff reward tail
            deadline (fun other => timingLawTail (mixed other)) player)
          (fun player => pushforward (mixed player) timingActionCurrent) who =
        quittingRetainedTailTimingMixedPayoff reward tail (deadline + 1)
          (Function.update mixed who
            ((timingLawTail (mixed who)).map timingActionLift)) who :=
        (quittingRetainedTailTimingMixedPayoff_update_liftedTail_eq_continuePayoff
          reward tail deadline mixed who).symm
      _ ≤ quittingRetainedTailTimingMixedPayoff reward tail (deadline + 1)
          mixed who := hcontinue
      _ = quittingRootSuccessorPayoff reward
          (fun player => quittingRetainedTailTimingMixedPayoff reward tail
            deadline (fun other => timingLawTail (mixed other)) player)
          (fun player => pushforward (mixed player) timingActionCurrent) who :=
        quittingRetainedTailTimingMixedPayoff_bellman
          reward tail deadline mixed who
      _ ≤ _ := by simp

/-! ## Positive Never mass and exact reconstruction -/

/-- Positive mass on `Never` forces positive current Continue mass. -/
theorem timingActionCurrent_false_ne_zero_of_none_toReal_pos
    {deadline : ℕ}
    (law : PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
    (hnever : 0 < (law none).toReal) :
    pushforward law timingActionCurrent false ≠ 0 := by
  intro hzero
  have hle : law none ≤
      pushforward law timingActionCurrent false := by
    simpa [timingActionCurrent] using
      (le_pushforward_apply law timingActionCurrent
        (none : QuittingFiniteDeadlineTimingAction (deadline + 1)))
  rw [hzero] at hle
  have hlaw : law none = 0 := le_antisymm hle bot_le
  rw [hlaw] at hnever
  simp at hnever

/-- Positive `Never` mass remains positive in the conditioned shifted tail. -/
theorem timingLawTail_none_toReal_pos_of_none_toReal_pos
    {deadline : ℕ}
    (law : PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
    (hnever : 0 < (law none).toReal) :
    0 < (timingLawTail law none).toReal := by
  have hcontinue :=
    timingActionCurrent_false_ne_zero_of_none_toReal_pos law hnever
  have hlaw : law none ≠ 0 := by
    intro hzero
    rw [hzero] at hnever
    simp at hnever
  have hconditional : none ∈
      (condOn law timingActionCurrent false).support := by
    rw [PMF.mem_support_iff,
      condOn_apply law timingActionCurrent false none hcontinue]
    simp only [timingActionCurrent, ↓reduceIte]
    exact ENNReal.div_ne_zero.mpr ⟨hlaw,
      PMF.apply_ne_top (pushforward law timingActionCurrent) false⟩
  have hmapped : none ∈
      ((timingLawTail law).map timingActionLift).support := by
    rw [timingLawTail_map_lift law hcontinue]
    exact hconditional
  rcases (PMF.mem_support_map_iff timingActionLift
      (timingLawTail law) none).mp hmapped with
    ⟨action, haction, hlift⟩
  have hactionNone : action = none := by
    cases action with
    | none => rfl
    | some time => simp [timingActionLift] at hlift
  subst action
  exact ENNReal.toReal_pos
    ((PMF.mem_support_iff (timingLawTail law) none).mp haction)
    (PMF.apply_ne_top (timingLawTail law) none)

/-- The pure `Never` timing law has pure `Never` as its conditioned tail. -/
@[simp] theorem retainedTimingLawTail_pure_none {deadline : ℕ} :
    timingLawTail
        (PMF.pure none :
          PMF (QuittingFiniteDeadlineTimingAction (deadline + 1))) =
      (PMF.pure none :
        PMF (QuittingFiniteDeadlineTimingAction deadline)) := by
  let law : PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)) :=
    PMF.pure none
  have hcontinue : pushforward law timingActionCurrent false ≠ 0 := by
    unfold law pushforward
    rw [PMF.pure_map]
    simp [timingActionCurrent]
  have hcond : condOn law timingActionCurrent false = law := by
    apply PMF.ext
    intro action
    rw [condOn_apply law timingActionCurrent false action hcontinue]
    cases action with
    | none =>
        unfold pushforward law
        rw [PMF.pure_map]
        simp [timingActionCurrent]
    | some time => simp [law]
  have hlift := timingLawTail_map_lift law hcontinue
  rw [hcond] at hlift
  have hmapped := congrArg (fun source => source.map timingActionTail) hlift
  have hcomp :
      (timingActionTail (dates := deadline)) ∘
          (timingActionLift (dates := deadline)) =
        (id : QuittingFiniteDeadlineTimingAction deadline →
          QuittingFiniteDeadlineTimingAction deadline) := by
    funext action
    exact timingActionTail_lift action
  rw [PMF.map_comp, hcomp, PMF.map_id] at hmapped
  dsimp only [law] at hmapped
  simpa only [PMF.pure_map, timingActionTail] using hmapped

/-- Every retained timing deadline evaluates pure `Never` laws as the
prescribed actual tail payoff. -/
theorem quittingRetainedTailTimingMixedPayoff_pureNever
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile) :
    ∀ (deadline : ℕ) (who : ι),
      quittingRetainedTailTimingMixedPayoff reward tail deadline
          (fun _ => PMF.pure none) who =
        quittingTerminalPayoff reward tail who := by
  intro deadline
  induction deadline with
  | zero =>
      intro who
      exact quittingRetainedTailTimingMixedPayoff_zero
        reward tail (fun _ => PMF.pure none) who
  | succ deadline ih =>
      intro who
      rw [quittingRetainedTailTimingMixedPayoff_bellman]
      have hroot :
          (fun player : ι => pushforward
            (PMF.pure (none : QuittingFiniteDeadlineTimingAction
              (deadline + 1))) timingActionCurrent) =
            quittingAllContinueRoot := by
        funext player
        unfold pushforward quittingAllContinueRoot
        rw [PMF.pure_map]
        rfl
      have htail :
          (fun player : ι => timingLawTail
            (PMF.pure (none : QuittingFiniteDeadlineTimingAction
              (deadline + 1)))) =
            fun _ => (PMF.pure none :
              PMF (QuittingFiniteDeadlineTimingAction deadline)) := by
        funext player
        exact retainedTimingLawTail_pure_none
      rw [hroot, htail]
      have hpayoff :
          (fun player : ι =>
            quittingRetainedTailTimingMixedPayoff reward tail deadline
              (fun _ => PMF.pure none) player) =
            fun player => quittingTerminalPayoff reward tail player := by
        funext player
        exact ih player
      rw [hpayoff]
      unfold quittingRootExpectedPayoff quittingAllContinueRoot
      rw [pmfPi_pure]
      simp [quittingRootPayoff]

/-! ## The actual mixed-Nash compiler -/

/-- If every exact endpoint-Nash current root against the prescribed tail is
all-Continue, then an actual retained-tail timing Nash law with positive
`Never` mass in every marginal is literally the pure-`Never` law. -/
theorem retainedTailFiniteTimingNash_eq_pureNever_of_root_rigidity
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (hrootRigidity : ∀ root : ι → PMF Bool,
      IsεQuittingRootEndpointNash reward
          (fun who => quittingTerminalPayoff reward tail who) 0 root →
        root = quittingAllContinueRoot) :
    ∀ (deadline : ℕ)
      (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)),
      (quittingRetainedTailFiniteTimingGame reward deadline tail).mixedExtension.IsNash
          mixed →
      (∀ who, 0 < (mixed who none).toReal) →
      ∀ who, mixed who = PMF.pure none := by
  intro deadline
  induction deadline with
  | zero =>
      intro mixed hnash hnever who
      exact Math.ProbabilityMassFunction.eq_pure_of_subsingleton
        (mixed who) none
  | succ deadline ih =>
      intro mixed hnash hnever
      have hcontinue : ∀ who,
          pushforward (mixed who) timingActionCurrent false ≠ 0 :=
        fun who =>
          timingActionCurrent_false_ne_zero_of_none_toReal_pos
            (mixed who) (hnever who)
      have htailNash :
          (quittingRetainedTailFiniteTimingGame reward
            deadline tail).mixedExtension.IsNash
              (fun who => timingLawTail (mixed who)) :=
        retainedTimingLawTail_isNash_of_isNash_of_positiveContinue
          reward tail deadline mixed hnash hcontinue
      have htailNever : ∀ who,
          0 < (timingLawTail (mixed who) none).toReal :=
        fun who =>
          timingLawTail_none_toReal_pos_of_none_toReal_pos
            (mixed who) (hnever who)
      have htailPure : ∀ who,
          timingLawTail (mixed who) = PMF.pure none :=
        ih (fun who => timingLawTail (mixed who)) htailNash htailNever
      have htails :
          (fun who => timingLawTail (mixed who)) =
            fun _ => (PMF.pure none :
              PMF (QuittingFiniteDeadlineTimingAction deadline)) := by
        funext who
        exact htailPure who
      have hendpoint :=
        retainedTimingCurrentRoot_isZeroEndpointNash_of_isNash
          reward tail deadline mixed hnash
      have hcontinuation :
          (fun player =>
            quittingRetainedTailTimingMixedPayoff reward tail deadline
              (fun other => timingLawTail (mixed other)) player) =
            fun player => quittingTerminalPayoff reward tail player := by
        rw [htails]
        funext player
        exact quittingRetainedTailTimingMixedPayoff_pureNever
          reward tail deadline player
      rw [hcontinuation] at hendpoint
      have hroot := hrootRigidity
        (fun player => pushforward (mixed player) timingActionCurrent)
        hendpoint
      intro who
      apply timingLaw_eq_of_current_tail_eq
          (mixed who)
          (PMF.pure none :
            PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
      · have hcoordinate := congrFun hroot who
        rw [hcoordinate]
        unfold quittingAllContinueRoot pushforward
        rw [PMF.pure_map]
        rfl
      · rw [htailPure who, retainedTimingLawTail_pure_none]
      · exact hcontinue who
      · unfold pushforward
        rw [PMF.pure_map]
        simp [timingActionCurrent]

/-- Near a positive global debt minimum, the retained-tail timing normal form
has only the literal pure-`Never` Nash law among laws giving every player
positive `Never` probability.  This is an actual normal-form Nash compiler,
not a supplied root-stack verifier. -/
theorem nearMinimum_retainedTailFiniteTimingNash_eq_pureNever
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    {M kappa excess : ℝ}
    (hM : 0 < M) (hkappa : 0 < kappa)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : 0 < quittingTerminalDebtSumInf reward)
    (htail : quittingTerminalDebtSum reward tail ≤
      quittingTerminalDebtSumInf reward + excess)
    (hsingleton : ∀ who,
      reward (quittingSingletonTerminal who) who + kappa ≤
        quittingTerminalPayoff reward tail who)
    (hnear : excess <
      kappa * quittingTerminalDebtSumInf reward / (2 * M))
    (hnash : (quittingRetainedTailFiniteTimingGame reward
      deadline tail).mixedExtension.IsNash mixed)
    (hnever : ∀ who, 0 < (mixed who none).toReal) :
    ∀ who, mixed who = PMF.pure none := by
  apply retainedTailFiniteTimingNash_eq_pureNever_of_root_rigidity
    reward tail
  · intro root hnashRoot
    exact nearMinimum_rootNashAgainstPayoff_eq_allContinue
      reward tail root hM hkappa hreward hminimum htail hsingleton
        hnashRoot hnear
  · exact hnash
  · exact hnever

/-- Profile-level form of the retained-tail mixed-Nash rigidity compiler. -/
theorem nearMinimum_retainedTailFiniteTimingNash_eq_pureNeverProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    {M kappa excess : ℝ}
    (hM : 0 < M) (hkappa : 0 < kappa)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : 0 < quittingTerminalDebtSumInf reward)
    (htail : quittingTerminalDebtSum reward tail ≤
      quittingTerminalDebtSumInf reward + excess)
    (hsingleton : ∀ who,
      reward (quittingSingletonTerminal who) who + kappa ≤
        quittingTerminalPayoff reward tail who)
    (hnear : excess <
      kappa * quittingTerminalDebtSumInf reward / (2 * M))
    (hnash : (quittingRetainedTailFiniteTimingGame reward
      deadline tail).mixedExtension.IsNash mixed)
    (hnever : ∀ who, 0 < (mixed who none).toReal) :
    mixed = fun _ => PMF.pure none := by
  funext who
  exact nearMinimum_retainedTailFiniteTimingNash_eq_pureNever
    reward tail deadline mixed hM hkappa hreward hminimum htail
      hsingleton hnear hnash hnever who

end GameTheory

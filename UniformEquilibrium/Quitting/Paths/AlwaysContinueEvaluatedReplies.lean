import UniformEquilibrium.Quitting.Paths.EvaluatedPureTimeCap
import UniformEquilibrium.Quitting.Paths.FiniteHorizonStoppingLawPayoff

/-! # Bounded clock evaluations against actual all-Continue opponents

Every finite pure-time reply receives its actual singleton reward multiplied
by the actual exit weight; Never receives zero. The complete behavioral cap
uses the canonical all-date/Never envelope, not a restricted reply menu.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Actual all-Continue play has a pure Never law in every coordinate. -/
theorem quittingBehaviorStoppingLaws_alwaysContinue_eq_pure_never
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingBehaviorStoppingLaws reward (quittingAlwaysContinueProfile reward) =
      fun _ => PMF.pure none := by
  funext who
  change quittingBehaviorStoppingLaw reward
    (quittingPureTimeBehaviorStrategy reward who none) = PMF.pure none
  exact quittingBehaviorStoppingLaw_pureTime_never reward who

/-- Literal date/Never values against actual all-Continue laws, for ANY evaluation. -/
theorem quittingStoppingLawEvaluatedPayoff_alwaysContinue_pureTime_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (evaluation : WithTop ℕ → ℝ) (who : ι) (choice : Option ℕ) :
    letI : Nonempty ι := ⟨who⟩
    quittingStoppingLawEvaluatedPayoff reward evaluation
        (Function.update (quittingBehaviorStoppingLaws reward
          (quittingAlwaysContinueProfile reward)) who (PMF.pure choice)) who =
      match choice with
      | none => 0
      | some time => evaluation (time : WithTop ℕ) *
          reward (quittingSingletonTerminal who) who := by
  let : Nonempty ι := ⟨who⟩
  rw [quittingBehaviorStoppingLaws_alwaysContinue_eq_pure_never]
  have hupdate : Function.update (fun _ : ι => PMF.pure none) who (PMF.pure choice) =
      fun player => PMF.pure (Function.update (fun _ : ι => none) who choice player) := by
    funext player
    by_cases hplayer : player = who <;> simp [hplayer]
  rw [hupdate, quittingStoppingLawEvaluatedPayoff, pmfPi_pure, expect_pure]
  cases choice with
  | none =>
      simp only [Function.update_eq_self, quittingPureClockEvaluatedPayoff,
        quittingFirstStoppingOutcome_all_never]
  | some time =>
      have hevent : QuittingClockFirstEvent time (quittingSingletonTerminal who)
          (Function.update (fun _ : ι => none) who (some time)) := by
        intro player
        by_cases hplayer : player = who
        · subst player
          simp [quittingSingletonTerminal]
        · simp [quittingSingletonTerminal, hplayer]
      obtain ⟨hearliest, hfirst⟩ := (quittingClockFirstEvent_iff
        time (quittingSingletonTerminal who) _).mp hevent
      simp only [quittingPureClockEvaluatedPayoff, hfirst, hearliest]

/-- A nonnegative singleton and an evaluation in [0,1] bound the COMPLETE
behavioral cap by that singleton. No opponent clock contracts here. -/
theorem quittingBehaviorEvaluatedDeviationPayoffCap_alwaysContinue_le_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (evaluation : WithTop ℕ → ℝ)
    (hzero : ∀ clock, 0 ≤ evaluation clock) (hone : ∀ clock, evaluation clock ≤ 1)
    (who : ι) (hsolo : 0 ≤ reward (quittingSingletonTerminal who) who) :
    letI : Nonempty ι := ⟨who⟩
    quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
      (quittingAlwaysContinueProfile reward) who ≤ reward (quittingSingletonTerminal who) who := by
  let : Nonempty ι := ⟨who⟩
  rw [quittingBehaviorEvaluatedDeviationPayoffCap_eq_pureTime reward evaluation hzero hone]
  apply csSup_le
  · exact ⟨_, ⟨none, rfl⟩⟩
  · rintro _ ⟨choice, rfl⟩
    change quittingStoppingLawEvaluatedPayoff reward evaluation
      (Function.update (quittingBehaviorStoppingLaws reward
        (quittingAlwaysContinueProfile reward)) who (PMF.pure choice)) who ≤
      reward (quittingSingletonTerminal who) who
    rw [quittingStoppingLawEvaluatedPayoff_alwaysContinue_pureTime_eq]
    cases choice with
    | none => exact hsolo
    | some time =>
        exact (mul_le_mul_of_nonneg_right (hone (time : WithTop ℕ)) hsolo).trans_eq
          (one_mul _)

end GameTheory

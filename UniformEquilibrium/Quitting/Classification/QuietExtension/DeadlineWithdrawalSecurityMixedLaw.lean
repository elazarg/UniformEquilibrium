import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalSecurityEvaluatedPlan
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalMixedLaw

/-!
# Disjoint advancement and fresh security restart

Only a tied finite source/deadline can restart. On that event, replace the
existing private mixture's withdrawn Never outcome by a fresh private plan.
The resulting coefficient remains the maximum of the two row weights.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability

/-- Withdraw a finite atom into a fresh law, keeping all other clocks. -/
def deadlineSecurityAtomRestartLaw
    (restart : ℕ → PMF (Option ℕ)) (source deadline : Option ℕ) : PMF (Option ℕ) :=
  match deadline with
  | none => PMF.pure source
  | some time => if source = some time then restart time else PMF.pure source

/-- The max-weight private mixture, with its tied withdrawal branch replaced
by fresh restart randomness independent of the source and opponent clocks. -/
def deadlineSecurityMixedPrivateClockLaw
    (restart : ℕ → PMF (Option ℕ)) (source deadline : Option ℕ)
    (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) : PMF (Option ℕ) :=
  match deadline with
  | none => deadlineMixedPrivateClockLaw source none
      advanceWeight withdrawalWeight hadvance hwithdrawal
  | some time =>
      if source = some time then
        (deadlineMixedPrivateClockLaw source (some time)
          advanceWeight withdrawalWeight hadvance hwithdrawal).bind fun clock =>
            if clock = none then restart time else PMF.pure clock
      else deadlineMixedPrivateClockLaw source (some time)
        advanceWeight withdrawalWeight hadvance hwithdrawal

/-- Exact bounded one-site identity, including zero weights and Never
deadlines. No security estimate or payoff-cap premise enters the identity. -/
theorem deadlineSecurityMixedPrivateClockLaw_gain_identity
    (restart : ℕ → PMF (Option ℕ)) (source deadline : Option ℕ)
    (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight)
    (value : Option ℕ → ℝ) {bound : ℝ} (hvalue : ∀ clock, |value clock| ≤ bound) :
    max advanceWeight withdrawalWeight *
        (expect (deadlineSecurityMixedPrivateClockLaw restart source deadline
          advanceWeight withdrawalWeight hadvance hwithdrawal) value - value source) =
      advanceWeight * (value (cappedStoppingClock source deadline) - value source) +
        withdrawalWeight *
          (expect (deadlineSecurityAtomRestartLaw restart source deadline) value -
            value source) := by
  cases deadline with
  | none =>
      simp [deadlineSecurityMixedPrivateClockLaw, deadlineSecurityAtomRestartLaw,
        deadlineMixedPrivateClockLaw_none, cappedStoppingClock, quittingStoppingTimeValue]
  | some time =>
      by_cases htie : source = some time
      · subst source
        let transformed : Option ℕ → ℝ := fun clock =>
          if clock = none then expect (restart time) value else value clock
        have hexpect : expect (deadlineSecurityMixedPrivateClockLaw restart
            (some time) (some time) advanceWeight withdrawalWeight hadvance hwithdrawal)
            value = expect (deadlineMixedPrivateClockLaw (some time) (some time)
              advanceWeight withdrawalWeight hadvance hwithdrawal) transformed := by
          simp only [deadlineSecurityMixedPrivateClockLaw, ↓reduceIte]
          rw [expect_bind_of_bounded _ _ value hvalue]
          apply congrArg (expect _)
          funext clock
          by_cases hnone : clock = none <;> simp [transformed, hnone]
        rw [hexpect]
        have h := deadlineMixedPrivateClockLaw_gain_identity
          (some time) (some time) advanceWeight withdrawalWeight hadvance hwithdrawal transformed
        simpa [transformed, deadlineSecurityAtomRestartLaw, cappedStoppingClock,
          deadlineWithdrawnClock, quittingStoppingTimeValue] using h
      · have hwithdraw := deadlineWithdrawnClock_some_ne source time htie
        simpa [deadlineSecurityMixedPrivateClockLaw, deadlineSecurityAtomRestartLaw,
          htie, hwithdraw] using deadlineMixedPrivateClockLaw_gain_identity
            source (some time) advanceWeight withdrawalWeight hadvance hwithdrawal value

/-- One complete legal replacement samples only the owner's source clock,
the independent outsider replica, and the appropriate operation randomness. -/
def deadlineSecurityMixedPrivateReplacementLaw
    (restart : ℕ → PMF (Option ℕ)) (sourceLaw outsideLaw : PMF (Option ℕ))
    (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) : PMF (Option ℕ) :=
  sourceLaw.bind fun source => outsideLaw.bind fun deadline =>
    deadlineSecurityMixedPrivateClockLaw restart source deadline
      advanceWeight withdrawalWeight hadvance hwithdrawal

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The actual raw-table plan family used by the restart kernel. It is
selected before the evaluation and all hidden opponent clocks. -/
def deadlineSecurityEvaluatedRestartFamily
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (deadline : ℕ) : PMF (Option ℕ) :=
  Classical.choose (exists_deadlineWithdrawalSecurityEvaluatedPlan reward i deadline)

theorem deadlineSecurityEvaluatedRestartFamily_before
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (deadline time : ℕ) (htime : time ≤ deadline) :
    deadlineSecurityEvaluatedRestartFamily reward i deadline (some time) = 0 :=
  (Classical.choose_spec (exists_deadlineWithdrawalSecurityEvaluatedPlan
    reward i deadline)).1 time htime

theorem deadlineSecurityEvaluatedRestartFamily_floor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (deadline : ℕ) (evaluation : WithTop ℕ → ℝ)
    (hnonneg : ∀ time, 0 ≤ evaluation time) (hantitone : Antitone evaluation)
    (opponents : ι → Option ℕ) (hown : opponents i = none)
    (hfuture : ∀ j, (deadline : WithTop ℕ) < quittingStoppingTimeValue (opponents j)) :
    evaluation deadline * min (deadlineWithdrawalSecurityFloor reward i) 0 ≤
      expect (deadlineSecurityEvaluatedRestartFamily reward i deadline)
        (fun clock => quittingPureClockEvaluatedPayoff reward evaluation
          (Function.update (quietParentClocks opponents) (some i) clock) (some i)) :=
  (Classical.choose_spec (exists_deadlineWithdrawalSecurityEvaluatedPlan
    reward i deadline)).2 evaluation hnonneg hantitone opponents hown hfuture

end GameTheory

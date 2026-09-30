import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalMixedRestartCore
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalSecurityMixedBehavioral

/-! # Evaluated security specialization of the shared private mixed-restart core -/

noncomputable section

namespace GameTheory

open _root_.Math _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
/-- The reward-selected evaluated restart delegates to the shared private-law core. -/
theorem deadlineSecurityMixedPrivateReplacement_childProduct
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (i : ι) (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) :
    (pmfPi childLaws).bind (fun times =>
        outsideLaw.bind fun deadline =>
          (deadlineSecurityMixedPrivateClockLaw
            (deadlineSecurityEvaluatedRestartFamily reward i) (times i) deadline
            advanceWeight withdrawalWeight hadvance hwithdrawal).map
              fun newClock => Function.update times i newClock) =
      pmfPi (Function.update childLaws i
        (deadlineSecurityMixedPrivateReplacementLaw
          (deadlineSecurityEvaluatedRestartFamily reward i) (childLaws i) outsideLaw
          advanceWeight withdrawalWeight hadvance hwithdrawal)) := by
  exact deadlineSecurityMixedPrivateReplacement_childProductWithRestart
    (deadlineSecurityEvaluatedRestartFamily reward i)
      childLaws outsideLaw i advanceWeight withdrawalWeight hadvance hwithdrawal

omit [Nonempty ι] in
/-- The reward-selected evaluated restart delegates to the shared private-law core. -/
theorem deadlineSecurityMixedPrivateReplacement_parentProduct
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (i : ι) (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) :
    ((pmfPi childLaws).bind (fun times =>
        outsideLaw.bind fun deadline =>
          (deadlineSecurityMixedPrivateClockLaw
            (deadlineSecurityEvaluatedRestartFamily reward i) (times i) deadline
            advanceWeight withdrawalWeight hadvance hwithdrawal).map
              fun newClock => Function.update times i newClock)).map
        quietParentClocks =
      pmfPi (deadlineSecurityMixedChildParentStoppingLaws reward childLaws outsideLaw i
        advanceWeight withdrawalWeight hadvance hwithdrawal) := by
  exact deadlineSecurityMixedPrivateReplacement_parentProductWithRestart
    (deadlineSecurityEvaluatedRestartFamily reward i)
      childLaws outsideLaw i advanceWeight withdrawalWeight hadvance hwithdrawal

omit [Nonempty ι] in
/-- The reward-selected evaluated restart delegates to the shared private-law core. -/
theorem deadlineSecurityMixedPrivateReplacement_parentMarginal
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (i : ι) (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) :
    (cappedClockIndependentSample childLaws outsideLaw).bind
        (fun sample =>
          (deadlineSecurityMixedPrivateClockLaw
            (deadlineSecurityEvaluatedRestartFamily reward i) (sample.1 i) sample.2
            advanceWeight withdrawalWeight hadvance hwithdrawal).map
              fun newClock => deadlinePrivateChildClocks sample.1 i newClock) =
      pmfPi (deadlineSecurityMixedChildParentStoppingLaws reward childLaws outsideLaw i
        advanceWeight withdrawalWeight hadvance hwithdrawal) := by
  exact deadlineSecurityMixedPrivateReplacement_parentMarginalWithRestart
    (deadlineSecurityEvaluatedRestartFamily reward i)
      childLaws outsideLaw i advanceWeight withdrawalWeight hadvance hwithdrawal

/-- The reward-selected evaluated restart delegates to the shared private-law core. -/
theorem deadlineSecurityMixedPrivateReplacement_evaluatedPayoff
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (i : ι) (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) :
    _root_.Math.Probability.expect
      ((cappedClockIndependentSample childLaws outsideLaw).bind
        (fun sample =>
          (deadlineSecurityMixedPrivateClockLaw
            (deadlineSecurityEvaluatedRestartFamily reward i) (sample.1 i) sample.2
            advanceWeight withdrawalWeight hadvance hwithdrawal).map
              fun newClock => deadlinePrivateChildClocks sample.1 i newClock))
        (fun clocks => quittingPureClockEvaluatedPayoff reward evaluation
          clocks (some i)) =
      quittingStoppingLawEvaluatedPayoff reward evaluation
        (deadlineSecurityMixedChildParentStoppingLaws reward childLaws outsideLaw i
          advanceWeight withdrawalWeight hadvance hwithdrawal) (some i) := by
  exact deadlineSecurityMixedPrivateReplacement_evaluatedPayoffWithRestart reward
    (deadlineSecurityEvaluatedRestartFamily reward i)
      evaluation childLaws outsideLaw i advanceWeight withdrawalWeight hadvance hwithdrawal

/-- The reward-selected evaluated restart delegates to the shared private-law core. -/
theorem expect_deadlineSecurityMixedPrivateClockLaw_payoff_eq_stoppingLaw
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (i : ι) (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) :
    _root_.Math.Probability.expect
        (cappedClockIndependentSample childLaws outsideLaw)
        (fun sample => _root_.Math.Probability.expect
          (deadlineSecurityMixedPrivateClockLaw
            (deadlineSecurityEvaluatedRestartFamily reward i) (sample.1 i) sample.2
            advanceWeight withdrawalWeight hadvance hwithdrawal)
          (fun newClock => quittingPureClockEvaluatedPayoff reward evaluation
            (deadlinePrivateChildClocks sample.1 i newClock) (some i))) =
      quittingStoppingLawEvaluatedPayoff reward evaluation
        (deadlineSecurityMixedChildParentStoppingLaws reward childLaws outsideLaw i
          advanceWeight withdrawalWeight hadvance hwithdrawal) (some i) := by
  exact expect_deadlineSecurityMixedPrivateClockLaw_payoff_eq_stoppingLawWithRestart reward
    (deadlineSecurityEvaluatedRestartFamily reward i)
      evaluation evaluation_nonneg evaluation_antitone childLaws outsideLaw i
      advanceWeight withdrawalWeight hadvance hwithdrawal

end GameTheory

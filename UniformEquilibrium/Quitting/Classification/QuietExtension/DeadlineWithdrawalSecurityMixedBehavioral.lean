import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalMixedRestartCore

/-! # Evaluated security specialization of the shared private mixed-restart core -/

noncomputable section

namespace GameTheory

open _root_.Math _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Evaluated security specialization of the shared mixed-restart interface. -/
def deadlineSecurityActualEvaluatedChildGain
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (times : ι → Option ℕ) (deadline : Option ℕ) (i : ι) : ℝ :=
  expect (deadlineSecurityAtomRestartLaw (deadlineSecurityEvaluatedRestartFamily reward i)
      (times i) deadline)
    (fun clock => quittingPureClockEvaluatedPayoff reward evaluation
      (deadlinePrivateChildClocks times i clock) (some i)) -
    quittingPureClockEvaluatedPayoff reward evaluation (quietParentClocks times) (some i)

/-- The reward-selected evaluated restart delegates to the shared private-law core. -/
theorem deadlineSecurityMixedPrivateClockLaw_evaluatedGain_identity
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (hnonneg : ∀ time, 0 ≤ evaluation time) (hantitone : Antitone evaluation)
    (times : ι → Option ℕ) (deadline : Option ℕ) (i : ι)
    (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) :
    max advanceWeight withdrawalWeight *
        (expect (deadlineSecurityMixedPrivateClockLaw
            (deadlineSecurityEvaluatedRestartFamily reward i) (times i) deadline
            advanceWeight withdrawalWeight hadvance hwithdrawal)
          (fun clock => quittingPureClockEvaluatedPayoff reward evaluation
            (deadlinePrivateChildClocks times i clock) (some i)) -
          quittingPureClockEvaluatedPayoff reward evaluation (quietParentClocks times) (some i)) =
      advanceWeight * cappedClockActualEvaluatedChildGain reward evaluation times deadline i +
        withdrawalWeight * deadlineSecurityActualEvaluatedChildGain
          reward evaluation times deadline i := by
  exact deadlineSecurityMixedPrivateClockLaw_evaluatedGain_identityWithRestart reward
    (deadlineSecurityEvaluatedRestartFamily reward i)
      evaluation hnonneg hantitone times deadline i
      advanceWeight withdrawalWeight hadvance hwithdrawal

/-- Evaluated security specialization of the shared mixed-restart interface. -/
def deadlineSecurityMixedChildParentStoppingLaws
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (i : ι) (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) :
    Option ι → PMF (Option ℕ) :=
  Function.update (quietParentStoppingLaws childLaws) (some i)
    (deadlineSecurityMixedPrivateReplacementLaw
      (deadlineSecurityEvaluatedRestartFamily reward i) (childLaws i) outsideLaw
      advanceWeight withdrawalWeight hadvance hwithdrawal)

/-- The reward-selected evaluated restart delegates to the shared private-law core. -/
theorem deadlineSecurityMixedChild_payoff_le_behaviorDeviationCap
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (hnonneg : ∀ time, 0 ≤ evaluation time) (hantitone : Antitone evaluation)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (i : ι) (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) :
    quittingStoppingLawEvaluatedPayoff reward evaluation
        (deadlineSecurityMixedChildParentStoppingLaws reward childLaws outsideLaw i
          advanceWeight withdrawalWeight hadvance hwithdrawal) (some i) ≤
      quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
        (quittingStoppingLawProfile reward (quietParentStoppingLaws childLaws)) (some i) := by
  exact deadlineSecurityMixedChild_payoff_le_behaviorDeviationCapWithRestart reward
    (deadlineSecurityEvaluatedRestartFamily reward i)
      evaluation hnonneg hantitone childLaws outsideLaw i
      advanceWeight withdrawalWeight hadvance hwithdrawal

end GameTheory

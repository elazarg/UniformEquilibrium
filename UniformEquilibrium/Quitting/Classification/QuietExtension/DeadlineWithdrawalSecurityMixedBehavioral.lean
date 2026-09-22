import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalSecurityMixedLaw
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockEvaluatedActualPayoffAdapter

/-!
# Actual private security-mixture responses

The fresh plan is chosen from the raw reward table. This module identifies
the exact one-site evaluated gain and transports its independent replacement
law to the unrestricted behavioral cap.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Actual averaged gain from withdrawing just the deadline atom into the
reward-table security plan. -/
def deadlineSecurityActualEvaluatedChildGain
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (times : ι → Option ℕ) (deadline : Option ℕ) (i : ι) : ℝ :=
  expect (deadlineSecurityAtomRestartLaw (deadlineSecurityEvaluatedRestartFamily reward i)
      (times i) deadline)
    (fun clock => quittingPureClockEvaluatedPayoff reward evaluation
      (deadlinePrivateChildClocks times i clock) (some i)) -
    quittingPureClockEvaluatedPayoff reward evaluation (quietParentClocks times) (some i)

/-- The exact max-weight identity applied to the actual evaluated quitting
payoff; the restart term is averaged over the fresh private plan. -/
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
  have hbase : deadlinePrivateChildClocks times i (times i) = quietParentClocks times := by
    funext player
    cases player with
    | none => rfl
    | some j => by_cases h : j = i <;> simp [deadlinePrivateChildClocks, quietParentClocks, h]
  have hcap : deadlinePrivateChildClocks times i (cappedStoppingClock (times i) deadline) =
      cappedChildParentClocks times deadline i := by
    funext player
    cases player with
    | none => rfl
    | some j => by_cases h : j = i <;>
        simp [deadlinePrivateChildClocks, cappedChildParentClocks, h]
  simpa only [hbase, hcap, cappedClockActualEvaluatedChildGain,
    deadlineSecurityActualEvaluatedChildGain] using
    deadlineSecurityMixedPrivateClockLaw_gain_identity
      (deadlineSecurityEvaluatedRestartFamily reward i) (times i) deadline
      advanceWeight withdrawalWeight hadvance hwithdrawal
      (fun clock => quittingPureClockEvaluatedPayoff reward evaluation
        (deadlinePrivateChildClocks times i clock) (some i))
      (fun clock => abs_quittingPureClockEvaluatedPayoff_le
        reward evaluation hnonneg hantitone _ _)

/-- Quiet independent laws with one child replaced by its actual
reward-table-selected security mixture. -/
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

/-- The actual private mixture is a legal complete behavioral replacement,
so its evaluated payoff is below the unrestricted behavioral cap. -/
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
  rw [← quittingBehaviorEvaluatedPayoff_stoppingLawProfile]
  let quietProfile := quittingStoppingLawProfile reward (quietParentStoppingLaws childLaws)
  let deviation := quittingStoppingLawBehaviorStrategy reward (some i)
    (deadlineSecurityMixedPrivateReplacementLaw
      (deadlineSecurityEvaluatedRestartFamily reward i) (childLaws i) outsideLaw
      advanceWeight withdrawalWeight hadvance hwithdrawal)
  have hprofile : quittingStoppingLawProfile reward
      (deadlineSecurityMixedChildParentStoppingLaws reward childLaws outsideLaw i
        advanceWeight withdrawalWeight hadvance hwithdrawal) =
      Function.update quietProfile (some i) deviation := by
    funext player
    by_cases hp : player = some i
    · subst player
      simp [deadlineSecurityMixedChildParentStoppingLaws, quietProfile, deviation,
        quittingStoppingLawProfile]
    · simp [deadlineSecurityMixedChildParentStoppingLaws, quietProfile, deviation,
        quittingStoppingLawProfile, hp]
  rw [hprofile]
  unfold quittingBehaviorEvaluatedDeviationPayoffCap
  apply le_csSup
    (bddAbove_range_quittingBehaviorEvaluatedPayoff_update reward evaluation
      hnonneg hantitone quietProfile (some i))
  exact ⟨deviation, rfl⟩

end GameTheory

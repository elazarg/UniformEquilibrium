import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalDomination
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockEvaluatedActualPayoffAdapter

/-!
# Legal mixed deadline withdrawal as a behavioral replacement

The source/deadline/operation mixture produces one child's independent
complete stopping law. Its payoff is below the unrestricted behavioral cap
in the quiet parent profile. This is the legal-response half of the D bridge;
the coupled expectation must still be identified with this product marginal.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Quiet parent laws with exactly one child independently replaced by its
private deadline-mixture law. -/
def deadlineMixedChildParentStoppingLaws
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (i : ι) (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) :
    Option ι → PMF (Option ℕ) :=
  Function.update (quietParentStoppingLaws childLaws) (some i)
    (deadlineMixedPrivateReplacementLaw (childLaws i) outsideLaw
      advanceWeight withdrawalWeight hadvance hwithdrawal)

/-- The actual mixed child stopping-law payoff is one legal behavioral
replacement payoff, so it is below the full behavioral deviation envelope. -/
theorem deadlineMixedChild_stoppingLawEvaluatedPayoff_le_behaviorDeviationCap
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (i : ι) (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) :
    quittingStoppingLawEvaluatedPayoff reward evaluation
        (deadlineMixedChildParentStoppingLaws childLaws outsideLaw i
          advanceWeight withdrawalWeight hadvance hwithdrawal) (some i) ≤
      quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
        (quittingStoppingLawProfile reward
          (quietParentStoppingLaws childLaws)) (some i) := by
  rw [← quittingBehaviorEvaluatedPayoff_stoppingLawProfile]
  let quietProfile := quittingStoppingLawProfile reward
    (quietParentStoppingLaws childLaws)
  let deviation := quittingStoppingLawBehaviorStrategy reward (some i)
    (deadlineMixedPrivateReplacementLaw (childLaws i) outsideLaw
      advanceWeight withdrawalWeight hadvance hwithdrawal)
  have hprofile : quittingStoppingLawProfile reward
      (deadlineMixedChildParentStoppingLaws childLaws outsideLaw i
        advanceWeight withdrawalWeight hadvance hwithdrawal) =
      Function.update quietProfile (some i) deviation := by
    funext player
    by_cases hp : player = some i
    · subst player
      simp [deadlineMixedChildParentStoppingLaws, quietProfile, deviation,
        quittingStoppingLawProfile]
    · simp [deadlineMixedChildParentStoppingLaws, quietProfile, deviation,
        quittingStoppingLawProfile, hp]
  rw [hprofile]
  unfold quittingBehaviorEvaluatedDeviationPayoffCap
  apply le_csSup
    (bddAbove_range_quittingBehaviorEvaluatedPayoff_update reward evaluation
      evaluation_nonneg evaluation_antitone quietProfile (some i))
  exact ⟨deviation, rfl⟩

end GameTheory

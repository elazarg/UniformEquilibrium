import UniformEquilibrium.Quitting.Paths.ActualExactPrefixBlock
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeRectangle

/-! # Payoff-difference atoms under literal reverse prefixes -/

noncomputable section
namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A common literal prefix transports an old payoff-difference atom by
exactly the probability of entering the old suffix.  Fresh prefix outcomes
cancel because the two executable profiles have the same literal prefix. -/
theorem quittingTerminalPayoffDifferenceAtom_literalRootStack_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (first second : (quittingGame reward).BehaviorProfile)
    (observer : ι) (outcome : QuittingTerminalOutcome ι) :
    quittingTerminalPayoffDifferenceAtom reward
          (quittingLiteralRootStackProfile reward roots first)
          (quittingLiteralRootStackProfile reward roots second)
          observer outcome =
      quittingLiteralRootStackJointSurvival roots *
        quittingTerminalPayoffDifferenceAtom reward first second observer
          outcome := by
  unfold quittingTerminalPayoffDifferenceAtom
  induction roots with
  | nil => simp [quittingLiteralRootStackJointSurvival]
  | cons root roots ih =>
      simp only [quittingLiteralRootStackProfile_cons,
        quittingTerminalOutcomeMass_rootThenContinuation,
        quittingLiteralRootStackJointSurvival, List.map_cons,
        List.prod_cons] at ih ⊢
      cases outcome <;>
        linear_combination (quittingStationaryContinueMass root) * ih

/-- Actual nested reverse prefixes give the literal marked-atom transport,
with the executable endpoints identified as the supplied actual profiles. -/
theorem quittingTerminalPayoffDifferenceAtom_actualReversePrefix_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool)
    (hnested : ∀ n, profiles (n + 1) =
      quittingRootThenContinuationProfile reward (roots n) (profiles n))
    (alternative : (quittingGame reward).BehaviorProfile)
    (observer : ι) (outcome : QuittingTerminalOutcome ι) (depth : ℕ) :
    quittingTerminalPayoffDifferenceAtom reward (profiles depth)
          (quittingLiteralRootStackProfile reward
            (quittingReversePrefixRootStack roots depth) alternative)
          observer outcome =
      quittingLiteralRootStackJointSurvival
          (quittingReversePrefixRootStack roots depth) *
        quittingTerminalPayoffDifferenceAtom reward (profiles 0) alternative
          observer outcome := by
  rw [← quittingReversePrefixProfile_eq_of_nested
    reward profiles roots hnested depth]
  exact quittingTerminalPayoffDifferenceAtom_literalRootStack_eq
    reward (quittingReversePrefixRootStack roots depth) (profiles 0)
      alternative observer outcome

/-- A nonnegative old marked atom retains the corresponding uniform fraction
of its reach through every actual reverse prefix with a survival floor. -/
theorem quittingTerminalPayoffDifferenceAtom_actualReversePrefix_ge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool)
    (hnested : ∀ n, profiles (n + 1) =
      quittingRootThenContinuationProfile reward (roots n) (profiles n))
    (alternative : (quittingGame reward).BehaviorProfile)
    (observer : ι) (outcome : QuittingTerminalOutcome ι)
    {survivalFloor : ℝ}
    (hsurvival : ∀ depth, survivalFloor ≤
      quittingLiteralRootStackJointSurvival
        (quittingReversePrefixRootStack roots depth))
    (hatom : 0 ≤ quittingTerminalPayoffDifferenceAtom reward
      (profiles 0) alternative observer outcome) (depth : ℕ) :
    survivalFloor * quittingTerminalPayoffDifferenceAtom reward
          (profiles 0) alternative observer outcome ≤
      quittingTerminalPayoffDifferenceAtom reward (profiles depth)
        (quittingLiteralRootStackProfile reward
          (quittingReversePrefixRootStack roots depth) alternative)
        observer outcome := by
  rw [quittingTerminalPayoffDifferenceAtom_actualReversePrefix_eq
    reward profiles roots hnested alternative observer outcome depth]
  exact mul_le_mul_of_nonneg_right (hsurvival depth) hatom

end GameTheory

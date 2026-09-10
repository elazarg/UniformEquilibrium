import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockParentLawPushforward
import UniformEquilibrium.Quitting.Paths.StoppingLawOperationalDistance
import UniformEquilibrium.Quitting.Root.FirstBranch

/-!
# Actual payoff adapter for capped-clock parent laws
-/

noncomputable section

namespace GameTheory

open Math Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private theorem quittingStoppingLawExpectedPayoff_eq_expect_pmfPi
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (laws : Option ι → PMF (Option ℕ)) (who : Option ι) :
    quittingStoppingLawExpectedPayoff reward laws who =
    Math.Probability.expect (pmfPi laws)
      (fun clocks => quittingPureClockTerminalPayoff reward clocks who) := by
  rw [quittingStoppingLawExpectedPayoff,
    quittingIndependentTerminalOutcomeLaw, Math.Probability.expect_map]
  apply congrArg (Math.Probability.expect (pmfPi laws))
  funext clocks
  unfold quittingPureClockTerminalPayoff
  cases h : quittingFirstStoppingOutcome clocks <;>
    simp [quittingTerminalOutcomeReward]

/-- The source coupling's literal outsider outcome is the canonical expected
payoff of the parent law in which the outsider uses `outsideLaw`. -/
theorem expect_parentSource_outside_eq_stoppingLawExpectedPayoff
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ)) :
    Math.Probability.expect
      (pmfPi (cappedClockParentSourceLaws childLaws outsideLaw))
        (fun clocks => quittingPureClockTerminalPayoff reward
          (outsideDeadlineClocks (fun i => clocks (some i)) (clocks none)) none) =
      quittingStoppingLawExpectedPayoff reward
        (cappedClockParentSourceLaws childLaws outsideLaw) none := by
  rw [quittingStoppingLawExpectedPayoff_eq_expect_pmfPi]
  apply congrArg (Math.Probability.expect (pmfPi
    (cappedClockParentSourceLaws childLaws outsideLaw)))
  funext clocks
  congr 2
  funext player
  cases player <;> rfl

/-- The literal quiet baseline in the source coupling is the canonical parent
stopping-law payoff of the quiet lift. -/
theorem expect_parentSource_quiet_eq_stoppingLawExpectedPayoff
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (who : Option ι) :
    Math.Probability.expect
      (pmfPi (cappedClockParentSourceLaws childLaws outsideLaw))
        (fun clocks => quittingPureClockTerminalPayoff reward
          (quietParentClocks fun i => clocks (some i)) who) =
      quittingStoppingLawExpectedPayoff reward
        (quietParentStoppingLaws childLaws) who := by
  rw [quittingStoppingLawExpectedPayoff_eq_expect_pmfPi]
  rw [← map_pmfPi_cappedClockParentSourceLaws_quiet childLaws outsideLaw,
    Math.Probability.expect_map]

/-- The literal capped-child outcome in the common coupling is the canonical
expected payoff of the actual reconstructed capped child law. -/
theorem expect_parentSource_cappedChild_eq_stoppingLawExpectedPayoff
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ)) (i : ι) :
    Math.Probability.expect
      (pmfPi (cappedClockParentSourceLaws childLaws outsideLaw))
        (fun clocks => quittingPureClockTerminalPayoff reward
          (cappedChildParentClocks (fun j => clocks (some j))
            (clocks none) i) (some i)) =
      quittingStoppingLawExpectedPayoff reward
        (cappedChildParentStoppingLaws childLaws outsideLaw i) (some i) := by
  rw [quittingStoppingLawExpectedPayoff_eq_expect_pmfPi]
  rw [← map_pmfPi_cappedClockParentSourceLaws_cappedChild
    childLaws outsideLaw i, Math.Probability.expect_map]

/-- Each capped-child expectation is the payoff of an actual unrestricted
behavioral deviation from the reconstructed quiet parent profile and hence is
bounded by the full behavioral deviation cap. -/
theorem cappedChild_stoppingLawExpectedPayoff_le_behaviorDeviationCap
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ)) (i : ι) :
    quittingStoppingLawExpectedPayoff reward
        (cappedChildParentStoppingLaws childLaws outsideLaw i) (some i) ≤
      quittingBehaviorDeviationPayoffCap reward
        (quittingStoppingLawProfile reward
          (quietParentStoppingLaws childLaws)) (some i) := by
  rw [← quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff]
  let quietProfile := quittingStoppingLawProfile reward
    (quietParentStoppingLaws childLaws)
  let deviation := quittingStoppingLawBehaviorStrategy reward (some i)
    (cappedClockStoppingLaw (childLaws i) outsideLaw)
  have hprofile : quittingStoppingLawProfile reward
      (cappedChildParentStoppingLaws childLaws outsideLaw i) =
      Function.update quietProfile (some i) deviation := by
    funext player
    by_cases hp : player = some i
    · subst player
      simp [cappedChildParentStoppingLaws, quietProfile, deviation,
        quittingStoppingLawProfile]
    · simp [cappedChildParentStoppingLaws, quietProfile, deviation,
        quittingStoppingLawProfile, hp]
  rw [hprofile]
  unfold quittingBehaviorDeviationPayoffCap
  apply le_csSup
    (bddAbove_range_quittingTerminalPayoff_update reward quietProfile (some i))
  exact ⟨deviation, rfl⟩

end GameTheory

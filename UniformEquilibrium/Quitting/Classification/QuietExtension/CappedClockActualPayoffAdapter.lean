import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockEvaluatedActualPayoffAdapter
import UniformEquilibrium.Quitting.Root.FirstBranch

/-!
# Actual payoff adapter for capped-clock parent laws
-/

noncomputable section

namespace GameTheory

open _root_.Math _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] in
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
  simpa [quittingPureClockEvaluatedPayoff_terminalEvaluation,
    quittingStoppingLawEvaluatedPayoff_terminalEvaluation] using
      (expect_parentSource_outside_eq_stoppingLawEvaluatedPayoff
        reward quittingTerminalEvaluation childLaws outsideLaw)

omit [DecidableEq ι] in
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
  simpa [quittingPureClockEvaluatedPayoff_terminalEvaluation,
    quittingStoppingLawEvaluatedPayoff_terminalEvaluation] using
      (expect_parentSource_quiet_eq_stoppingLawEvaluatedPayoff
        reward quittingTerminalEvaluation childLaws outsideLaw who)

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
  simpa [quittingPureClockEvaluatedPayoff_terminalEvaluation,
    quittingStoppingLawEvaluatedPayoff_terminalEvaluation] using
      (expect_parentSource_cappedChild_eq_stoppingLawEvaluatedPayoff
        reward quittingTerminalEvaluation childLaws outsideLaw i)

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
  simpa [quittingStoppingLawEvaluatedPayoff_terminalEvaluation,
    quittingBehaviorEvaluatedDeviationPayoffCap_terminalEvaluation] using
      (cappedChild_stoppingLawEvaluatedPayoff_le_behaviorDeviationCap
        reward quittingTerminalEvaluation quittingTerminalEvaluation_nonneg
          quittingTerminalEvaluation_antitone childLaws outsideLaw i)

end GameTheory

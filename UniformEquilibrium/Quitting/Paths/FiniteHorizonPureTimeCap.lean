import UniformEquilibrium.Quitting.Paths.FiniteHorizonStoppingLawPayoff
import UniformEquilibrium.Quitting.Paths.EvaluatedPureTimeCap
import UniformEquilibrium.Quitting.ControllerTester.FiniteHorizonExploitability

/-! # Full finite-horizon caps from actual pure-time replacements -/

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.PMFProduct Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Finite stage-average and evaluated full behavioral caps are literally equal. -/
theorem quittingFiniteHorizonDeviationCap_eq_evaluatedCap
    (reward : {A : Finset ι // A.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (horizon : ℕ) (who : ι) :
    quittingFiniteHorizonDeviationCap reward profile horizon who =
      quittingBehaviorEvaluatedDeviationPayoffCap reward
        (quittingFiniteHorizonEvaluation horizon) profile who := by
  unfold quittingFiniteHorizonDeviationCap quittingBehaviorEvaluatedDeviationPayoffCap
  apply congrArg sSup
  apply congrArg Set.range
  funext deviation
  exact quittingFiniteAveragePayoff_eq_stoppingLawEvaluatedPayoff
    reward (Function.update profile who deviation) horizon who

/-- Every actual replacement payoff averages exact deterministic replacement payoffs. -/
theorem quittingFiniteAveragePayoff_update_eq_expect_pureTime
    (reward : {A : Finset ι // A.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (horizon : ℕ) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    (quittingGame reward).finiteAveragePayoff none horizon
        (Function.update profile who deviation) who =
      expect (quittingBehaviorStoppingLaw reward deviation) (fun choice =>
        quittingStoppingLawEvaluatedPayoff reward (quittingFiniteHorizonEvaluation horizon)
          (Function.update (quittingBehaviorStoppingLaws reward profile) who
            (PMF.pure choice)) who) := by
  rw [quittingFiniteAveragePayoff_eq_stoppingLawEvaluatedPayoff]
  exact quittingBehaviorEvaluatedPayoff_update_eq_expect_pureTime reward
    (quittingFiniteHorizonEvaluation horizon) (quittingFiniteHorizonEvaluation_nonneg horizon)
    (quittingFiniteHorizonEvaluation_le_one horizon) profile who deviation

/-- Exact horizon cap: deterministic dates and Never exhaust the unrestricted envelope.
The pure law is realized by its canonical actual behavioral strategy. -/
theorem quittingFiniteHorizonDeviationCap_eq_pureTime
    (reward : {A : Finset ι // A.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (horizon : ℕ) (who : ι) :
    quittingFiniteHorizonDeviationCap reward profile horizon who =
      sSup (Set.range fun choice : Option ℕ =>
        quittingStoppingLawEvaluatedPayoff reward (quittingFiniteHorizonEvaluation horizon)
          (Function.update (quittingBehaviorStoppingLaws reward profile) who
            (PMF.pure choice)) who) := by
  rw [quittingFiniteHorizonDeviationCap_eq_evaluatedCap]
  exact quittingBehaviorEvaluatedDeviationPayoffCap_eq_pureTime reward
    (quittingFiniteHorizonEvaluation horizon) (quittingFiniteHorizonEvaluation_nonneg horizon)
    (quittingFiniteHorizonEvaluation_le_one horizon) profile who

end GameTheory

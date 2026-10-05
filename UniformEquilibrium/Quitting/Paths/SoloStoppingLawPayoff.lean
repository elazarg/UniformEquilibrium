import UniformEquilibrium.Quitting.Paths.StoppingLawOperationalDistance
import UniformEquilibrium.Quitting.Root.AlwaysContinuePureTimeReplies
import MathUE.ProbabilityMassFunction.IndicatorExpectation

/-! # Actual one-active-player stopping-law payoff

All other players have the literal Never law. Every payoff observer receives
the active player's singleton reward times its complete finite-quit probability.
The active law may have infinite support and a positive Never atom.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Only one actual marginal can quit: its finite probability multiplies
the literal singleton reward in every observer coordinate. -/
theorem quittingTerminalPayoff_soloStoppingLaw_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (owner observer : ι)
    (hothers : ∀ who, who ≠ owner →
      quittingBehaviorStoppingLaw reward (profile who) = PMF.pure none) :
    quittingTerminalPayoff reward profile observer =
      (1 - (quittingBehaviorStoppingLaw reward (profile owner) none).toReal) *
        reward (quittingSingletonTerminal owner) observer := by
  let solo := Function.update (quittingAlwaysContinueProfile reward) owner (profile owner)
  have hlaws : quittingBehaviorStoppingLaws reward solo =
      quittingBehaviorStoppingLaws reward profile := by
    funext who
    by_cases hwho : who = owner
    · subst who
      simp [solo, quittingBehaviorStoppingLaws]
    · change quittingBehaviorStoppingLaw reward (solo who) = _
      rw [show solo who = quittingPureTimeBehaviorStrategy reward who none by
        simp only [solo, Function.update_of_ne hwho]; rfl,
        quittingBehaviorStoppingLaw_pureTime_never]
      exact (hothers who hwho).symm
  rw [← quittingTerminalPayoff_eq_of_behaviorStoppingLaws_eq reward solo profile hlaws,
    quittingTerminalPayoff_eq_expect_behaviorStoppingLaw_pureTime reward solo owner observer]
  simp only [solo, Function.update_self, Function.update_idem]
  have hchoice (choice : Option ℕ) : quittingTerminalPayoff reward
      (Function.update (quittingAlwaysContinueProfile reward) owner
        (quittingPureTimeBehaviorStrategy reward owner choice)) observer =
      (if choice = none then 0 else 1) * reward (quittingSingletonTerminal owner) observer := by
    cases choice with
    | none =>
        rw [quittingAlwaysContinueProfile_update_pureTime_none,
          quittingTerminalPayoff_quittingAlwaysContinue]
        simp
    | some date =>
        rw [← quittingTerminalPayoff_observerReward reward _ observer owner]
        change quittingTerminalPayoff (quittingObserverReward reward observer)
          (Function.update (quittingAlwaysContinueProfile (quittingObserverReward reward observer))
            owner (quittingPureTimeBehaviorStrategy (quittingObserverReward reward observer)
              owner (some date))) owner = _
        rw [quittingTerminalPayoff_alwaysContinueProfile_update_pureTime_some]
        simp [quittingObserverReward]
  simp_rw [hchoice]
  simp_rw [mul_comm _ (reward (quittingSingletonTerminal owner) observer)]
  rw [expect_const_mul, expect_complementSingletonIndicator]

end GameTheory

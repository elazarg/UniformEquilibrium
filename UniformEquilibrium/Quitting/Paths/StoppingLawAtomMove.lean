import MathUE.ProbabilityMassFunction.MoveAtom
import UniformEquilibrium.Quitting.Paths.StoppingLawOperationalDistance

/-! # Actual behavioral realization of a single stopping-law atom move -/

noncomputable section

namespace GameTheory

open _root_.Math.Probability _root_.Math.ProbabilityMassFunction Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The deterministic pushforward is reconstructed as one independent
behavioral replacement. No other atom or player's law is resampled. -/
def quittingMoveStoppingAtomStrategy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (source target : Option ℕ) : (quittingGame reward).BehaviorStrategy who :=
  quittingStoppingLawBehaviorStrategy reward who
    (pmfMoveAtom (quittingBehaviorStoppingLaws reward profile who) source target)

omit [DecidableEq ι] [Nonempty ι] in
@[simp] theorem quittingMoveStoppingAtomStrategy_stoppingLaw
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (source target : Option ℕ) :
    quittingBehaviorStoppingLaw reward
        (quittingMoveStoppingAtomStrategy reward profile who source target) =
      pmfMoveAtom (quittingBehaviorStoppingLaws reward profile who) source target := by
  simp [quittingMoveStoppingAtomStrategy]

omit [Nonempty ι] in
/-- Actual behavioral payoff affinity reduces the gain to the existing
generic pushforward identity. Source mass zero and one are both accepted. -/
theorem quittingTerminalPayoff_moveStoppingAtom_gain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (source target : Option ℕ) :
    quittingTerminalPayoff reward
        (Function.update profile who
          (quittingMoveStoppingAtomStrategy reward profile who source target)) who -
        quittingTerminalPayoff reward profile who =
      (quittingBehaviorStoppingLaws reward profile who source).toReal *
        (quittingBehaviorPureTimePayoff reward profile who target -
          quittingBehaviorPureTimePayoff reward profile who source) := by
  rw [quittingTerminalPayoff_update_eq_expect_behaviorStoppingLaws,
    quittingTerminalPayoff_eq_expect_behaviorStoppingLaws]
  simp only [quittingBehaviorStoppingLaws, Function.update_self,
    quittingMoveStoppingAtomStrategy_stoppingLaw]
  apply expect_pmfMoveAtom_sub
  intro choice
  exact abs_quittingTerminalPayoff_le_quittingRewardBound reward _ who

/-- A pure-time menu entry is read on the original complete opponent laws.
This is just the existing reconstruction and product-overwrite adapter. -/
theorem quittingBehaviorPureTimePayoff_eq_expect_overwrite
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) (choice : Option ℕ) :
    quittingBehaviorPureTimePayoff reward profile who choice =
      expect (pmfPi (quittingBehaviorStoppingLaws reward profile)) (fun times =>
        quittingTerminalOutcomeReward reward
          (quittingFirstStoppingOutcome (Function.update times who choice)) who) := by
  have hpure := quittingTerminalPayoff_update_stoppingLawBehaviorStrategy_eq_expect
    reward profile who who (PMF.pure choice)
  simp only [expect_pure] at hpure
  rw [quittingBehaviorPureTimePayoff, ← hpure,
    ← quittingStoppingLawExpectedPayoff_behaviorStoppingLaws_eq_terminalPayoff,
    quittingBehaviorStoppingLaws_update]
  simp only [quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy]
  have hbound : ∀ times : ι → Option ℕ,
      |quittingTerminalOutcomeReward reward (quittingFirstStoppingOutcome times) who| ≤
        quittingRewardBound reward := by
    intro times
    cases quittingFirstStoppingOutcome times with
    | none =>
        simpa [quittingTerminalOutcomeReward] using quittingRewardBound_nonneg reward
    | some terminal =>
        simpa [quittingTerminalOutcomeReward] using
          abs_reward_le_quittingRewardBound reward terminal who
  rw [quittingStoppingLawExpectedPayoff, quittingIndependentTerminalOutcomeLaw, expect_map,
    ← pmfPi_bind_update_pure,
    expect_bind_of_bounded _ _ _ hbound]
  simp only [expect_pure]

end GameTheory

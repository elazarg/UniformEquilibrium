import UniformEquilibrium.Quitting.Terminal.PivotRepairFiniteLP

/-! # A signed game requiring the limiting late-response endpoint

For the displayed actual game and feasible repair masses, the first-date and
Never response values are zero, while the limiting late-response value is one half.
-/

noncomputable section

namespace GameTheory.PivotRepairSignedThirdEndpoint

open Math.LinearProgramming

def reward : {S : Finset Bool // S.Nonempty} → Payoff Bool := fun terminal who ↦
  if who then
    if terminal.1 = {true} then 1 else if terminal.1 = {false} then 0 else -1
  else 0

def opponents : Bool → PMF (Option ℕ) := fun _ ↦ PMF.pure none

def input : QuittingPivotRepairLPInput reward where
  opponents := opponents
  pivot := false
  deadline := 1
  deadline_pos := by omega
  opponents_finite := by
    intro j hj choice hchoice
    left
    simpa [opponents, PMF.pure_apply] using hchoice

def mass : PivotRepairMass 1
  | Sum.inl _ => 0
  | Sum.inr .late => 1 / 2
  | Sum.inr .never => 1 / 2
  | Sum.inr .firstAtom => 1 / 2

theorem mass_feasible : IsPivotRepairMassFeasible mass := by
  norm_num [IsPivotRepairMassFeasible, pivotRepairHead, pivotRepairLate,
    pivotRepairNever, pivotRepairFirstAtom, mass, Fin.sum_univ_succ]

private theorem pure_none_none_payoff_true :
    input.purePivotResponderPayoff true none none true = 0 := by
  rw [show input.purePivotResponderPayoff true none none true =
      quittingTerminalPayoff reward
        (quittingPureTimeProfileBehavior reward (fun _ ↦ none)) true by
    unfold QuittingPivotRepairLPInput.purePivotResponderPayoff input opponents
    congr 2
    funext player
    simp [quittingStoppingLawProfile, quittingPureTimeProfileBehavior]
    unfold quittingStoppingLawBehaviorStrategy quittingPureTimeBehaviorStrategy
    funext time history
    simp [Math.Probability.DiscreteHazard.StoppingLaw.toScalarHazard,
      Math.Probability.DiscreteHazard.ScalarHazard.toBoolean,
      Math.Probability.DiscreteHazard.StoppingLaw.finiteMass,
      Math.Probability.DiscreteHazard.StoppingLaw.survival,
      quittingPureTimeHazard]
    apply PMF.ext
    intro stop
    cases stop <;> simp [Math.Probability.DiscreteHazard.booleanCoin,
      PMF.pure_apply]]
  rw [quittingTerminalPayoff_pureTimeProfileBehavior_eq_firstStoppingOutcome]
  simp [quittingFirstStoppingOutcome, quittingEarliestStoppingValue,
    quittingStoppingTimeValue, quittingTerminalOutcomeReward]

theorem earlyContribution_eq_zero : input.earlyContribution mass true = 0 := by
  simp [QuittingPivotRepairLPInput.earlyContribution, mass,
    pivotRepairHead, pivotRepairLate, pivotRepairNever,
    pure_none_none_payoff_true]

theorem signed_endpoints :
    input.responderFirstEndpoint mass true = 0 ∧
      input.responderNeverEndpoint mass true = 0 ∧
      input.responderLimitEndpoint mass true = 1 / 2 := by
  rw [QuittingPivotRepairLPInput.responderFirstEndpoint,
    QuittingPivotRepairLPInput.responderNeverEndpoint,
    QuittingPivotRepairLPInput.responderLimitEndpoint,
    earlyContribution_eq_zero]
  norm_num [QuittingPivotRepairLPInput.otherNeverProduct,
    QuittingPivotRepairLPInput.responderEarlierReward,
    QuittingPivotRepairLPInput.responderTieReward,
    QuittingPivotRepairLPInput.responderLaterReward, reward, input, opponents,
    pivotRepairLate, pivotRepairNever, pivotRepairFirstAtom, mass,
    quittingSingletonTerminal, Finset.ext_iff]

theorem third_endpoint_strictly_needed :
    max (input.responderNeverEndpoint mass true)
        (input.responderFirstEndpoint mass true) <
      input.responderLimitEndpoint mass true := by
  rw [signed_endpoints.1, signed_endpoints.2.1, signed_endpoints.2.2]
  norm_num

end GameTheory.PivotRepairSignedThirdEndpoint

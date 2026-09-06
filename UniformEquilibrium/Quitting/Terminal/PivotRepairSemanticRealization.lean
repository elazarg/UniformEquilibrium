import UniformEquilibrium.Quitting.Terminal.PivotRepairFiniteLP
import UniformEquilibrium.Quitting.Terminal.FiniteOpponentPivotNeverResponse
import MathUE.LinearProgramming.PivotRepairStoppingLaw

/-! # Actual stopping-law semantics of the finite pivot repair objective -/

noncomputable section

namespace GameTheory

open _root_.Math.LinearProgramming _root_.Math.Probability
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace QuittingPivotRepairLPInput

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable (input : QuittingPivotRepairLPInput reward)

/-- Actual independent laws with the provisional pivot mass split inserted. -/
def provisionalLaws (mass : PivotRepairMass input.deadline)
    (hfeasible : IsPivotRepairMassFeasible mass) : ι → PMF (Option ℕ) :=
  Function.update input.opponents input.pivot (pivotRepairProvisionalStoppingLaw mass hfeasible)

/-- Actual independent laws with a geometric pivot tail of the displayed
hazard. This construction does not assert that a relaxed zero first atom is
attained when the late finite mass is positive. -/
def geometricLaws (mass : PivotRepairMass input.deadline)
    (hfeasible : IsPivotRepairMassFeasible mass) (hazard : ℝ)
    (hpositive : 0 < hazard) (hle : hazard ≤ 1) : ι → PMF (Option ℕ) :=
  Function.update input.opponents input.pivot
    (geometricPivotStoppingLaw (pivotRepairProvisionalStoppingLaw mass hfeasible)
      input.deadline hazard hpositive hle)

/-- The single prescribed affine map is the actual provisional payoff. -/
theorem provisional_payoff_eq_prescribedPayoff
    (mass : PivotRepairMass input.deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (observer : ι) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward (input.provisionalLaws mass hfeasible)) observer =
      input.prescribedPayoff mass observer := by
  rw [provisionalLaws, quittingTerminalPayoff_stoppingLawProfile_update_eq_expect,
    expect_pivotRepairProvisionalStoppingLaw]
  rfl

/-- The finite response coefficient is the actual pure-response payoff
against the provisional pivot law, not a separately supplied payoff table. -/
theorem provisional_pureResponse_eq
    (mass : PivotRepairMass input.deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (responder : ι) (hne : responder ≠ input.pivot) (choice : Option ℕ) (observer : ι) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update (input.provisionalLaws mass hfeasible) responder (PMF.pure choice)))
        observer = input.pureResponsePayoff mass responder choice observer := by
  rw [provisionalLaws, Function.update_comm hne.symm,
    quittingTerminalPayoff_stoppingLawProfile_update_eq_expect,
    expect_pivotRepairProvisionalStoppingLaw]
  simp only [pureResponsePayoff, purePivotResponderPayoff, Function.update_comm hne]

/-- The LP early coefficient is the actual unconditional censored payoff. -/
theorem provisional_earlyContribution_eq
    (mass : PivotRepairMass input.deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (responder : ι) (hne : responder ≠ input.pivot) :
    quittingPivotEarlyContribution reward input.opponents input.pivot responder responder
        input.deadline (pivotRepairProvisionalStoppingLaw mass hfeasible) =
      input.earlyContribution mass responder := by
  rw [quittingPivotEarlyContribution, Function.update_comm hne.symm,
    quittingTerminalPayoff_stoppingLawProfile_update_eq_expect,
    expect_censor_pivotRepairProvisionalStoppingLaw input.deadline_pos]
  simp only [earlyContribution, purePivotResponderPayoff, Function.update_comm hne]

/-- The LP Never endpoint is a literal actual response. -/
theorem provisional_neverResponse_eq
    (mass : PivotRepairMass input.deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (responder : ι) (hne : responder ≠ input.pivot) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update (input.provisionalLaws mass hfeasible) responder (PMF.pure none)))
        responder = input.responderNeverEndpoint mass responder := by
  rw [provisionalLaws, quittingTerminalPayoff_pivot_never_response_eq
    reward input.opponents input.pivot responder responder hne input.deadline input.deadline_pos
    (fun j hjp _ ↦ input.opponents_finite j hjp), input.provisional_earlyContribution_eq mass
    hfeasible responder hne, pivotRepairProvisionalStoppingLaw_lateFiniteMass input.deadline_pos]
  unfold responderNeverEndpoint otherNeverProduct responderEarlierReward
  ring

/-- The LP limiting endpoint is the actual limiting finite response. -/
theorem provisional_lateLimit_eq
    (mass : PivotRepairMass input.deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (responder : ι) (hne : responder ≠ input.pivot) :
    quittingPivotLateLimitValue reward input.opponents input.pivot responder responder
        input.deadline
        (pivotRepairProvisionalStoppingLaw mass hfeasible) =
      input.responderLimitEndpoint mass responder := by
  rw [quittingPivotLateLimitValue,
    input.provisional_earlyContribution_eq mass hfeasible responder hne,
    pivotRepairProvisionalStoppingLaw_lateFiniteMass input.deadline_pos,
    pivotRepairProvisionalStoppingLaw_none_toReal]
  rfl

/-- Every geometric hazard retains the same actual prescribed payoff map. -/
theorem geometric_payoff_eq_prescribedPayoff
    (mass : PivotRepairMass input.deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1) (observer : ι) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (input.geometricLaws mass hfeasible hazard hpositive hle))
        observer = input.prescribedPayoff mass observer := by
  rw [geometricLaws, quittingTerminalPayoff_geometric_pivot_eq reward input.opponents input.pivot
    input.deadline input.opponents_finite]
  exact input.provisional_payoff_eq_prescribedPayoff mass hfeasible observer

/-- Head dates and Never have their exact old finite response coefficients
after the actual geometric replacement. -/
theorem geometric_pureResponse_eq_of_head_or_never
    (mass : PivotRepairMass input.deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1)
    (responder : ι) (hne : responder ≠ input.pivot) (choice : Option ℕ)
    (hchoice : choice = none ∨ ∃ time < input.deadline, choice = some time) (observer : ι) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update (input.geometricLaws mass hfeasible hazard hpositive hle)
            responder (PMF.pure choice))) observer =
      input.pureResponsePayoff mass responder choice observer := by
  have heq := quittingTerminalPayoff_pivot_finiteReplacement_eq reward input.opponents input.pivot
    input.deadline input.opponents_finite
    (geometricPivotStoppingLaw (pivotRepairProvisionalStoppingLaw mass hfeasible)
      input.deadline hazard hpositive hle)
    (pivotRepairProvisionalStoppingLaw mass hfeasible)
    (fun _ htime ↦ geometricPivotStoppingLaw_some_of_lt _ _ _ _ _ htime)
    (geometricPivotStoppingLaw_none _ _ _ _ _) responder hne (PMF.pure choice)
    (by
      intro value hvalue
      have heq : value = choice := by simpa [PMF.pure_apply] using hvalue
      exact heq ▸ hchoice) observer
  rw [geometricLaws, heq]
  exact input.provisional_pureResponse_eq mass hfeasible responder hne choice observer

/-- The actual geometric Never response equals the LP Never endpoint. -/
theorem geometric_neverResponse_eq
    (mass : PivotRepairMass input.deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1)
    (responder : ι) (hne : responder ≠ input.pivot) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update (input.geometricLaws mass hfeasible hazard hpositive hle)
            responder (PMF.pure none))) responder =
      input.responderNeverEndpoint mass responder := by
  rw [input.geometric_pureResponse_eq_of_head_or_never mass hfeasible hazard hpositive hle
    responder hne none (Or.inl rfl) responder]
  rw [← input.provisional_pureResponse_eq mass hfeasible responder hne none responder]
  exact input.provisional_neverResponse_eq mass hfeasible responder hne

/-- The geometric early term is the LP's actual censored-head coefficient. -/
theorem geometric_earlyContribution_eq
    (mass : PivotRepairMass input.deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1)
    (responder : ι) (hne : responder ≠ input.pivot) :
    quittingPivotEarlyContribution reward input.opponents input.pivot responder responder
        input.deadline (geometricPivotStoppingLaw
          (pivotRepairProvisionalStoppingLaw mass hfeasible) input.deadline hazard hpositive hle) =
      input.earlyContribution mass responder := by
  have heq : quittingPivotEarlyContribution reward input.opponents input.pivot responder responder
      input.deadline (geometricPivotStoppingLaw
        (pivotRepairProvisionalStoppingLaw mass hfeasible) input.deadline hazard hpositive hle) =
      quittingPivotEarlyContribution reward input.opponents input.pivot responder responder
        input.deadline (pivotRepairProvisionalStoppingLaw mass hfeasible) := by
    unfold quittingPivotEarlyContribution
    rw [censorLateFiniteStoppingLaw_geometricPivotStoppingLaw _ input.deadline_pos]
  rw [heq]
  exact input.provisional_earlyContribution_eq mass hfeasible responder hne

/-- The geometric late limit is exactly the LP limiting endpoint. -/
theorem geometric_lateLimit_eq
    (mass : PivotRepairMass input.deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1)
    (responder : ι) (hne : responder ≠ input.pivot) :
    quittingPivotLateLimitValue reward input.opponents input.pivot responder responder
        input.deadline
        (geometricPivotStoppingLaw (pivotRepairProvisionalStoppingLaw mass hfeasible)
          input.deadline hazard hpositive hle) = input.responderLimitEndpoint mass responder := by
  rw [quittingPivotLateLimitValue,
    input.geometric_earlyContribution_eq mass hfeasible hazard hpositive hle responder hne,
    geometricPivotStoppingLaw_lateFiniteMass _ input.deadline_pos,
    pivotRepairProvisionalStoppingLaw_lateFiniteMass input.deadline_pos,
    geometricPivotStoppingLaw_none, pivotRepairProvisionalStoppingLaw_none_toReal]
  rfl

/-- When the constructed first atom equals the LP coordinate, every actual
geometric late response is the exact interpolation of the LP first and
limiting endpoints. The zero-tail case is included. -/
theorem geometric_lateResponse_eq_affine
    (mass : PivotRepairMass input.deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1)
    (hmatch : pivotRepairLate mass * hazard = pivotRepairFirstAtom mass)
    (responder : ι) (hne : responder ≠ input.pivot) (offset : ℕ) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update (input.geometricLaws mass hfeasible hazard hpositive hle)
            responder (PMF.pure (some (input.deadline + offset))))) responder =
      (1 - hazard) ^ offset * input.responderFirstEndpoint mass responder +
        (1 - (1 - hazard) ^ offset) * input.responderLimitEndpoint mass responder := by
  rw [geometricLaws, quittingTerminalPayoff_pivot_late_response_eq reward input.opponents
    input.pivot responder responder hne input.deadline (input.deadline + offset)
    input.deadline_pos (by omega) (fun j hjp _ ↦ input.opponents_finite j hjp)]
  rw [input.geometric_earlyContribution_eq mass hfeasible hazard hpositive hle responder hne,
    geometricPivotStoppingLaw_lateFiniteMass _ input.deadline_pos,
    geometricPivotStoppingLaw_none, pivotRepairProvisionalStoppingLaw_none_toReal,
    geometricPivotStoppingLaw_sum_Ico_add _ input.deadline_pos,
    geometricPivotStoppingLaw_add_apply_toReal _ input.deadline_pos,
    pivotRepairProvisionalStoppingLaw_lateFiniteMass input.deadline_pos]
  unfold responderFirstEndpoint responderLimitEndpoint otherNeverProduct
    responderEarlierReward responderTieReward responderLaterReward
  rw [← hmatch]
  ring

theorem geometric_firstResponse_eq
    (mass : PivotRepairMass input.deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1)
    (hmatch : pivotRepairLate mass * hazard = pivotRepairFirstAtom mass)
    (responder : ι) (hne : responder ≠ input.pivot) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update (input.geometricLaws mass hfeasible hazard hpositive hle)
            responder (PMF.pure (some input.deadline)))) responder =
      input.responderFirstEndpoint mass responder := by
  simpa using input.geometric_lateResponse_eq_affine
    mass hfeasible hazard hpositive hle hmatch responder hne 0

end QuittingPivotRepairLPInput
end GameTheory

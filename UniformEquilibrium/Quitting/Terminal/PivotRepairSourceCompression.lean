import UniformEquilibrium.Quitting.Terminal.PivotRepairExactObjective
import MathUE.LinearProgramming.PivotRepairMassOfStoppingLaw

/-! # Actual pivot laws produce no-worse feasible repair points -/

noncomputable section

namespace GameTheory.QuittingPivotRepairLPInput

open _root_.Math.LinearProgramming _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable (input : QuittingPivotRepairLPInput reward)

/-- Every complete pivot law supplies a literal feasible repair point with
the same prescribed payoff vector and no larger objective. The producer
uses actual geometric cap domination, not supplied response coefficients. -/
theorem exists_feasible_mass_payoff_eq_and_objective_le (law : PMF (Option ℕ)) :
    letI : Nonempty ι := ⟨input.pivot⟩
    ∃ mass : PivotRepairMass input.deadline, IsPivotRepairMassFeasible mass ∧
      quittingTerminalPayoff reward
          (quittingStoppingLawProfile reward (Function.update input.opponents input.pivot law)) =
        input.prescribedPayoff mass ∧
      input.objective mass ≤ quittingTerminalExploitability reward
        (quittingStoppingLawProfile reward (Function.update input.opponents input.pivot law)) := by
  letI : Nonempty ι := ⟨input.pivot⟩
  obtain ⟨hazard, hpositive, hle, hpayoff, hexploitability⟩ :=
    exists_geometric_pivot_payoff_eq_and_exploitability_le reward input.opponents input.pivot
      input.deadline input.deadline_pos input.opponents_finite law
  let mass := pivotRepairMassOfStoppingLaw law input.deadline
    (stoppingLawLateFiniteMass law (input.deadline - 1) * hazard)
  have htail : 0 ≤ stoppingLawLateFiniteMass law (input.deadline - 1) :=
    pmfFiniteComplementMass_nonneg _ _
  have hfeasible : IsPivotRepairMassFeasible mass :=
    isPivotRepairMassFeasible_ofStoppingLaw law input.deadline_pos _
      (mul_nonneg htail hpositive.le) (by nlinarith)
  have hlaws : input.geometricLaws mass hfeasible hazard hpositive hle =
      Function.update input.opponents input.pivot
        (geometricPivotStoppingLaw law input.deadline hazard hpositive hle) := by
    unfold geometricLaws mass
    rw [geometricPivotStoppingLaw_ofStoppingLaw_eq law input.deadline_pos]
  have hobjective := input.geometric_exploitability_eq_objective
    mass hfeasible hazard hpositive hle (by rfl)
  rw [hlaws] at hobjective
  refine ⟨mass, hfeasible, ?_, ?_⟩
  · funext observer
    rw [← hpayoff]
    have h := input.geometric_payoff_eq_prescribedPayoff
      mass hfeasible hazard hpositive hle observer
    rw [hlaws] at h
    exact h
  · rw [← hobjective]
    exact hexploitability

end GameTheory.QuittingPivotRepairLPInput

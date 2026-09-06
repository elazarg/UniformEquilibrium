import UniformEquilibrium.Quitting.Terminal.PivotRepairSourceCompression
import UniformEquilibrium.Quitting.Terminal.PivotRepairBehavioralApproximation
import UniformEquilibrium.Quitting.Terminal.StoppingLawExploitability

/-! # Exact finite-LP value of one-marginal behavioral repair -/

noncomputable section

namespace GameTheory.QuittingPivotRepairLPInput

open _root_.Math.LinearProgramming

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable (input : QuittingPivotRepairLPInput reward)

/-- The terminal exploitability values obtained by arbitrary pivot behavior
are exactly those obtained by arbitrary complete pivot stopping laws. -/
theorem range_pivotBehavior_exploitability_eq_range_stoppingLaw :
    letI : Nonempty ι := ⟨input.pivot⟩
    Set.range (fun deviation : (quittingGame reward).BehaviorStrategy input.pivot ↦
      quittingTerminalExploitability reward
        (Function.update (quittingStoppingLawProfile reward input.opponents)
          input.pivot deviation)) =
      Set.range (fun law : PMF (Option ℕ) ↦ quittingTerminalExploitability reward
        (quittingStoppingLawProfile reward
          (Function.update input.opponents input.pivot law))) := by
  letI : Nonempty ι := ⟨input.pivot⟩
  have hvalue (deviation : (quittingGame reward).BehaviorStrategy input.pivot) :
      quittingTerminalExploitability reward
          (Function.update (quittingStoppingLawProfile reward input.opponents)
            input.pivot deviation) =
        quittingTerminalExploitability reward
          (quittingStoppingLawProfile reward (Function.update input.opponents input.pivot
            (quittingBehaviorStoppingLaw reward deviation))) := by
    rw [← quittingTerminalExploitability_stoppingLawProfile_behaviorLaws_eq,
      quittingBehaviorStoppingLaws_update, quittingBehaviorStoppingLaws_stoppingLawProfile]
  ext value
  constructor
  · rintro ⟨deviation, rfl⟩
    exact ⟨quittingBehaviorStoppingLaw reward deviation, (hvalue deviation).symm⟩
  · rintro ⟨law, rfl⟩
    refine ⟨quittingStoppingLawBehaviorStrategy reward input.pivot law, ?_⟩
    dsimp only
    rw [hvalue, quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy]

/-- A minimizing feasible repair point gives the exact greatest lower bound
over all actual pivot laws. Attainment in the law space is not asserted. -/
theorem isGLB_pivotLaw_exploitability_of_objective_minimizer
    (mass : PivotRepairMass input.deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (hmin : IsMinOn input.objective (pivotRepairMassFeasibleSet input.deadline) mass) :
    letI : Nonempty ι := ⟨input.pivot⟩
    IsGLB (Set.range (fun law : PMF (Option ℕ) ↦ quittingTerminalExploitability reward
      (quittingStoppingLawProfile reward (Function.update input.opponents input.pivot law))))
      (input.objective mass) := by
  letI : Nonempty ι := ⟨input.pivot⟩
  constructor
  · rintro value ⟨law, rfl⟩
    obtain ⟨other, hother, _, hobjective⟩ :=
      input.exists_feasible_mass_payoff_eq_and_objective_le law
    exact (hmin hother).trans hobjective
  · intro bound hbound
    apply le_of_forall_pos_le_add
    intro error herror
    obtain ⟨law, _, hobjective, _⟩ :=
      input.exists_law_payoff_eq_and_exploitability_le_objective_add mass hfeasible error herror
    exact (hbound ⟨law, rfl⟩).trans hobjective

/-- The compact finite LP attains a mass-coordinate optimum whose value is
the infimum over all pivot behavioral strategies against the fixed actual
finite opponent laws. The behavioral infimum need not be attained. -/
theorem exists_objective_minimizer_eq_behavioral_infimum :
    letI : Nonempty ι := ⟨input.pivot⟩
    ∃ mass : PivotRepairMass input.deadline, IsPivotRepairMassFeasible mass ∧
      IsMinOn input.objective (pivotRepairMassFeasibleSet input.deadline) mass ∧
      input.objective mass =
        sInf (Set.range (fun deviation : (quittingGame reward).BehaviorStrategy input.pivot ↦
          quittingTerminalExploitability reward
            (Function.update (quittingStoppingLawProfile reward input.opponents)
              input.pivot deviation))) := by
  letI : Nonempty ι := ⟨input.pivot⟩
  obtain ⟨mass, hfeasible, hmin⟩ := input.exists_objective_minimizer
  refine ⟨mass, hfeasible, hmin, ?_⟩
  rw [input.range_pivotBehavior_exploitability_eq_range_stoppingLaw]
  exact ((input.isGLB_pivotLaw_exploitability_of_objective_minimizer mass hfeasible hmin).csInf_eq
    (Set.range_nonempty _)).symm

end GameTheory.QuittingPivotRepairLPInput

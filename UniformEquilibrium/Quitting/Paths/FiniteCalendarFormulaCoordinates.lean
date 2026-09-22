import UniformEquilibrium.Quitting.Paths.FiniteCalendarParameters
import UniformEquilibrium.Quitting.Paths.FiniteCalendarPayoffFormula

/-! # Deterministic formula coordinates for finite quitting calendars -/

namespace GameTheory

open MathUE.RealQuantifierElimination

variable {players deadline : Nat}

/-- The rational-expression variable assigned to a raw calendar coordinate. -/
def quittingFiniteCalendarVariableTerm
    (entry : QuittingFiniteCalendarVariable (Fin players) deadline) :
    RingExpression (quittingFiniteCalendarParameterCount players deadline) :=
  .var (quittingFiniteCalendarVariableIndex entry)

/-- The deterministic-coordinate formula for the product of player simplices. -/
def quittingFiniteCalendarSimplexFormula (players deadline : Nat) :
    QuantifierFreeFormula (quittingFiniteCalendarParameterCount players deadline) :=
  quittingFiniteCalendarSimplexFormulaWithTerms
    (quittingFiniteCalendarVariableTerm (players := players) (deadline := deadline))

@[simp]
theorem evalReal_quittingFiniteCalendarVariableTerm_parameters
    (profile : MixedSimplex (Fin players)
      (fun _ => QuittingFiniteDeadlineTimingAction deadline))
    (entry : QuittingFiniteCalendarVariable (Fin players) deadline) :
    (quittingFiniteCalendarVariableTerm entry).evalReal
        (quittingFiniteCalendarParameters fun pair =>
          (profile pair.1).weights pair.2) =
      (profile entry.1).weights entry.2 := by
  change (profile
      ((quittingFiniteCalendarVariableList players deadline).get
        (quittingFiniteCalendarVariableIndex entry)).1).weights
      ((quittingFiniteCalendarVariableList players deadline).get
        (quittingFiniteCalendarVariableIndex entry)).2 = _
  rw [quittingFiniteCalendarVariableList_get_index]

@[simp]
theorem quittingFiniteCalendarSimplexFormula_holdsAt_iff
    (parameters : Fin (quittingFiniteCalendarParameterCount players deadline) → ℝ) :
    (quittingFiniteCalendarSimplexFormula players deadline).HoldsAt parameters ↔
      (∀ who choice,
        0 ≤ quittingFiniteCalendarFromParameters parameters (who, choice)) ∧
      ∀ who, quittingFiniteCalendarFromParameters parameters (who, none) +
        ∑ time : Fin deadline,
          quittingFiniteCalendarFromParameters parameters (who, some time) = 1 := by
  rw [quittingFiniteCalendarSimplexFormula,
    quittingFiniteCalendarSimplexFormulaWithTerms_holdsAt_iff]
  rfl

/-- Raw parameters satisfying the simplex guard define a genuine calendar profile. -/
noncomputable def quittingFiniteCalendarProfileOfParameters
    (parameters : Fin (quittingFiniteCalendarParameterCount players deadline) → ℝ)
    (hparameters :
      (quittingFiniteCalendarSimplexFormula players deadline).HoldsAt parameters) :
    MixedSimplex (Fin players)
      (fun _ => QuittingFiniteDeadlineTimingAction deadline) :=
  fun who =>
    ⟨Finsupp.equivFunOnFinite.symm
        (fun choice => quittingFiniteCalendarFromParameters parameters (who, choice)),
      by
        intro choice
        rw [Finsupp.equivFunOnFinite_symm_apply_apply]
        exact (quittingFiniteCalendarSimplexFormula_holdsAt_iff parameters).mp
          hparameters |>.1 who choice,
      by
        rw [Finsupp.equivFunOnFinite_symm_sum, Fintype.sum_option]
        exact (quittingFiniteCalendarSimplexFormula_holdsAt_iff parameters).mp
          hparameters |>.2 who⟩

@[simp]
theorem quittingFiniteCalendarProfileOfParameters_apply
    (parameters : Fin (quittingFiniteCalendarParameterCount players deadline) → ℝ)
    (hparameters :
      (quittingFiniteCalendarSimplexFormula players deadline).HoldsAt parameters)
    (who : Fin players) (choice : Option (Fin deadline)) :
    (quittingFiniteCalendarProfileOfParameters parameters hparameters who).weights choice =
      quittingFiniteCalendarFromParameters parameters (who, choice) :=
  Finsupp.equivFunOnFinite_symm_apply_apply _ _

@[simp]
theorem quittingFiniteCalendarSimplexFormula_holdsAt_parameters
    (profile : MixedSimplex (Fin players)
      (fun _ => QuittingFiniteDeadlineTimingAction deadline)) :
    (quittingFiniteCalendarSimplexFormula players deadline).HoldsAt
      (quittingFiniteCalendarParameters fun pair =>
        (profile pair.1).weights pair.2) := by
  apply (quittingFiniteCalendarSimplexFormula_holdsAt_iff _).mpr
  constructor
  · intro who choice
    rw [quittingFiniteCalendarFromParameters_encode]
    exact (profile who).weights_nonneg choice
  · intro who
    rw [quittingFiniteCalendarFromParameters_encode]
    have htotal := (profile who).total_of_fintype
    rw [Fintype.sum_option] at htotal
    exact htotal

end GameTheory

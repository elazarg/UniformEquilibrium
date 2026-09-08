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
        (quittingFiniteCalendarParameters fun pair => profile pair.1 pair.2) =
      profile entry.1 entry.2 := by
  change profile
      ((quittingFiniteCalendarVariableList players deadline).get
        (quittingFiniteCalendarVariableIndex entry)).1
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
def quittingFiniteCalendarProfileOfParameters
    (parameters : Fin (quittingFiniteCalendarParameterCount players deadline) → ℝ)
    (hparameters :
      (quittingFiniteCalendarSimplexFormula players deadline).HoldsAt parameters) :
    MixedSimplex (Fin players)
      (fun _ => QuittingFiniteDeadlineTimingAction deadline) :=
  fun who =>
    ⟨fun choice => quittingFiniteCalendarFromParameters parameters (who, choice),
      ⟨fun choice =>
          (quittingFiniteCalendarSimplexFormula_holdsAt_iff parameters).mp
            hparameters |>.1 who choice,
        by
          rw [Fintype.sum_option]
          exact (quittingFiniteCalendarSimplexFormula_holdsAt_iff parameters).mp
            hparameters |>.2 who⟩⟩

@[simp]
theorem quittingFiniteCalendarProfileOfParameters_apply
    (parameters : Fin (quittingFiniteCalendarParameterCount players deadline) → ℝ)
    (hparameters :
      (quittingFiniteCalendarSimplexFormula players deadline).HoldsAt parameters)
    (who : Fin players) (choice : Option (Fin deadline)) :
    quittingFiniteCalendarProfileOfParameters parameters hparameters who choice =
      quittingFiniteCalendarFromParameters parameters (who, choice) :=
  rfl

@[simp]
theorem quittingFiniteCalendarSimplexFormula_holdsAt_parameters
    (profile : MixedSimplex (Fin players)
      (fun _ => QuittingFiniteDeadlineTimingAction deadline)) :
    (quittingFiniteCalendarSimplexFormula players deadline).HoldsAt
      (quittingFiniteCalendarParameters fun pair => profile pair.1 pair.2) := by
  apply (quittingFiniteCalendarSimplexFormula_holdsAt_iff _).mpr
  constructor
  · intro who choice
    rw [quittingFiniteCalendarFromParameters_encode]
    exact (profile who).property.1 choice
  · intro who
    rw [quittingFiniteCalendarFromParameters_encode]
    have htotal := (profile who).property.2
    rw [Fintype.sum_option] at htotal
    exact htotal

end GameTheory

import UniformEquilibrium.Quitting.Paths.FiniteCalendarPayoffFormula

/-! # Formula frontends for weak and group finite-calendar exclusion -/

namespace GameTheory

open Math.PolynomialSignCell.SignFormula
open MathUE.RealQuantifierElimination

variable {players deadline arity : Nat}

/-- Singleton rewards are nonnegative on a supplied owner set. -/
def quittingSingletonNonnegativeFormulaWithTerms
    (rewardTerm : {S : Finset (Fin players) // S.Nonempty} →
      Fin players → RingExpression arity)
    (owners : Finset (Fin players)) : QuantifierFreeFormula arity :=
  conjunction ((owners.sort (· ≤ ·)).map fun observer =>
    QuantifierFreeFormula.nonnegative
      (rewardTerm (quittingSingletonTerminal observer) observer))

@[simp]
theorem quittingSingletonNonnegativeFormulaWithTerms_holdsAt_iff
    (rewardTerm : {S : Finset (Fin players) // S.Nonempty} →
      Fin players → RingExpression arity)
    (owners : Finset (Fin players)) (environment : Fin arity → ℝ) :
    (quittingSingletonNonnegativeFormulaWithTerms rewardTerm owners).HoldsAt
        environment ↔
      ∀ observer ∈ owners,
        0 ≤ (rewardTerm (quittingSingletonTerminal observer) observer).evalReal
          environment := by
  rw [quittingSingletonNonnegativeFormulaWithTerms,
    QuantifierFreeFormula.HoldsAt, holds_conjunction_iff]
  constructor
  · intro hall observer hobserver
    apply (QuantifierFreeFormula.holdsAt_nonnegative_iff _ environment).mp
    apply hall
    rw [List.mem_map]
    exact ⟨observer, by simpa using hobserver, rfl⟩
  · intro hall formula hformula
    rw [List.mem_map] at hformula
    obtain ⟨observer, hobserver, rfl⟩ := hformula
    apply (QuantifierFreeFormula.holdsAt_nonnegative_iff _ environment).mpr
    exact hall observer (by simpa using hobserver)

/-- Weak exclusion on one calendar, guarded by the calendar simplex. -/
def quittingFiniteCalendarRawWeakSubsetFormulaWithTerms
    (rewardTerm : {S : Finset (Fin players) // S.Nonempty} →
      Fin players → RingExpression arity)
    (calendarTerm : QuittingFiniteCalendarVariable (Fin players) deadline →
      RingExpression arity)
    (owners : Finset (Fin players)) : QuantifierFreeFormula arity :=
  .and (quittingSingletonNonnegativeFormulaWithTerms rewardTerm owners)
    (.or (.not (quittingFiniteCalendarSimplexFormulaWithTerms calendarTerm))
      (disjunction ((owners.sort (· ≤ ·)).map fun observer =>
        QuantifierFreeFormula.nonpositive
          (quittingFiniteCalendarSingletonSurplusExpressionWithTerms
            rewardTerm calendarTerm observer))))

@[simp]
theorem quittingFiniteCalendarRawWeakSubsetFormulaWithTerms_holdsAt_iff
    (rewardTerm : {S : Finset (Fin players) // S.Nonempty} →
      Fin players → RingExpression arity)
    (calendarTerm : QuittingFiniteCalendarVariable (Fin players) deadline →
      RingExpression arity)
    (owners : Finset (Fin players)) (environment : Fin arity → ℝ) :
    (quittingFiniteCalendarRawWeakSubsetFormulaWithTerms rewardTerm calendarTerm
        owners).HoldsAt environment ↔
      (∀ observer ∈ owners,
        0 ≤ (rewardTerm (quittingSingletonTerminal observer) observer).evalReal
          environment) ∧
      ((¬(quittingFiniteCalendarSimplexFormulaWithTerms calendarTerm).HoldsAt
          environment) ∨
        ∃ observer ∈ owners,
          (quittingFiniteCalendarSingletonSurplusExpressionWithTerms
            rewardTerm calendarTerm observer).evalReal environment ≤ 0) := by
  change
    (quittingSingletonNonnegativeFormulaWithTerms rewardTerm owners).HoldsAt
        environment ∧
      ((¬(quittingFiniteCalendarSimplexFormulaWithTerms calendarTerm).HoldsAt
          environment) ∨
        (disjunction ((owners.sort (· ≤ ·)).map fun observer =>
          QuantifierFreeFormula.nonpositive
            (quittingFiniteCalendarSingletonSurplusExpressionWithTerms
              rewardTerm calendarTerm observer))).Holds
          (realSignAssignment environment)) ↔ _
  rw [quittingSingletonNonnegativeFormulaWithTerms_holdsAt_iff,
    holds_disjunction_iff]
  apply and_congr Iff.rfl
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨formula, hformula, hholds⟩
    rw [List.mem_map] at hformula
    obtain ⟨observer, hobserver, rfl⟩ := hformula
    refine ⟨observer, by simpa using hobserver, ?_⟩
    exact (QuantifierFreeFormula.holdsAt_nonpositive_iff _ environment).mp hholds
  · rintro ⟨observer, hobserver, hsurplus⟩
    refine ⟨_, ?_,
      (QuantifierFreeFormula.holdsAt_nonpositive_iff _ environment).mpr hsurplus⟩
    rw [List.mem_map]
    exact ⟨observer, by simpa using hobserver, rfl⟩

/-- The weighted singleton-surplus expression for an ordered player pair. -/
def quittingFiniteCalendarOrderedPairSurplusExpressionWithTerms
    (rewardTerm : {S : Finset (Fin players) // S.Nonempty} →
      Fin players → RingExpression arity)
    (calendarTerm : QuittingFiniteCalendarVariable (Fin players) deadline →
      RingExpression arity)
    (lambda : RingExpression arity) (first second : Fin players) :
    RingExpression arity :=
  (1 + -lambda) *
      quittingFiniteCalendarSingletonSurplusExpressionWithTerms
        rewardTerm calendarTerm first +
    lambda * quittingFiniteCalendarSingletonSurplusExpressionWithTerms
      rewardTerm calendarTerm second

@[simp]
theorem evalReal_quittingFiniteCalendarOrderedPairSurplusExpressionWithTerms
    (rewardTerm : {S : Finset (Fin players) // S.Nonempty} →
      Fin players → RingExpression arity)
    (calendarTerm : QuittingFiniteCalendarVariable (Fin players) deadline →
      RingExpression arity)
    (lambda : RingExpression arity) (first second : Fin players)
    (environment : Fin arity → ℝ) :
    (quittingFiniteCalendarOrderedPairSurplusExpressionWithTerms
      rewardTerm calendarTerm lambda first second).evalReal environment =
        (1 - lambda.evalReal environment) *
            (quittingFiniteCalendarSingletonSurplusExpressionWithTerms
              rewardTerm calendarTerm first).evalReal environment +
          lambda.evalReal environment *
        (quittingFiniteCalendarSingletonSurplusExpressionWithTerms
              rewardTerm calendarTerm second).evalReal environment := by
  rw [quittingFiniteCalendarOrderedPairSurplusExpressionWithTerms]
  rw [RingExpression.evalReal_add, RingExpression.evalReal_mul,
    RingExpression.evalReal_mul, RingExpression.evalReal_add,
    RingExpression.evalReal_one, RingExpression.evalReal_neg]
  ring

private def orderedPairFormulasWithTerms
    (rewardTerm : {S : Finset (Fin players) // S.Nonempty} →
      Fin players → RingExpression arity)
    (calendarTerm : QuittingFiniteCalendarVariable (Fin players) deadline →
      RingExpression arity)
    (lambda : RingExpression arity) : List (QuantifierFreeFormula arity) :=
  (List.ofFn fun first : Fin players => first).flatMap fun first =>
    (List.ofFn fun second : Fin players => second).map fun second =>
      if first = second then .bot else
        QuantifierFreeFormula.nonpositive
          (quittingFiniteCalendarOrderedPairSurplusExpressionWithTerms
            rewardTerm calendarTerm lambda first second)

/-- Ordered-pair group exclusion on one calendar, guarded by the simplex. -/
def quittingFiniteCalendarRawOrderedPairFormulaWithTerms
    (rewardTerm : {S : Finset (Fin players) // S.Nonempty} →
      Fin players → RingExpression arity)
    (calendarTerm : QuittingFiniteCalendarVariable (Fin players) deadline →
      RingExpression arity)
    (lambda : RingExpression arity) : QuantifierFreeFormula arity :=
  .or (.not (quittingFiniteCalendarSimplexFormulaWithTerms calendarTerm))
    (disjunction (orderedPairFormulasWithTerms rewardTerm calendarTerm lambda))

@[simp]
theorem quittingFiniteCalendarRawOrderedPairFormulaWithTerms_holdsAt_iff
    (rewardTerm : {S : Finset (Fin players) // S.Nonempty} →
      Fin players → RingExpression arity)
    (calendarTerm : QuittingFiniteCalendarVariable (Fin players) deadline →
      RingExpression arity)
    (lambda : RingExpression arity) (environment : Fin arity → ℝ) :
    (quittingFiniteCalendarRawOrderedPairFormulaWithTerms
        rewardTerm calendarTerm lambda).HoldsAt environment ↔
      (¬(quittingFiniteCalendarSimplexFormulaWithTerms calendarTerm).HoldsAt
          environment) ∨
        ∃ first second, first ≠ second ∧
          (quittingFiniteCalendarOrderedPairSurplusExpressionWithTerms
            rewardTerm calendarTerm lambda first second).evalReal environment ≤ 0 := by
  change
    (¬(quittingFiniteCalendarSimplexFormulaWithTerms calendarTerm).HoldsAt
        environment) ∨
      (disjunction (orderedPairFormulasWithTerms rewardTerm calendarTerm lambda)).Holds
        (realSignAssignment environment) ↔ _
  rw [holds_disjunction_iff]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨formula, hformula, hholds⟩
    rw [orderedPairFormulasWithTerms, List.mem_flatMap] at hformula
    obtain ⟨first, _, hfirst⟩ := hformula
    rw [List.mem_map] at hfirst
    obtain ⟨second, _, rfl⟩ := hfirst
    by_cases hequal : first = second
    · simp [hequal, Holds] at hholds
    · refine ⟨first, second, hequal, ?_⟩
      simp only [if_neg hequal] at hholds
      exact (QuantifierFreeFormula.holdsAt_nonpositive_iff _ environment).mp hholds
  · rintro ⟨first, second, hne, hsurplus⟩
    refine ⟨QuantifierFreeFormula.nonpositive
      (quittingFiniteCalendarOrderedPairSurplusExpressionWithTerms
        rewardTerm calendarTerm lambda first second), ?_, ?_⟩
    · rw [orderedPairFormulasWithTerms, List.mem_flatMap]
      refine ⟨first, List.mem_ofFn.mpr ⟨first, rfl⟩, ?_⟩
      rw [List.mem_map]
      refine ⟨second, List.mem_ofFn.mpr ⟨second, rfl⟩, ?_⟩
      simp only [if_neg hne]
    · exact (QuantifierFreeFormula.holdsAt_nonpositive_iff _ environment).mpr hsurplus

end GameTheory

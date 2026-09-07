import MathUE.Logic.SignFormula

/-!
# Finite conjunctions and disjunctions of sign formulas

The folds use the logical units, so empty conjunctions are true and empty
disjunctions are false.
-/

namespace Math.PolynomialSignCell.SignFormula

/-- Right-associated conjunction of a finite formula list. -/
def conjunction : List (SignFormula ι) → SignFormula ι
  | [] => .top
  | formula :: formulas => .and formula (conjunction formulas)

/-- Right-associated disjunction of a finite formula list. -/
def disjunction : List (SignFormula ι) → SignFormula ι
  | [] => .bot
  | formula :: formulas => .or formula (disjunction formulas)

@[simp]
theorem holds_conjunction_iff
    (formulas : List (SignFormula ι)) (assignment : ι → SignType) :
    (conjunction formulas).Holds assignment ↔
      ∀ formula ∈ formulas, formula.Holds assignment := by
  induction formulas with
  | nil => simp [conjunction, Holds]
  | cons formula formulas ih => simp [conjunction, Holds, ih]

@[simp]
theorem holds_disjunction_iff
    (formulas : List (SignFormula ι)) (assignment : ι → SignType) :
    (disjunction formulas).Holds assignment ↔
      ∃ formula ∈ formulas, formula.Holds assignment := by
  induction formulas with
  | nil => simp [disjunction, Holds]
  | cons formula formulas ih => simp [disjunction, Holds, ih]

end Math.PolynomialSignCell.SignFormula

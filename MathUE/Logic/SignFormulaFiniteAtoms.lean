import MathUE.Logic.SignFormula

/-!
# Finite atom rows for sign formulas

Atoms are retained in syntax order, including duplicates.  Evaluation consumes
the corresponding finite sign row, so no decidable equality or default lookup
on the atom type is needed.
-/

namespace Math.PolynomialSignCell.SignFormula

/-- Atom occurrences in syntax order, with duplicates retained. -/
def atoms : SignFormula ι → List ι
  | .atom index _ => [index]
  | .top => []
  | .bot => []
  | .and left right => left.atoms ++ right.atoms
  | .or left right => left.atoms ++ right.atoms
  | .not formula => formula.atoms

/-- Number of atom occurrences. -/
def atomCount : SignFormula ι → Nat
  | .atom _ _ => 1
  | .top => 0
  | .bot => 0
  | .and left right => left.atomCount + right.atomCount
  | .or left right => left.atomCount + right.atomCount
  | .not formula => formula.atomCount

@[simp] theorem length_atoms (formula : SignFormula ι) :
    formula.atoms.length = formula.atomCount := by
  induction formula <;> simp_all [atoms, atomCount]

/-- Executable evaluation from the finite row aligned with `atoms`. -/
def evalRow : SignFormula ι → List SignType → Bool
  | .atom _ expected, row => decide (row.head? = some expected)
  | .top, _ => true
  | .bot, _ => false
  | .and left right, row =>
      left.evalRow (row.take left.atomCount) &&
        right.evalRow (row.drop left.atomCount)
  | .or left right, row =>
      left.evalRow (row.take left.atomCount) ||
        right.evalRow (row.drop left.atomCount)
  | .not formula, row => !(formula.evalRow row)

/-- Evaluation on the actual atom-sign row agrees with ordinary assignment
evaluation. -/
theorem evalRow_map_atoms (formula : SignFormula ι) (assignment : ι → SignType) :
    formula.evalRow (formula.atoms.map assignment) = formula.eval assignment := by
  induction formula with
  | atom index expected => simp [evalRow, atoms, SignFormula.eval]
  | top => rfl
  | bot => rfl
  | and left right ihLeft ihRight =>
      simp [evalRow, atoms, ihLeft, ihRight, SignFormula.eval]
  | or left right ihLeft ihRight =>
      simp [evalRow, atoms, ihLeft, ihRight, SignFormula.eval]
  | not formula ih => simp [evalRow, atoms, ih, SignFormula.eval]

/-- Boolean row evaluation is true exactly when the formula holds on the
actual atom-sign row. -/
theorem evalRow_map_atoms_eq_true_iff
    (formula : SignFormula ι) (assignment : ι → SignType) :
    formula.evalRow (formula.atoms.map assignment) = true ↔ formula.Holds assignment := by
  rw [evalRow_map_atoms, eval_eq_true_iff]

end Math.PolynomialSignCell.SignFormula

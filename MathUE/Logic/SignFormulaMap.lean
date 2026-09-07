import MathUE.Logic.SignFormula

/-! Atom relabeling preserves the Boolean structure and truth of sign formulas. -/

namespace Math.PolynomialSignCell.SignFormula

/-- Relabel every atom without changing the Boolean structure. -/
def mapAtoms (function : ι → κ) : SignFormula ι → SignFormula κ
  | .atom value sign => .atom (function value) sign
  | .top => .top
  | .bot => .bot
  | .and left right => .and (left.mapAtoms function) (right.mapAtoms function)
  | .or left right => .or (left.mapAtoms function) (right.mapAtoms function)
  | .not formula => .not (formula.mapAtoms function)

theorem holds_mapAtoms (function : ι → κ) (formula : SignFormula ι)
    (assignment : κ → SignType) :
    (formula.mapAtoms function).Holds assignment ↔ formula.Holds (assignment ∘ function) := by
  induction formula with
  | atom atom sign => rfl
  | top => rfl
  | bot => rfl
  | and left right ihl ihr => exact and_congr ihl ihr
  | or left right ihl ihr => exact or_congr ihl ihr
  | not formula ih => exact not_congr ih

end Math.PolynomialSignCell.SignFormula

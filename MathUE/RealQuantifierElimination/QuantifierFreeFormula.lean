import MathUE.RealQuantifierElimination.RingExpression
import MathUE.Logic.SignFormula

/-! # Quantifier-free rational polynomial formulas -/

namespace MathUE.RealQuantifierElimination

open Math.PolynomialSignCell

/-- Quantifier-free formulas are finite Boolean formulas in expression signs. -/
abbrev QuantifierFreeFormula (n : Nat) :=
  Math.PolynomialSignCell.SignFormula (RingExpression n)

/-- The exact signs of all rational expressions at a real environment. -/
noncomputable def realSignAssignment {n : Nat} (environment : Fin n → ℝ) :
    RingExpression n → SignType :=
  fun expression => SignType.sign (expression.evalReal environment)

namespace QuantifierFreeFormula

variable {n : Nat}

/-- Real truth semantics of a quantifier-free sign formula. -/
def HoldsAt (formula : QuantifierFreeFormula n) (environment : Fin n → ℝ) : Prop :=
  formula.Holds (realSignAssignment environment)

/-- Boolean evaluation after a sign assignment has been supplied. -/
def evalSigns
    (formula : QuantifierFreeFormula n)
    (signs : RingExpression n → SignType) : Bool :=
  formula.eval signs

@[simp]
theorem evalSigns_eq_true_iff
    (formula : QuantifierFreeFormula n)
    (signs : RingExpression n → SignType) :
    formula.evalSigns signs = true ↔ formula.Holds signs :=
  formula.eval_eq_true_iff signs

/-- The sign formula asserting that an expression is nonnegative. -/
def nonnegative (expression : RingExpression n) : QuantifierFreeFormula n :=
  .not (.atom expression .neg)

/-- The sign formula asserting that an expression is positive. -/
def positive (expression : RingExpression n) : QuantifierFreeFormula n :=
  .atom expression .pos

/-- The sign formula asserting that an expression is nonpositive. -/
def nonpositive (expression : RingExpression n) : QuantifierFreeFormula n :=
  .not (.atom expression .pos)

@[simp]
theorem holdsAt_nonnegative_iff
    (expression : RingExpression n) (environment : Fin n → ℝ) :
    (nonnegative expression).HoldsAt environment ↔
      0 ≤ expression.evalReal environment := by
  simp [nonnegative, HoldsAt, realSignAssignment, SignFormula.Holds,
    SignType.neg_eq_neg_one, sign_eq_neg_one_iff]

@[simp]
theorem holdsAt_positive_iff
    (expression : RingExpression n) (environment : Fin n → ℝ) :
    (positive expression).HoldsAt environment ↔
      0 < expression.evalReal environment := by
  simp [positive, HoldsAt, realSignAssignment, SignFormula.Holds,
    SignType.pos_eq_one, sign_eq_one_iff]

@[simp]
theorem holdsAt_nonpositive_iff
    (expression : RingExpression n) (environment : Fin n → ℝ) :
    (nonpositive expression).HoldsAt environment ↔
      expression.evalReal environment ≤ 0 := by
  simp [nonpositive, HoldsAt, realSignAssignment, SignFormula.Holds,
    SignType.pos_eq_one, sign_eq_one_iff]

end QuantifierFreeFormula

end MathUE.RealQuantifierElimination

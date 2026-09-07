import MathUE.Logic.SignFormula
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Real.Basic

/-! Semialgebraic sets as finite Boolean combinations of real polynomial sign sets. -/

namespace MathUE

/-- Boolean sign formulas over actual real-coefficient multivariate polynomials. -/
abbrev RealPolynomialSignFormula (n : ℕ) :=
  Math.PolynomialSignCell.SignFormula (MvPolynomial (Fin n) ℝ)

/-- Real truth semantics for a real-polynomial sign formula. -/
def RealPolynomialSignFormula.HoldsAt {n : ℕ} (formula : RealPolynomialSignFormula n)
    (environment : Fin n → ℝ) : Prop :=
  formula.Holds (fun p => SignType.sign (MvPolynomial.eval environment p))

/-- A semialgebraic set is a finite Boolean combination of real polynomial sign sets. -/
def IsSemialgebraic {n : ℕ} (set : Set (Fin n → ℝ)) : Prop :=
  ∃ formula : RealPolynomialSignFormula n, ∀ environment,
    environment ∈ set ↔ formula.HoldsAt environment

end MathUE

import MathUE.RealQuantifierElimination.CoefficientSignBranch
import MathUE.Logic.SignFormulaMap
import MathUE.Semialgebraic.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-! Rational sign syntax with fixed real coefficient parameters. -/

namespace MathUE

namespace RealQuantifierElimination

namespace QuantifierFreeFormula

/-- Rename free variables throughout a quantifier-free formula. -/
def rename {n m : ℕ} (indexMap : Fin n → Fin m) (formula : QuantifierFreeFormula n) :
    QuantifierFreeFormula m :=
  formula.mapAtoms (RingExpression.rename indexMap)

theorem holdsAt_rename {n m : ℕ} (indexMap : Fin n → Fin m)
    (formula : QuantifierFreeFormula n) (environment : Fin m → ℝ) :
    (formula.rename indexMap).HoldsAt environment ↔
      formula.HoldsAt (environment ∘ indexMap) := by
  rw [rename, HoldsAt, Math.PolynomialSignCell.SignFormula.holds_mapAtoms]
  have heq : realSignAssignment environment ∘ RingExpression.rename indexMap =
      realSignAssignment (environment ∘ indexMap) := by
    funext expression
    exact congrArg SignType.sign (RingExpression.evalReal_rename environment indexMap expression)
  rw [heq]
  rfl

end QuantifierFreeFormula

namespace RingExpression

/-- Substitute fixed real coefficient parameters, leaving the initial variables free. -/
noncomputable def specializeParameters {n k : ℕ} (parameters : Fin k → ℝ)
    (expression : RingExpression (n + k)) : MvPolynomial (Fin n) ℝ :=
  expression.eval (fun value => MvPolynomial.C (value : ℝ))
    (Fin.append MvPolynomial.X (fun index => MvPolynomial.C (parameters index)))

theorem eval_parameterPolynomialEnvironment {n k : ℕ} (parameters : Fin k → ℝ)
    (environment : Fin n → ℝ) (index : Fin (n + k)) :
    MvPolynomial.eval environment
        (Fin.append MvPolynomial.X (fun i => MvPolynomial.C (parameters i)) index) =
      Fin.append environment parameters index := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) index <;> simp

theorem eval_specializeParameters {n k : ℕ} (parameters : Fin k → ℝ)
    (expression : RingExpression (n + k)) (environment : Fin n → ℝ) :
    MvPolynomial.eval environment (expression.specializeParameters parameters) =
      expression.evalReal (Fin.append environment parameters) := by
  induction expression with
  | const value => simp [specializeParameters, eval, evalReal]
  | var index => exact eval_parameterPolynomialEnvironment parameters environment index
  | neg expression ih =>
      simpa only [specializeParameters, eval, map_neg, evalReal] using congrArg Neg.neg ih
  | add left right ihl ihr =>
      simpa only [specializeParameters, eval, map_add, evalReal] using
        congrArg₂ (fun a b : ℝ => a + b) ihl ihr
  | mul left right ihl ihr =>
      simpa only [specializeParameters, eval, map_mul, evalReal] using
        congrArg₂ (fun a b : ℝ => a * b) ihl ihr

end RingExpression

namespace QuantifierFreeFormula

/-- Fix real coefficient parameters in a rational formula, obtaining actual real polynomials. -/
noncomputable def specializeParameters {n k : ℕ} (parameters : Fin k → ℝ)
    (formula : QuantifierFreeFormula (n + k)) : RealPolynomialSignFormula n :=
  formula.mapAtoms (RingExpression.specializeParameters parameters)

theorem holdsAt_specializeParameters {n k : ℕ} (parameters : Fin k → ℝ)
    (formula : QuantifierFreeFormula (n + k)) (environment : Fin n → ℝ) :
    (formula.specializeParameters parameters).HoldsAt environment ↔
      formula.HoldsAt (Fin.append environment parameters) := by
  rw [specializeParameters, RealPolynomialSignFormula.HoldsAt,
    Math.PolynomialSignCell.SignFormula.holds_mapAtoms]
  have heq : (fun p => SignType.sign (MvPolynomial.eval environment p)) ∘
      RingExpression.specializeParameters parameters =
        realSignAssignment (Fin.append environment parameters) := by
    funext expression
    exact congrArg SignType.sign (expression.eval_specializeParameters parameters environment)
  rw [heq]
  rfl

theorem isSemialgebraic_fixed_parameters {n k : ℕ} (parameters : Fin k → ℝ)
    (formula : QuantifierFreeFormula (n + k)) :
    IsSemialgebraic {environment | formula.HoldsAt (Fin.append environment parameters)} := by
  exact ⟨formula.specializeParameters parameters,
    fun environment => (formula.holdsAt_specializeParameters parameters environment).symm⟩

end QuantifierFreeFormula
end RealQuantifierElimination
end MathUE

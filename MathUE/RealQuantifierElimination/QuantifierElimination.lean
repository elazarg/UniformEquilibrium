import MathUE.RealQuantifierElimination.OneVariableDiagramConsumer
import MathUE.RealQuantifierElimination.PolynomialFormula
import MathUE.RealQuantifierElimination.SignDiagramProducer

/-!
# Executable real polynomial quantifier elimination

The concrete Cohen--Hormander sign-diagram producer is consumed at each
existential step.  Structural recursion then eliminates arbitrary Boolean and
quantifier nesting, and closed formulas receive an executable Boolean decision.
-/

namespace MathUE.RealQuantifierElimination

open Math.PolynomialSignCell
open Math.PolynomialSignCell.SignFormula
open MathUE.OrderedRealSignDiagram

/-- Eliminate the real variable at index zero from a quantifier-free formula. -/
def eliminateOneVariable (formula : QuantifierFreeFormula (n + 1)) :
    QuantifierFreeFormula n :=
  existentialFromDiagramTree formula
    (signDiagram (formula.atoms.map RingExpression.toUnivariateDense))

/-- The concrete one-variable eliminator preserves existential real truth. -/
theorem eliminateOneVariable_holdsAt_iff
    (formula : QuantifierFreeFormula (n + 1)) (environment : Fin n → ℝ) :
    (eliminateOneVariable formula).HoldsAt environment ↔
      ∃ value : ℝ, formula.HoldsAt (Fin.cases value environment) := by
  apply existentialFromDiagramTree_holdsAt_iff
  intro parameters rows hselected
  have hdiagram := signDiagram_correct parameters
    (formula.atoms.map RingExpression.toUnivariateDense) rows hselected
  obtain ⟨cuts, hrealizes, _⟩ := hdiagram
  refine ⟨cuts, ?_⟩
  simpa only [QuantifierFreeFormula.univariateAtomPolynomials,
    specializeFamily, List.map_map, Function.comp_def] using hrealizes

/-- Eliminate every quantifier, retaining the same free variables. -/
def eliminateQuantifiers : {n : Nat} → PolynomialFormula n → QuantifierFreeFormula n
  | _, .atom expression expected => .atom expression expected
  | _, .top => .top
  | _, .bot => .bot
  | _, .and left right => .and (eliminateQuantifiers left) (eliminateQuantifiers right)
  | _, .or left right => .or (eliminateQuantifiers left) (eliminateQuantifiers right)
  | _, .not formula => .not (eliminateQuantifiers formula)
  | _, .ex body => eliminateOneVariable (eliminateQuantifiers body)
  | _, .all body => .not (eliminateOneVariable (.not (eliminateQuantifiers body)))

/-- Full structural quantifier elimination preserves real truth. -/
theorem eliminateQuantifiers_holdsAt_iff
    (formula : PolynomialFormula n) (environment : Fin n → ℝ) :
    (eliminateQuantifiers formula).HoldsAt environment ↔
      formula.HoldsAt environment := by
  induction formula with
  | atom expression expected =>
      rfl
  | top =>
      rfl
  | bot =>
      rfl
  | and left right ihLeft ihRight =>
      change ((eliminateQuantifiers left).HoldsAt environment ∧
          (eliminateQuantifiers right).HoldsAt environment) ↔
        left.HoldsAt environment ∧ right.HoldsAt environment
      exact and_congr (ihLeft environment) (ihRight environment)
  | or left right ihLeft ihRight =>
      change ((eliminateQuantifiers left).HoldsAt environment ∨
          (eliminateQuantifiers right).HoldsAt environment) ↔
        left.HoldsAt environment ∨ right.HoldsAt environment
      exact or_congr (ihLeft environment) (ihRight environment)
  | not formula ih =>
      change (¬(eliminateQuantifiers formula).HoldsAt environment) ↔
        ¬formula.HoldsAt environment
      exact not_congr (ih environment)
  | ex body ih =>
      rw [eliminateQuantifiers, eliminateOneVariable_holdsAt_iff]
      exact exists_congr fun value => ih (Fin.cases value environment)
  | all body ih =>
      change (¬(eliminateOneVariable (.not (eliminateQuantifiers body))).HoldsAt
          environment) ↔ ∀ value : ℝ, body.HoldsAt (Fin.cases value environment)
      rw [eliminateOneVariable_holdsAt_iff]
      change (¬∃ value : ℝ,
          ¬(eliminateQuantifiers body).HoldsAt (Fin.cases value environment)) ↔ _
      simp only [not_exists, not_not]
      exact forall_congr' fun value => ih (Fin.cases value environment)

/-- Execute the quantifier-free rational endpoint for a closed formula. -/
def decideClosedFormula (formula : PolynomialFormula 0) : Bool :=
  (eliminateQuantifiers formula).decideClosedQuantifierFree

/-- The executable closed decision is true exactly when the original real
sentence holds. -/
theorem decideClosedFormula_eq_true_iff (formula : PolynomialFormula 0) :
    decideClosedFormula formula = true ↔ formula.HoldsAt Fin.elim0 := by
  rw [decideClosedFormula, QuantifierFreeFormula.decideClosedQuantifierFree_eq_true_iff,
    eliminateQuantifiers_holdsAt_iff]

end MathUE.RealQuantifierElimination

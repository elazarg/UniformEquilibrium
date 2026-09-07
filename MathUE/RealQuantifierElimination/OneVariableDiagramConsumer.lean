import MathUE.Logic.SignFormulaFiniteAtoms
import MathUE.Polynomial.OrderedRealSignDiagram
import MathUE.RealQuantifierElimination.CoefficientSignBranch
import MathUE.RealQuantifierElimination.UnivariateCompilation

/-!
# Consume a realized one-variable sign diagram

This module turns actual realized sign rows into an existential truth value and
then compiles a coefficient-branch tree of such rows to a quantifier-free
formula.  It does not construct a sign diagram or assume a completed general
eliminator.
-/

namespace MathUE.RealQuantifierElimination

open Math.PolynomialSignCell
open Math.PolynomialSignCell.SignFormula
open MathUE.OrderedRealSignDiagram

namespace QuantifierFreeFormula

variable {n : Nat}

/-- The specialized real univariate polynomials for all atom occurrences, in
syntax order and with duplicates retained. -/
noncomputable def univariateAtomPolynomials
    (formula : QuantifierFreeFormula (n + 1)) (parameters : Fin n → ℝ) :
    List (Polynomial ℝ) :=
  formula.atoms.map fun expression =>
    Math.DensePolynomial.toPolynomial (RingExpression.realEvaluator parameters)
      expression.toUnivariateDense

/-- Whether at least one supplied sign row satisfies the formula. -/
def someRowSatisfies
    (formula : QuantifierFreeFormula (n + 1)) (rows : List (List SignType)) : Bool :=
  rows.any fun row => formula.evalRow row

theorem map_sign_eval_univariateAtomPolynomials
    (formula : QuantifierFreeFormula (n + 1)) (parameters : Fin n → ℝ) (x : ℝ) :
    (formula.univariateAtomPolynomials parameters).map
        (fun polynomial => SignType.sign (polynomial.eval x)) =
      formula.atoms.map (realSignAssignment (Fin.cases x parameters)) := by
  rw [univariateAtomPolynomials, List.map_map]
  apply List.map_congr_left
  intro expression hexpression
  simp only [Function.comp_apply, realSignAssignment]
  rw [RingExpression.toPolynomial_toUnivariateDense_eval]

theorem evalRow_eq_true_iff_of_RowOn
    (formula : QuantifierFreeFormula (n + 1)) (parameters : Fin n → ℝ)
    {cell : Set ℝ} {row : List SignType}
    (hrow : RowOn (formula.univariateAtomPolynomials parameters) cell row)
    {x : ℝ} (hx : x ∈ cell) :
    formula.evalRow row = true ↔
      formula.HoldsAt (Fin.cases x parameters) := by
  rw [hrow.eq_map_at hx, map_sign_eval_univariateAtomPolynomials,
    evalRow_map_atoms_eq_true_iff]
  rfl

private theorem exists_right_of_mem_left_forall₂
    {relation : α → β → Prop} {lefts : List α} {rights : List β}
    (hrel : List.Forall₂ relation lefts rights) {left : α} (hleft : left ∈ lefts) :
    ∃ right ∈ rights, relation left right := by
  induction hrel with
  | nil => simp at hleft
  | cons hhead htail ih =>
      rw [List.mem_cons] at hleft
      rcases hleft with rfl | hleft
      · exact ⟨_, by simp, hhead⟩
      · obtain ⟨right, hright, hrelation⟩ := ih hleft
        exact ⟨right, by simp [hright], hrelation⟩

private theorem exists_left_of_mem_right_forall₂
    {relation : α → β → Prop} {lefts : List α} {rights : List β}
    (hrel : List.Forall₂ relation lefts rights) {right : β} (hright : right ∈ rights) :
    ∃ left ∈ lefts, relation left right := by
  induction hrel with
  | nil => simp at hright
  | cons hhead htail ih =>
      rw [List.mem_cons] at hright
      rcases hright with rfl | hright
      · exact ⟨_, by simp, hhead⟩
      · obtain ⟨left, hleft, hrelation⟩ := ih hright
        exact ⟨left, by simp [hleft], hrelation⟩

/-- A realized diagram's finite row scan is true exactly when the original
formula has a real witness for its variable at index zero. -/
theorem someRowSatisfies_eq_true_iff_of_realizes
    (formula : QuantifierFreeFormula (n + 1)) (parameters : Fin n → ℝ)
    (rows : List (List SignType))
    (hrealizes : Realizes (formula.univariateAtomPolynomials parameters) rows) :
    formula.someRowSatisfies rows = true ↔
      ∃ x : ℝ, formula.HoldsAt (Fin.cases x parameters) := by
  obtain ⟨cuts, hordered, hrows⟩ := hrealizes
  constructor
  · intro hsatisfies
    rw [someRowSatisfies, List.any_eq_true] at hsatisfies
    obtain ⟨row, hrowMem, hrowTrue⟩ := hsatisfies
    obtain ⟨cell, hcellMem, hrow⟩ :=
      exists_left_of_mem_right_forall₂ hrows hrowMem
    obtain ⟨x, hx⟩ := cellsFrom_nonempty hordered cell hcellMem
    exact ⟨x, (evalRow_eq_true_iff_of_RowOn formula parameters hrow hx).mp hrowTrue⟩
  · rintro ⟨x, hx⟩
    obtain ⟨cell, hcellMem, hxCell⟩ := (cellsFrom_cover hordered x).mpr trivial
    obtain ⟨row, hrowMem, hrow⟩ :=
      exists_right_of_mem_left_forall₂ hrows hcellMem
    rw [someRowSatisfies, List.any_eq_true]
    exact ⟨row, hrowMem,
      (evalRow_eq_true_iff_of_RowOn formula parameters hrow hxCell).mpr hx⟩

end QuantifierFreeFormula

/-- Compile a coefficient-sign tree of realized one-variable diagrams into a
quantifier-free formula on the remaining parameters. -/
def existentialFromDiagramTree
    (formula : QuantifierFreeFormula (n + 1))
    (tree : CoefficientSignBranch n (List (List SignType))) :
    QuantifierFreeFormula n :=
  (tree.map fun rows =>
    if formula.someRowSatisfies rows then SignFormula.top else SignFormula.bot).compile

/-- Correctness of the explicit one-variable diagram-tree consumer.  The only
input certificate is realization of every actually selected leaf. -/
theorem existentialFromDiagramTree_holdsAt_iff
    (formula : QuantifierFreeFormula (n + 1))
    (tree : CoefficientSignBranch n (List (List SignType)))
    (hrealizes : ∀ (parameters : Fin n → ℝ) rows,
      tree.Selects parameters rows →
        OrderedRealSignDiagram.Realizes
          (formula.univariateAtomPolynomials parameters) rows)
    (parameters : Fin n → ℝ) :
    (existentialFromDiagramTree formula tree).HoldsAt parameters ↔
      ∃ x : ℝ, formula.HoldsAt (Fin.cases x parameters) := by
  rw [existentialFromDiagramTree, CoefficientSignBranch.compile_holdsAt_iff_exists]
  constructor
  · rintro ⟨leaf, hleaf, htruth⟩
    rw [CoefficientSignBranch.selects_map_iff] at hleaf
    obtain ⟨rows, hrows, rfl⟩ := hleaf
    by_cases hsatisfies : formula.someRowSatisfies rows = true
    · exact (formula.someRowSatisfies_eq_true_iff_of_realizes parameters rows
        (hrealizes parameters rows hrows)).mp hsatisfies
    · simp [hsatisfies, QuantifierFreeFormula.HoldsAt, SignFormula.Holds] at htruth
  · intro hexists
    obtain ⟨rows, hrows, _⟩ := tree.existsUnique_selects parameters
    have hsatisfies : formula.someRowSatisfies rows = true :=
      (formula.someRowSatisfies_eq_true_iff_of_realizes parameters rows
        (hrealizes parameters rows hrows)).mpr hexists
    refine ⟨SignFormula.top, ?_, ?_⟩
    · rw [CoefficientSignBranch.selects_map_iff]
      exact ⟨rows, hrows, by simp [hsatisfies]⟩
    · trivial

end MathUE.RealQuantifierElimination

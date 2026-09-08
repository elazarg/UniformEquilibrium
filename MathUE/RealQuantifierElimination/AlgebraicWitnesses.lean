import MathUE.RealQuantifierElimination.AlgebraicEvaluation
import MathUE.RealQuantifierElimination.QuantifierElimination
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Algebra.Algebra.Rat

/-! # Algebraic witnesses for rational sign formulas -/

namespace MathUE.OrderedRealSignDiagram

/-- A finite endpoint is algebraic; an infinite endpoint has no condition. -/
def EndpointIsAlgebraic : Option ℝ → Prop
  | none => True
  | some value => IsAlgebraic ℚ value

/-- Every nonempty open cell with algebraic finite endpoints contains an
algebraic point. -/
theorem openCell_exists_isAlgebraic
    {lower upper : Option ℝ}
    (hlower : EndpointIsAlgebraic lower)
    (hupper : EndpointIsAlgebraic upper)
    (hnonempty : (openCell lower upper).Nonempty) :
    ∃ value ∈ openCell lower upper, IsAlgebraic ℚ value := by
  cases lower with
  | none =>
      cases upper with
      | none =>
          exact ⟨0, by trivial, isAlgebraic_zero⟩
      | some upper =>
          refine ⟨upper - 1, ?_, hupper.sub isAlgebraic_one⟩
          exact ⟨trivial, by dsimp [Below]; linarith⟩
  | some lower =>
      cases upper with
      | none =>
          refine ⟨lower + 1, ?_, hlower.add isAlgebraic_one⟩
          exact ⟨by dsimp [Above]; linarith, trivial⟩
      | some upper =>
          obtain ⟨sample, hsample⟩ := hnonempty
          refine ⟨(1 / 2 : ℚ) • (lower + upper), ?_,
            (hlower.add hupper).smul (1 / 2 : ℚ)⟩
          dsimp [openCell, Above, Below] at hsample ⊢
          rw [Algebra.smul_def]
          norm_num
          constructor <;> linarith

/-- Every cell in an ordered decomposition with algebraic cuts contains an
algebraic point. -/
theorem cellsFrom_exists_isAlgebraic
    {lower : Option ℝ} {cuts : List ℝ}
    (hordered : OrderedFrom lower cuts)
    (hlower : EndpointIsAlgebraic lower)
    (hcuts : ∀ cut ∈ cuts, IsAlgebraic ℚ cut) :
    ∀ cell ∈ cellsFrom lower cuts,
      ∃ value ∈ cell, IsAlgebraic ℚ value := by
  induction cuts generalizing lower with
  | nil =>
      intro cell hcell
      have hcellEq : cell = openCell lower none := by
        simpa only [cellsFrom, List.mem_singleton] using hcell
      subst cell
      exact openCell_exists_isAlgebraic hlower trivial
        (openCell_right_nonempty lower)
  | cons cut cuts ih =>
      intro cell hcell
      rcases List.mem_cons.mp hcell with rfl | hcell
      · exact openCell_exists_isAlgebraic hlower
          (hcuts cut (List.mem_cons_self))
          (openCell_left_nonempty hordered.1)
      · rcases List.mem_cons.mp hcell with rfl | hcell
        · exact ⟨cut, Set.mem_singleton cut,
            hcuts cut (List.mem_cons_self)⟩
        · exact ih hordered.2
            (hcuts cut (List.mem_cons_self))
            (fun other hother => hcuts other (List.mem_cons_of_mem cut hother))
            cell hcell

/-- Whole-line specialization of `cellsFrom_exists_isAlgebraic`. -/
theorem cellsFrom_none_exists_isAlgebraic
    {cuts : List ℝ} (hordered : OrderedFrom none cuts)
    (hcuts : ∀ cut ∈ cuts, IsAlgebraic ℚ cut) :
    ∀ cell ∈ cellsFrom none cuts,
      ∃ value ∈ cell, IsAlgebraic ℚ value :=
  cellsFrom_exists_isAlgebraic hordered trivial hcuts

end MathUE.OrderedRealSignDiagram

namespace MathUE.RealQuantifierElimination

open Math.PolynomialSignCell
open MathUE.OrderedRealSignDiagram

private theorem exists_left_of_mem_right_forall₂
    {relation : α → β → Prop} {lefts : List α} {rights : List β}
    (hrelation : List.Forall₂ relation lefts rights)
    {right : β} (hright : right ∈ rights) :
    ∃ left ∈ lefts, relation left right := by
  induction hrelation with
  | nil => simp at hright
  | cons hhead htail ih =>
      rw [List.mem_cons] at hright
      rcases hright with rfl | hright
      · exact ⟨_, by simp, hhead⟩
      · obtain ⟨left, hleft, hrelation⟩ := ih hright
        exact ⟨left, by simp [hleft], hrelation⟩

namespace QuantifierFreeFormula

private theorem univariateAtomPolynomial_coeff_isAlgebraic
    (formula : QuantifierFreeFormula (n + 1))
    (parameters : Fin n → ℝ)
    (hparameters : ∀ index, IsAlgebraic ℚ (parameters index))
    {polynomial : Polynomial ℝ}
    (hpolynomial : polynomial ∈ formula.univariateAtomPolynomials parameters)
    (degree : ℕ) :
    IsAlgebraic ℚ (polynomial.coeff degree) := by
  rw [univariateAtomPolynomials] at hpolynomial
  obtain ⟨expression, _, rfl⟩ := List.mem_map.mp hpolynomial
  exact Math.DensePolynomial.toPolynomial_realEvaluator_coeff_isAlgebraic
    parameters hparameters expression.toUnivariateDense degree

/-- A reduced sign diagram scans true exactly when the rational formula has
an algebraic witness for its bound variable, provided the parameters are
algebraic. -/
theorem someRowSatisfies_eq_true_iff_exists_isAlgebraic_of_reducedRealizes
    (formula : QuantifierFreeFormula (n + 1))
    (parameters : Fin n → ℝ)
    (hparameters : ∀ index, IsAlgebraic ℚ (parameters index))
    (rows : List (List SignType))
    (hrealizes : ReducedRealizes (formula.univariateAtomPolynomials parameters) rows) :
    formula.someRowSatisfies rows = true ↔
      ∃ value : ℝ, IsAlgebraic ℚ value ∧
        formula.HoldsAt (Fin.cases value parameters) := by
  obtain ⟨cuts, hrealizesFrom, hroots⟩ := hrealizes
  have hcuts : ∀ cut ∈ cuts, IsAlgebraic ℚ cut := by
    intro cut hcut
    obtain ⟨polynomial, hpolynomial, hnonzero, hroot⟩ := (hroots cut).mp hcut
    exact Polynomial.isAlgebraic_of_eval_eq_zero_of_coeff_isAlgebraic
      polynomial hnonzero
      (univariateAtomPolynomial_coeff_isAlgebraic formula parameters hparameters
        hpolynomial)
      hroot
  constructor
  · intro hsatisfies
    rw [someRowSatisfies, List.any_eq_true] at hsatisfies
    obtain ⟨row, hrow, htrue⟩ := hsatisfies
    obtain ⟨cell, hcell, hrowOn⟩ :=
      exists_left_of_mem_right_forall₂ hrealizesFrom.2 hrow
    obtain ⟨value, hvalue, halgebraic⟩ :=
      cellsFrom_none_exists_isAlgebraic hrealizesFrom.1 hcuts cell hcell
    exact ⟨value, halgebraic,
      (evalRow_eq_true_iff_of_RowOn formula parameters hrowOn hvalue).mp htrue⟩
  · rintro ⟨value, _, hformula⟩
    exact (someRowSatisfies_eq_true_iff_of_realizes formula parameters rows
      ⟨cuts, hrealizesFrom⟩).mpr ⟨value, hformula⟩

end QuantifierFreeFormula

/-- One-variable elimination has an algebraic witness whenever its fixed
parameter environment is algebraic. -/
theorem eliminateOneVariable_holdsAt_iff_exists_isAlgebraic
    (formula : QuantifierFreeFormula (n + 1))
    (parameters : Fin n → ℝ)
    (hparameters : ∀ index, IsAlgebraic ℚ (parameters index)) :
    (eliminateOneVariable formula).HoldsAt parameters ↔
      ∃ value : ℝ, IsAlgebraic ℚ value ∧
        formula.HoldsAt (Fin.cases value parameters) := by
  constructor
  · intro heliminated
    have hexists := (eliminateOneVariable_holdsAt_iff formula parameters).mp heliminated
    let family := formula.atoms.map RingExpression.toUnivariateDense
    obtain ⟨rows, hrows, _⟩ := (signDiagram family).existsUnique_selects parameters
    have hdiagram := signDiagram_correct parameters family rows hrows
    have hrealizes :
        ReducedRealizes (formula.univariateAtomPolynomials parameters) rows := by
      simpa only [QuantifierFreeFormula.univariateAtomPolynomials,
        specializeFamily, family, List.map_map, Function.comp_def] using hdiagram
    have hrealizesPlain :
        Realizes (formula.univariateAtomPolynomials parameters) rows := by
      obtain ⟨cuts, hrealizesFrom, _⟩ := hrealizes
      exact ⟨cuts, hrealizesFrom⟩
    have hsatisfies : formula.someRowSatisfies rows = true :=
      (formula.someRowSatisfies_eq_true_iff_of_realizes parameters rows
        hrealizesPlain).mpr
        hexists
    exact
      (formula.someRowSatisfies_eq_true_iff_exists_isAlgebraic_of_reducedRealizes
        parameters hparameters rows hrealizes).mp hsatisfies
  · rintro ⟨value, _, hformula⟩
    exact (eliminateOneVariable_holdsAt_iff formula parameters).mpr ⟨value, hformula⟩

namespace QuantifierFreeFormula

/-- Every inhabited rational sign condition has a satisfying environment
whose real coordinates are all algebraic over the rationals. -/
theorem exists_isAlgebraic_environment_of_exists_holdsAt
    (formula : QuantifierFreeFormula n)
    (hexists : ∃ environment : Fin n → ℝ, formula.HoldsAt environment) :
    ∃ environment : Fin n → ℝ,
      (∀ index, IsAlgebraic ℚ (environment index)) ∧
        formula.HoldsAt environment := by
  induction n with
  | zero =>
      obtain ⟨environment, hformula⟩ := hexists
      refine ⟨Fin.elim0, fun index => Fin.elim0 index, ?_⟩
      have henvironment : environment = Fin.elim0 := Subsingleton.elim _ _
      rwa [← henvironment]
  | succ n ih =>
      obtain ⟨environment, hformula⟩ := hexists
      let parameters : Fin n → ℝ := fun index => environment index.succ
      have henvironment : Fin.cases (environment 0) parameters = environment := by
        funext index
        refine Fin.cases ?_ (fun parameter => ?_) index
        · rfl
        · rfl
      have heliminated : (eliminateOneVariable formula).HoldsAt parameters := by
        apply (eliminateOneVariable_holdsAt_iff formula parameters).mpr
        exact ⟨environment 0, henvironment ▸ hformula⟩
      obtain ⟨algebraicParameters, hparameters, heliminated⟩ :=
        ih (eliminateOneVariable formula) ⟨parameters, heliminated⟩
      obtain ⟨value, hvalue, hformula⟩ :=
        (eliminateOneVariable_holdsAt_iff_exists_isAlgebraic formula
          algebraicParameters hparameters).mp heliminated
      refine ⟨Fin.cases value algebraicParameters, ?_, hformula⟩
      intro index
      exact Fin.cases hvalue hparameters index

/-- Existence over the reals is equivalent to existence of a coordinatewise
real-algebraic satisfying environment. -/
theorem exists_isAlgebraic_environment_iff
    (formula : QuantifierFreeFormula n) :
    (∃ environment : Fin n → ℝ, formula.HoldsAt environment) ↔
      ∃ environment : Fin n → ℝ,
        (∀ index, IsAlgebraic ℚ (environment index)) ∧
          formula.HoldsAt environment := by
  constructor
  · exact formula.exists_isAlgebraic_environment_of_exists_holdsAt
  · rintro ⟨environment, _, hformula⟩
    exact ⟨environment, hformula⟩

end QuantifierFreeFormula

end MathUE.RealQuantifierElimination

namespace MathUE.RealQuantifierElimination.PolynomialFormula

/-- Every inhabited first-order rational polynomial formula has a satisfying
environment whose real coordinates are all algebraic over the rationals. -/
theorem exists_isAlgebraic_environment_of_exists_holdsAt
    (formula : PolynomialFormula n)
    (hexists : ∃ environment : Fin n → ℝ, formula.HoldsAt environment) :
    ∃ environment : Fin n → ℝ,
      (∀ index, IsAlgebraic ℚ (environment index)) ∧
        formula.HoldsAt environment := by
  have heliminated :
      ∃ environment : Fin n → ℝ,
        (eliminateQuantifiers formula).HoldsAt environment := by
    obtain ⟨environment, hformula⟩ := hexists
    exact ⟨environment,
      (eliminateQuantifiers_holdsAt_iff formula environment).mpr hformula⟩
  obtain ⟨environment, halgebraic, heliminated⟩ :=
    QuantifierFreeFormula.exists_isAlgebraic_environment_of_exists_holdsAt
      (eliminateQuantifiers formula) heliminated
  exact ⟨environment, halgebraic,
    (eliminateQuantifiers_holdsAt_iff formula environment).mp heliminated⟩

/-- Existence over the reals for a first-order rational polynomial formula is
equivalent to existence of a coordinatewise real-algebraic environment. -/
theorem exists_isAlgebraic_environment_iff
    (formula : PolynomialFormula n) :
    (∃ environment : Fin n → ℝ, formula.HoldsAt environment) ↔
      ∃ environment : Fin n → ℝ,
        (∀ index, IsAlgebraic ℚ (environment index)) ∧
          formula.HoldsAt environment := by
  constructor
  · exact formula.exists_isAlgebraic_environment_of_exists_holdsAt
  · rintro ⟨environment, _, hformula⟩
    exact ⟨environment, hformula⟩

end MathUE.RealQuantifierElimination.PolynomialFormula

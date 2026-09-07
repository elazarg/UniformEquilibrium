import MathUE.RealQuantifierElimination.QuantifierElimination
import MathUE.Logic.SignFormulaFiniteFolds

/-!
# Certified isolated real roots as exact decision parameters

The executable payload consists only of rational coefficients and rational
interval endpoints. Real values occur in semantics, never in executable input.
Validity is checked by the proved rational-formula quantifier eliminator.
-/

namespace MathUE.RealQuantifierElimination

open Math.PolynomialSignCell

/-- Rational ascending coefficients and an open isolating interval. -/
structure IsolatedRealRootData where
  coefficients : List ℚ
  lower : ℚ
  upper : ℚ
  deriving DecidableEq, Repr

namespace IsolatedRealRootData

/-- The real polynomial value, used only for the specification. -/
noncomputable def evalAt (data : IsolatedRealRootData) (value : ℝ) : ℝ :=
  data.coefficients.foldr (fun coefficient tail => (coefficient : ℝ) + value * tail) 0

/-- The specified real is a root strictly inside the supplied interval. -/
def RootWithin (data : IsolatedRealRootData) (value : ℝ) : Prop :=
  (data.lower : ℝ) < value ∧ value < (data.upper : ℝ) ∧ data.evalAt value = 0

/-- A valid encoding has exactly one distinct real root in its open interval.
Repeated polynomial roots are permitted. -/
def IsValid (data : IsolatedRealRootData) : Prop :=
  ∃! value : ℝ, data.RootWithin value

/-- Compile the coefficient list by Horner's rule at an arbitrary expression. -/
def polynomialExpression {n : Nat} (data : IsolatedRealRootData)
    (expression : RingExpression n) : RingExpression n :=
  data.coefficients.foldr (fun coefficient tail =>
    RingExpression.const coefficient + expression * tail) 0

theorem evalReal_polynomialExpression {n : Nat} (data : IsolatedRealRootData)
    (expression : RingExpression n) (environment : Fin n → ℝ) :
    (data.polynomialExpression expression).evalReal environment =
      data.evalAt (expression.evalReal environment) := by
  rcases data with ⟨coefficients, lower, upper⟩
  induction coefficients with
  | nil => simp [polynomialExpression, evalAt]
  | cons coefficient coefficients ih =>
      simp only [polynomialExpression, List.foldr_cons, RingExpression.evalReal_add,
        RingExpression.evalReal_const, RingExpression.evalReal_mul, evalAt]
      exact congrArg (fun tail => (coefficient : ℝ) + expression.evalReal environment * tail) ih

/-- A rational sign formula asserting membership in the specified root interval. -/
def rootConstraint {n : Nat} (data : IsolatedRealRootData)
    (expression : RingExpression n) : QuantifierFreeFormula n :=
  .and (QuantifierFreeFormula.positive (expression + -RingExpression.const data.lower))
    (.and (QuantifierFreeFormula.positive (RingExpression.const data.upper + -expression))
      (.atom (data.polynomialExpression expression) 0))

theorem holdsAt_rootConstraint_iff {n : Nat} (data : IsolatedRealRootData)
    (expression : RingExpression n) (environment : Fin n → ℝ) :
    (data.rootConstraint expression).HoldsAt environment ↔
      data.RootWithin (expression.evalReal environment) := by
  simp [rootConstraint, QuantifierFreeFormula.HoldsAt, QuantifierFreeFormula.positive,
    SignFormula.Holds, realSignAssignment, evalReal_polynomialExpression,
    RootWithin, SignType.pos_eq_one, sign_eq_one_iff, sign_eq_zero_iff,
    ← sub_eq_add_neg, sub_pos]

/-- A closed rational formula checking existence and uniqueness of the selected root. -/
def validityFormula (data : IsolatedRealRootData) : PolynomialFormula 0 :=
  .ex (.and (PolynomialFormula.ofQuantifierFree (data.rootConstraint (.var 0)))
    (.all (.or
      (.not (PolynomialFormula.ofQuantifierFree (data.rootConstraint (.var 0))))
      (.atom (RingExpression.var 0 + -RingExpression.var 1) 0))))

theorem validityFormula_holdsAt_iff (data : IsolatedRealRootData) :
    data.validityFormula.HoldsAt Fin.elim0 ↔ data.IsValid := by
  change (∃ value : ℝ,
    (PolynomialFormula.ofQuantifierFree (data.rootConstraint (.var 0))).HoldsAt
      (Fin.cons value Fin.elim0) ∧
    ∀ other : ℝ,
      ¬(PolynomialFormula.ofQuantifierFree (data.rootConstraint (.var 0))).HoldsAt
        (Fin.cons other (Fin.cons value Fin.elim0)) ∨
      SignType.sign ((RingExpression.var 0 + -RingExpression.var 1).evalReal
        (Fin.cons other (Fin.cons value Fin.elim0))) = 0) ↔ _
  simp only [PolynomialFormula.holdsAt_ofQuantifierFree_iff,
    holdsAt_rootConstraint_iff, RingExpression.evalReal_var, Fin.cons_zero,
    RingExpression.evalReal_add, RingExpression.evalReal_neg, Fin.cons_one,
    sign_eq_zero_iff, add_neg_eq_zero, ← imp_iff_not_or]
  rfl

/-- Executable validation, including root existence and uniqueness. -/
def validate (data : IsolatedRealRootData) : Bool :=
  decideClosedFormula data.validityFormula

theorem validate_eq_true_iff (data : IsolatedRealRootData) :
    data.validate = true ↔ data.IsValid := by
  rw [validate, decideClosedFormula_eq_true_iff, validityFormula_holdsAt_iff]

end IsolatedRealRootData

/-- A rational root description together with its kernel-checked validity proof. -/
structure CertifiedIsolatedRealRoot where
  data : IsolatedRealRootData
  valid : data.IsValid

/-- Certified parameters always denote a simultaneous real environment. -/
theorem exists_isolatedRootParameterEnvironment {n : Nat}
    (parameters : Fin n → CertifiedIsolatedRealRoot) :
    ∃ environment : Fin n → ℝ, ∀ index, (parameters index).data.RootWithin (environment index) := by
  classical
  choose environment hroot using fun index => (parameters index).valid.exists
  exact ⟨environment, hroot⟩

/-- Validate a raw description and, on success, produce the certified input. -/
def certifyIsolatedRealRoot (data : IsolatedRealRootData) : Option CertifiedIsolatedRealRoot :=
  if h : data.validate = true then
    some ⟨data, data.validate_eq_true_iff.mp h⟩
  else none

theorem certifyIsolatedRealRoot_isSome_iff (data : IsolatedRealRootData) :
    (certifyIsolatedRealRoot data).isSome = true ↔ data.IsValid := by
  unfold certifyIsolatedRealRoot
  split_ifs with h
  · simp only [Option.isSome_some, true_iff]
    exact data.validate_eq_true_iff.mp h
  · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    exact fun hvalid => h (data.validate_eq_true_iff.mpr hvalid)

/-- Constrain every free parameter to its individually certified real root. -/
def isolatedRootParameterConstraints {n : Nat}
    (parameters : Fin n → CertifiedIsolatedRealRoot) : QuantifierFreeFormula n :=
  SignFormula.conjunction (List.ofFn fun index =>
    (parameters index).data.rootConstraint (.var index))

theorem holdsAt_isolatedRootParameterConstraints_iff {n : Nat}
    (parameters : Fin n → CertifiedIsolatedRealRoot) (environment : Fin n → ℝ) :
    (isolatedRootParameterConstraints parameters).HoldsAt environment ↔
      ∀ index, (parameters index).data.RootWithin (environment index) := by
  change (SignFormula.conjunction _).Holds (realSignAssignment environment) ↔ _
  rw [SignFormula.holds_conjunction_iff]
  simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff]
  change (∀ index, ((parameters index).data.rootConstraint (.var index)).HoldsAt environment) ↔ _
  simp only [IsolatedRealRootData.holdsAt_rootConstraint_iff, RingExpression.evalReal_var]

/-- Bind all isolated-root parameters, preserving arbitrary quantifiers already in the formula. -/
def isolatedRootParameterSentence {n : Nat}
    (parameters : Fin n → CertifiedIsolatedRealRoot) (formula : PolynomialFormula n) :
    PolynomialFormula 0 :=
  (PolynomialFormula.or
    (.not (.ofQuantifierFree (isolatedRootParameterConstraints parameters)))
      formula).universallyClose

/-- Exact executable rational-QE decision with certified real-algebraic parameters. -/
def decideAtIsolatedRoots {n : Nat}
    (parameters : Fin n → CertifiedIsolatedRealRoot) (formula : PolynomialFormula n) : Bool :=
  decideClosedFormula (isolatedRootParameterSentence parameters formula)

/-- Decision correctness is stated at any real environment denoted by the inputs;
the executable procedure never reads or compares these real values. -/
theorem decideAtIsolatedRoots_eq_true_iff {n : Nat}
    (parameters : Fin n → CertifiedIsolatedRealRoot) (formula : PolynomialFormula n)
    (environment : Fin n → ℝ)
    (hroots : ∀ index, (parameters index).data.RootWithin (environment index)) :
    decideAtIsolatedRoots parameters formula = true ↔ formula.HoldsAt environment := by
  rw [decideAtIsolatedRoots, decideClosedFormula_eq_true_iff,
    isolatedRootParameterSentence, PolynomialFormula.holdsAt_universallyClose_iff]
  change (∀ candidate : Fin n → ℝ,
    ¬(PolynomialFormula.ofQuantifierFree
      (isolatedRootParameterConstraints parameters)).HoldsAt candidate ∨
      formula.HoldsAt candidate) ↔ _
  simp only [PolynomialFormula.holdsAt_ofQuantifierFree_iff,
    holdsAt_isolatedRootParameterConstraints_iff, ← imp_iff_not_or]
  constructor
  · intro h
    exact h environment hroots
  · intro hformula candidate hcandidate
    have heq : candidate = environment := by
      funext index
      exact (parameters index).valid.unique (hcandidate index) (hroots index)
    rwa [heq]

/-- A closed correctness statement requiring no separately supplied real environment. -/
theorem decideAtIsolatedRoots_eq_true_iff_exists {n : Nat}
    (parameters : Fin n → CertifiedIsolatedRealRoot) (formula : PolynomialFormula n) :
    decideAtIsolatedRoots parameters formula = true ↔
      ∃ environment : Fin n → ℝ,
        (∀ index, (parameters index).data.RootWithin (environment index)) ∧
          formula.HoldsAt environment := by
  obtain ⟨environment, hroots⟩ := exists_isolatedRootParameterEnvironment parameters
  rw [decideAtIsolatedRoots_eq_true_iff parameters formula environment hroots]
  constructor
  · intro hformula
    exact ⟨environment, hroots, hformula⟩
  · rintro ⟨candidate, hcandidate, hformula⟩
    have heq : candidate = environment := by
      funext index
      exact (parameters index).valid.unique (hcandidate index) (hroots index)
    rwa [heq] at hformula

end MathUE.RealQuantifierElimination

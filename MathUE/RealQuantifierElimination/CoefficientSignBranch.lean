import MathUE.RealQuantifierElimination.QuantifierFreeFormula

/-! # Symbolic coefficient-sign branches

Finite sign-test trees compile to Boolean formulas while preserving truth
at every real environment. These operations do not construct sign diagrams
or eliminate quantifiers.
-/

namespace MathUE.RealQuantifierElimination

/-- A finite decision tree branching on the sign of symbolic coefficients. -/
inductive CoefficientSignBranch (n : Nat) (α : Type*)
  | leaf (value : α)
  | test (coefficient : RingExpression n)
      (negative zero positive : CoefficientSignBranch n α)
  deriving DecidableEq, Repr

namespace CoefficientSignBranch

variable {n : Nat} {α β : Type*}

/-- A real environment selects a leaf by following its coefficient signs. -/
def Selects (environment : Fin n → ℝ) :
    CoefficientSignBranch n α → α → Prop
  | .leaf value, selected => selected = value
  | .test coefficient negative zero positive, selected =>
      match SignType.sign (coefficient.evalReal environment) with
      | .neg => negative.Selects environment selected
      | .zero => zero.Selects environment selected
      | .pos => positive.Selects environment selected

/-- Every environment selects exactly one value. -/
theorem existsUnique_selects
    (tree : CoefficientSignBranch n α) (environment : Fin n → ℝ) :
    ∃! selected, tree.Selects environment selected := by
  induction tree with
  | leaf value =>
      exact ⟨value, rfl, fun selected hselected => hselected⟩
  | test coefficient negative zero positive hnegative hzero hpositive =>
      cases hsign : SignType.sign (coefficient.evalReal environment) with
      | neg => simpa [Selects, hsign] using hnegative
      | zero => simpa [Selects, hsign] using hzero
      | pos => simpa [Selects, hsign] using hpositive

/-- Functorial action on coefficient-sign branch leaves. -/
def map (function : α → β) :
    CoefficientSignBranch n α → CoefficientSignBranch n β
  | .leaf value => .leaf (function value)
  | .test coefficient negative zero positive =>
      .test coefficient (negative.map function) (zero.map function)
        (positive.map function)

/-- Monadic substitution at coefficient-sign branch leaves. -/
def bind (tree : CoefficientSignBranch n α)
    (function : α → CoefficientSignBranch n β) : CoefficientSignBranch n β :=
  match tree with
  | .leaf value => function value
  | .test coefficient negative zero positive =>
      .test coefficient (negative.bind function) (zero.bind function)
        (positive.bind function)

@[simp]
theorem selects_map_iff
    (tree : CoefficientSignBranch n α) (function : α → β)
    (environment : Fin n → ℝ) (selected : β) :
    (tree.map function).Selects environment selected ↔
      ∃ value, tree.Selects environment value ∧ selected = function value := by
  induction tree with
  | leaf value => simp [map, Selects]
  | test coefficient negative zero positive hnegative hzero hpositive =>
      cases hsign : SignType.sign (coefficient.evalReal environment) with
      | neg => simpa [map, Selects, hsign] using hnegative
      | zero => simpa [map, Selects, hsign] using hzero
      | pos => simpa [map, Selects, hsign] using hpositive

@[simp]
theorem selects_bind_iff
    (tree : CoefficientSignBranch n α)
    (function : α → CoefficientSignBranch n β)
    (environment : Fin n → ℝ) (selected : β) :
    (tree.bind function).Selects environment selected ↔
      ∃ value, tree.Selects environment value ∧
        (function value).Selects environment selected := by
  induction tree with
  | leaf value => simp [bind, Selects]
  | test coefficient negative zero positive hnegative hzero hpositive =>
      cases hsign : SignType.sign (coefficient.evalReal environment) with
      | neg => simpa [bind, Selects, hsign] using hnegative
      | zero => simpa [bind, Selects, hsign] using hzero
      | pos => simpa [bind, Selects, hsign] using hpositive

/-- Replace each leaf by the same fixed value. -/
def replace (tree : CoefficientSignBranch n α) (value : β) :
    CoefficientSignBranch n β :=
  tree.map fun _ => value

/-- Compile a sign-branch tree with formula leaves to guarded disjunctions. -/
def compile :
    CoefficientSignBranch n (QuantifierFreeFormula n) → QuantifierFreeFormula n
  | .leaf formula => formula
  | .test coefficient negative zero positive =>
      .or (.and (.atom coefficient .neg) negative.compile)
        (.or (.and (.atom coefficient .zero) zero.compile)
          (.and (.atom coefficient .pos) positive.compile))

/-- A compiled guarded disjunction is true exactly when its selected leaf is true. -/
theorem compile_holdsAt_iff_exists
    (tree : CoefficientSignBranch n (QuantifierFreeFormula n))
    (environment : Fin n → ℝ) :
    tree.compile.HoldsAt environment ↔
      ∃ formula, tree.Selects environment formula ∧ formula.HoldsAt environment := by
  induction tree with
  | leaf formula => simp [compile, Selects, QuantifierFreeFormula.HoldsAt]
  | test coefficient negative zero positive hnegative hzero hpositive =>
      cases hsign : SignType.sign (coefficient.evalReal environment) with
      | neg =>
          simpa [compile, Selects, QuantifierFreeFormula.HoldsAt,
            Math.PolynomialSignCell.SignFormula.Holds,
            realSignAssignment, hsign] using hnegative
      | zero =>
          simpa [compile, Selects, QuantifierFreeFormula.HoldsAt,
            Math.PolynomialSignCell.SignFormula.Holds,
            realSignAssignment, hsign] using hzero
      | pos =>
          simpa [compile, Selects, QuantifierFreeFormula.HoldsAt,
            Math.PolynomialSignCell.SignFormula.Holds,
            realSignAssignment, hsign] using hpositive

/-- Universal form of truth preservation, equivalent by unique selection. -/
theorem compile_holdsAt_iff_forall
    (tree : CoefficientSignBranch n (QuantifierFreeFormula n))
    (environment : Fin n → ℝ) :
    tree.compile.HoldsAt environment ↔
      ∀ formula, tree.Selects environment formula → formula.HoldsAt environment := by
  rw [compile_holdsAt_iff_exists]
  obtain ⟨selected, hselected, hunique⟩ := tree.existsUnique_selects environment
  constructor
  · rintro ⟨formula, hformula, htruth⟩ other hother
    simpa [hunique other hother, hunique formula hformula] using htruth
  · intro hall
    exact ⟨selected, hselected, hall selected hselected⟩

end CoefficientSignBranch
end MathUE.RealQuantifierElimination

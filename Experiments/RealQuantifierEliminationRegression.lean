import MathUE.RealQuantifierElimination.QuantifierElimination

/-!
# Small executable quantifier-elimination regressions

Reproduce with:

`lake --quiet --iofail build Experiments.RealQuantifierEliminationRegression`

The `#guard` commands execute the actual closed decision function during
elaboration; they do not create theorem declarations. Separate examples prove expected
outputs from real semantics and the endpoint correctness theorem, including
nontrivial alternating sentences. The polynomial guards cover one quantified variable.  Constant-body
alternation is only a bounded frontend smoke test: executing even the linear
sentence `∀ x, ∃ y, y - x = 0` does not fit this module's small-cost budget.
On these examples, ordinary kernel `by decide` gets stuck at the proof-aware
well-founded producer.
-/

namespace Experiments.RealQuantifierEliminationRegression

open MathUE.RealQuantifierElimination

/-- The true sentence `there exists x, x = 0`. -/
def regressionExistsZero : PolynomialFormula 0 :=
  .ex (.atom (.var 0) .zero)

/-- The false sentence `for every x, x > 0`. -/
def regressionAllPositive : PolynomialFormula 0 :=
  .all (.atom (.var 0) .pos)

/-- The true alternating sentence `for every x, there exists y, y - x = 0`. -/
def regressionAllExistsEqual : PolynomialFormula 0 :=
  .all (.ex (.atom (.add (.var 0) (.neg (.var 1))) .zero))

/-- The false alternating sentence `there exists x, for every y, y - x = 0`. -/
def regressionExistsAllEqual : PolynomialFormula 0 :=
  .ex (.all (.atom (.add (.var 0) (.neg (.var 1))) .zero))

/-- The true alternating sentence `for every x, there exists y, True`. -/
def regressionAllExistsTop : PolynomialFormula 0 :=
  .all (.ex .top)

/-- The false alternating sentence `there exists x, for every y, False`. -/
def regressionExistsAllBottom : PolynomialFormula 0 :=
  .ex (.all .bot)

#guard decideClosedFormula regressionExistsZero
#guard !(decideClosedFormula regressionAllPositive)
#guard decideClosedFormula regressionAllExistsTop
#guard !(decideClosedFormula regressionExistsAllBottom)

private theorem regressionExistsZero_semantics :
    regressionExistsZero.HoldsAt Fin.elim0 := by
  change ∃ value : ℝ, SignType.sign value = .zero
  refine ⟨0, ?_⟩
  simp

private theorem regressionAllPositive_semantics :
    ¬regressionAllPositive.HoldsAt Fin.elim0 := by
  change ¬∀ value : ℝ, SignType.sign value = .pos
  intro hholds
  have hzero := hholds 0
  simp at hzero

private theorem regressionAllExistsEqual_semantics :
    regressionAllExistsEqual.HoldsAt Fin.elim0 := by
  change ∀ value : ℝ, ∃ witness : ℝ,
    SignType.sign (witness + -value) = .zero
  intro value
  refine ⟨value, ?_⟩
  simp

private theorem regressionExistsAllEqual_semantics :
    ¬regressionExistsAllEqual.HoldsAt Fin.elim0 := by
  change ¬∃ value : ℝ, ∀ witness : ℝ,
    SignType.sign (witness + -value) = .zero
  rintro ⟨value, hvalue⟩
  have hnext := hvalue (value + 1)
  have hone : value + 1 + -value = (1 : ℝ) := by
    abel
  rw [hone] at hnext
  simp at hnext

/-- The semantic endpoint independently proves the true one-quantifier case. -/
example : decideClosedFormula regressionExistsZero = true :=
  (decideClosedFormula_eq_true_iff regressionExistsZero).mpr
    regressionExistsZero_semantics

/-- The semantic endpoint independently proves the true alternating case. -/
example : decideClosedFormula regressionAllExistsEqual = true :=
  (decideClosedFormula_eq_true_iff regressionAllExistsEqual).mpr
    regressionAllExistsEqual_semantics

/-- The semantic endpoint independently proves the false one-quantifier case. -/
example : decideClosedFormula regressionAllPositive = false := by
  cases hdecision : decideClosedFormula regressionAllPositive with
  | false => rfl
  | true =>
      exact (regressionAllPositive_semantics
        ((decideClosedFormula_eq_true_iff regressionAllPositive).mp hdecision)).elim

/-- The semantic endpoint independently proves the false alternating case. -/
example : decideClosedFormula regressionExistsAllEqual = false := by
  cases hdecision : decideClosedFormula regressionExistsAllEqual with
  | false => rfl
  | true =>
      exact (regressionExistsAllEqual_semantics
        ((decideClosedFormula_eq_true_iff regressionExistsAllEqual).mp hdecision)).elim

end Experiments.RealQuantifierEliminationRegression

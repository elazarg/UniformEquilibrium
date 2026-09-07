import MathUE.RealQuantifierElimination.SemialgebraicPresentation

/-!
# Reifying finite real polynomial coefficients as parameters

Arbitrary real coefficients become fixed appended parameters. The resulting
ring expression uses only its explicit raw syntax operations.
-/

namespace MathUE.RealQuantifierElimination

namespace RingExpression

variable {n leftCount rightCount : Nat}

/-- Embed the original variables into a context extended by `k` parameters. -/
def originalIndex (k : Nat) : Fin n → Fin (n + k) :=
  Fin.castAdd k

/-- Embed a left parameter block into the concatenation of two parameter blocks. -/
def leftBlockIndex (n rightCount : Nat) :
    Fin (n + leftCount) → Fin (n + (leftCount + rightCount)) :=
  Fin.addCases (Fin.castAdd (leftCount + rightCount)) fun index =>
    Fin.natAdd n (Fin.castAdd rightCount index)

/-- Embed a right parameter block after a left parameter block. -/
def rightBlockIndex (n leftCount : Nat) :
    Fin (n + rightCount) → Fin (n + (leftCount + rightCount)) :=
  Fin.addCases (Fin.castAdd (leftCount + rightCount)) fun index =>
    Fin.natAdd n (Fin.natAdd leftCount index)

theorem append_append_comp_leftBlockIndex
    (environment : Fin n → ℝ) (left : Fin leftCount → ℝ)
    (right : Fin rightCount → ℝ) :
    Fin.append environment (Fin.append left right) ∘
        leftBlockIndex n rightCount =
      Fin.append environment left := by
  funext index
  refine Fin.addCases ?_ ?_ index
  · intro original
    simp [leftBlockIndex]
  · intro parameter
    simp [leftBlockIndex]

theorem append_append_comp_rightBlockIndex
    (environment : Fin n → ℝ) (left : Fin leftCount → ℝ)
    (right : Fin rightCount → ℝ) :
    Fin.append environment (Fin.append left right) ∘
        rightBlockIndex n leftCount =
      Fin.append environment right := by
  funext index
  refine Fin.addCases ?_ ?_ index
  · intro original
    simp [rightBlockIndex]
  · intro parameter
    simp [rightBlockIndex]

/-- Every finite real multivariate polynomial is represented by a rational
ring expression after adjoining finitely many fixed real coefficient
parameters. This is an existence construction on mathematical real values,
not an algorithm for encoding opaque reals. -/
theorem exists_reification_mvPolynomial
    (polynomial : MvPolynomial (Fin n) ℝ) :
    ∃ k, ∃ parameters : Fin k → ℝ, ∃ expression : RingExpression (n + k),
      ∀ environment : Fin n → ℝ,
        expression.evalReal (Fin.append environment parameters) =
          MvPolynomial.eval environment polynomial := by
  induction polynomial using MvPolynomial.induction_on with
  | C value =>
      refine ⟨1, fun _ => value,
        .var (Fin.natAdd n (0 : Fin 1)), ?_⟩
      intro environment
      simp
  | add left right hleft hright =>
      obtain ⟨leftCount, leftParameters, leftExpression, hleft⟩ := hleft
      obtain ⟨rightCount, rightParameters, rightExpression, hright⟩ := hright
      refine ⟨leftCount + rightCount, Fin.append leftParameters rightParameters,
        leftExpression.rename (leftBlockIndex n rightCount) +
          rightExpression.rename (rightBlockIndex n leftCount), ?_⟩
      intro environment
      rw [evalReal_add, evalReal_rename, evalReal_rename,
        append_append_comp_leftBlockIndex,
        append_append_comp_rightBlockIndex, hleft, hright]
      simp
  | mul_X polynomial index hpolynomial =>
      obtain ⟨count, parameters, expression, hcorrect⟩ := hpolynomial
      refine ⟨count, parameters,
        expression * .var (originalIndex count index), ?_⟩
      intro environment
      rw [evalReal_mul, hcorrect]
      simp [originalIndex]

end RingExpression

end MathUE.RealQuantifierElimination

namespace Math.PolynomialSignCell.SignFormula

open MathUE.RealQuantifierElimination

/-- Every finite Boolean sign formula over real multivariate polynomials is a
rational quantifier-free formula after adjoining finitely many fixed real
coefficient parameters. -/
theorem exists_rationalReification
    (formula : SignFormula (MvPolynomial (Fin n) ℝ)) :
    ∃ k, ∃ parameters : Fin k → ℝ,
      ∃ rationalFormula : QuantifierFreeFormula (n + k),
        ∀ environment : Fin n → ℝ,
          rationalFormula.HoldsAt (Fin.append environment parameters) ↔
            formula.Holds (fun polynomial =>
              SignType.sign (MvPolynomial.eval environment polynomial)) := by
  induction formula with
  | atom polynomial sign =>
      obtain ⟨count, parameters, expression, hcorrect⟩ :=
        RingExpression.exists_reification_mvPolynomial polynomial
      refine ⟨count, parameters, .atom expression sign, ?_⟩
      intro environment
      change
        SignType.sign (expression.evalReal (Fin.append environment parameters)) = sign ↔
          SignType.sign (MvPolynomial.eval environment polynomial) = sign
      exact (congrArg (fun value => SignType.sign value = sign)
        (hcorrect environment)).to_iff
  | top =>
      exact ⟨0, Fin.elim0, .top, fun _ => Iff.rfl⟩
  | bot =>
      exact ⟨0, Fin.elim0, .bot, fun _ => Iff.rfl⟩
  | and left right hleft hright =>
      obtain ⟨leftCount, leftParameters, leftFormula, hleft⟩ := hleft
      obtain ⟨rightCount, rightParameters, rightFormula, hright⟩ := hright
      refine ⟨leftCount + rightCount, Fin.append leftParameters rightParameters,
        .and
          (leftFormula.rename (RingExpression.leftBlockIndex n rightCount))
          (rightFormula.rename (RingExpression.rightBlockIndex n leftCount)),
        ?_⟩
      intro environment
      change
        (leftFormula.rename (RingExpression.leftBlockIndex n rightCount)).HoldsAt
            (Fin.append environment (Fin.append leftParameters rightParameters)) ∧
          (rightFormula.rename
              (RingExpression.rightBlockIndex n leftCount)).HoldsAt
            (Fin.append environment (Fin.append leftParameters rightParameters)) ↔ _
      rw [QuantifierFreeFormula.holdsAt_rename, QuantifierFreeFormula.holdsAt_rename,
        RingExpression.append_append_comp_leftBlockIndex,
        RingExpression.append_append_comp_rightBlockIndex, hleft, hright]
      rfl
  | or left right hleft hright =>
      obtain ⟨leftCount, leftParameters, leftFormula, hleft⟩ := hleft
      obtain ⟨rightCount, rightParameters, rightFormula, hright⟩ := hright
      refine ⟨leftCount + rightCount, Fin.append leftParameters rightParameters,
        .or
          (leftFormula.rename (RingExpression.leftBlockIndex n rightCount))
          (rightFormula.rename (RingExpression.rightBlockIndex n leftCount)),
        ?_⟩
      intro environment
      change
        (leftFormula.rename (RingExpression.leftBlockIndex n rightCount)).HoldsAt
            (Fin.append environment (Fin.append leftParameters rightParameters)) ∨
          (rightFormula.rename
              (RingExpression.rightBlockIndex n leftCount)).HoldsAt
            (Fin.append environment (Fin.append leftParameters rightParameters)) ↔ _
      rw [QuantifierFreeFormula.holdsAt_rename, QuantifierFreeFormula.holdsAt_rename,
        RingExpression.append_append_comp_leftBlockIndex,
        RingExpression.append_append_comp_rightBlockIndex, hleft, hright]
      rfl
  | not formula hformula =>
      obtain ⟨count, parameters, rationalFormula, hformula⟩ := hformula
      refine ⟨count, parameters, .not rationalFormula, ?_⟩
      intro environment
      exact not_congr (hformula environment)

end Math.PolynomialSignCell.SignFormula

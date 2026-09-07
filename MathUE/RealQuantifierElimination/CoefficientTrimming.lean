import MathUE.RealQuantifierElimination.CoefficientSignBranch
import MathUE.RealQuantifierElimination.PolynomialEvaluation

/-!
# Symbolic trimming of dense polynomial coefficients

Leading coefficients are tested from highest to lowest.  Only a coefficient
whose real specialization is zero is deleted.  The result therefore has the
same specialized Horner evaluation and is either empty or has a nonzero
specialized leading coefficient.
-/

namespace MathUE.RealQuantifierElimination


namespace CoefficientSignBranch

variable {n : Nat}

/-- Branch on leading coefficients, deleting one only on its zero branch. -/
def trimLeading :
    (polynomial : Math.DensePolynomial (RingExpression n)) →
      CoefficientSignBranch n (Math.DensePolynomial (RingExpression n))
  | [] => .leaf []
  | polynomial@(_ :: _) =>
      let leading := Math.DensePolynomial.leadingCoeff polynomial
      .test leading (.leaf polynomial) (trimLeading polynomial.dropLast)
        (.leaf polynomial)
termination_by polynomial => polynomial.length
decreasing_by simp_all

/-- The kernel-level correctness contract for symbolic leading-zero trimming. -/
def IsTrimmedAt
    (environment : Fin n → ℝ)
    (original trimmed : Math.DensePolynomial (RingExpression n)) : Prop :=
  (∀ x, Math.DensePolynomial.evalMap (RingExpression.realEvaluator environment)
      original x =
    Math.DensePolynomial.evalMap (RingExpression.realEvaluator environment)
      trimmed x) ∧
  trimmed.length ≤ original.length ∧
  (trimmed = [] ∨
    RingExpression.realEvaluator environment
      (Math.DensePolynomial.leadingCoeff trimmed) ≠ 0)

/-- Every selected trim leaf preserves evaluation and removes specialized leading zeroes. -/
theorem isTrimmedAt_of_selects_trimLeading
    (environment : Fin n → ℝ)
    (original trimmed : Math.DensePolynomial (RingExpression n))
    (hselected : (trimLeading original).Selects environment trimmed) :
    IsTrimmedAt environment original trimmed := by
  induction hlength : original.length using Nat.strong_induction_on generalizing original trimmed with
  | h length ih =>
      cases original with
      | nil =>
          simp [trimLeading, Selects] at hselected
          subst trimmed
          simp [IsTrimmedAt]
      | cons coefficient rest =>
          let polynomial : Math.DensePolynomial (RingExpression n) := coefficient :: rest
          let leading := Math.DensePolynomial.leadingCoeff polynomial
          have hpolynomial : polynomial ≠ [] := List.cons_ne_nil coefficient rest
          have hshort : polynomial.dropLast.length < length := by
            calc
              polynomial.dropLast.length < polynomial.length := by
                rw [List.length_dropLast]
                have hpositive : 0 < polynomial.length :=
                  List.length_pos_iff.mpr hpolynomial
                omega
              _ = length := by simpa [polynomial] using hlength
          change (trimLeading polynomial).Selects environment trimmed at hselected
          cases hsign : SignType.sign (leading.evalReal environment) with
          | neg =>
              have htrimmed : trimmed = polynomial := by
                simpa [trimLeading, Selects, polynomial, leading, hsign] using hselected
              subst trimmed
              refine ⟨fun _ => rfl, le_rfl, Or.inr ?_⟩
              intro hzero
              have hsignZero : SignType.sign (leading.evalReal environment) = .zero :=
                sign_eq_zero_iff.mpr hzero
              rw [hsign] at hsignZero
              contradiction
          | zero =>
              have hselectedDrop :
                  (trimLeading polynomial.dropLast).Selects environment trimmed := by
                simpa [trimLeading, Selects, polynomial, leading, hsign] using hselected
              have hresult := ih polynomial.dropLast.length hshort
                polynomial.dropLast trimmed hselectedDrop rfl
              rcases hresult with ⟨heval, hlen, hlead⟩
              have hdropLe : polynomial.dropLast.length ≤ polynomial.length := by
                rw [List.length_dropLast]
                omega
              refine ⟨?_, hlen.trans hdropLe, hlead⟩
              intro x
              have hleadingZero :
                  RingExpression.realEvaluator environment
                    (Math.DensePolynomial.leadingCoeff polynomial) = 0 := by
                change leading.evalReal environment = 0
                exact sign_eq_zero_iff.mp hsign
              rw [← Math.DensePolynomial.evalMap_dropLast_of_leading_zero
                (RingExpression.realEvaluator environment) hpolynomial x hleadingZero]
              exact heval x
          | pos =>
              have htrimmed : trimmed = polynomial := by
                simpa [trimLeading, Selects, polynomial, leading, hsign] using hselected
              subst trimmed
              refine ⟨fun _ => rfl, le_rfl, Or.inr ?_⟩
              intro hzero
              have hsignZero : SignType.sign (leading.evalReal environment) = .zero :=
                sign_eq_zero_iff.mpr hzero
              rw [hsign] at hsignZero
              contradiction

/-- Trimming remains exhaustive and single-valued for every real environment. -/
theorem existsUnique_trimLeading
    (environment : Fin n → ℝ)
    (polynomial : Math.DensePolynomial (RingExpression n)) :
    ∃! trimmed, (trimLeading polynomial).Selects environment trimmed :=
  (trimLeading polynomial).existsUnique_selects environment

/-- A selected nonempty output has exact degree after real specialization. -/
theorem toPolynomial_natDegree_eq_of_selects_trimLeading
    (environment : Fin n → ℝ)
    (original trimmed : Math.DensePolynomial (RingExpression n))
    (hselected : (trimLeading original).Selects environment trimmed)
    (htrimmed : trimmed ≠ []) :
    (Math.DensePolynomial.toPolynomial (RingExpression.realEvaluator environment)
      trimmed).natDegree = trimmed.length - 1 := by
  have hresult := isTrimmedAt_of_selects_trimLeading
    environment original trimmed hselected
  exact Math.DensePolynomial.toPolynomial_natDegree_eq
    (RingExpression.realEvaluator environment) trimmed
    (hresult.2.2.resolve_left htrimmed)

end CoefficientSignBranch
end MathUE.RealQuantifierElimination

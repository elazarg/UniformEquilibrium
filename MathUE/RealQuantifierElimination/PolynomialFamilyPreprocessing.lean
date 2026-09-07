import MathUE.RealQuantifierElimination.CoefficientTrimming
import MathUE.RealQuantifierElimination.PolynomialFamilyMeasure
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Polynomial-family preprocessing for real sign diagrams

Symbolic leading-zero trimming is sequenced across an input family. Each leaf
classifies every original column, retains only nonconstant columns for recursive
geometry, and can reconstruct full sign rows in the original order.
-/

namespace MathUE.RealQuantifierElimination

open Math

/-- The specialized role of one polynomial column after coefficient trimming. -/
inductive PolynomialClassification (n : Nat)
  | zero
  | constant (sign : SignType)
  | nonconstant (polynomial : DensePolynomial (RingExpression n))
  deriving DecidableEq

namespace PolynomialClassification

variable {n : Nat}

/-- Classify an already-trimmed polynomial, branching on a singleton constant. -/
def classifyTrimmed :
    DensePolynomial (RingExpression n) →
      CoefficientSignBranch n (PolynomialClassification n)
  | [] => .leaf .zero
  | [coefficient] =>
      .test coefficient (.leaf (.constant .neg)) (.leaf .zero)
        (.leaf (.constant .pos))
  | coefficient :: next :: rest => .leaf (.nonconstant (coefficient :: next :: rest))

end PolynomialClassification

namespace CoefficientSignBranch

variable {n : Nat}

/-- Trim and classify one input polynomial. -/
def preprocessPolynomial (polynomial : DensePolynomial (RingExpression n)) :
    CoefficientSignBranch n (PolynomialClassification n) :=
  (trimLeading polynomial).bind PolynomialClassification.classifyTrimmed

/-- Preprocess a family from left to right while preserving classification order. -/
def preprocessFamily :
    List (DensePolynomial (RingExpression n)) →
      CoefficientSignBranch n (List (PolynomialClassification n))
  | [] => .leaf []
  | polynomial :: polynomials =>
      (preprocessPolynomial polynomial).bind fun classification =>
        (preprocessFamily polynomials).map fun classifications =>
          classification :: classifications

end CoefficientSignBranch

/-- Retain exactly the nonconstant polynomials, without changing their order. -/
def nonconstantPolynomials {n : Nat} :
    List (PolynomialClassification n) →
      List (DensePolynomial (RingExpression n))
  | [] => []
  | .zero :: classifications => nonconstantPolynomials classifications
  | .constant _ :: classifications => nonconstantPolynomials classifications
  | .nonconstant polynomial :: classifications =>
      polynomial :: nonconstantPolynomials classifications

/-- Reinsert removed zero and constant columns, consuming nonconstant signs in order. -/
def restoreRow {n : Nat} :
    List (PolynomialClassification n) → List SignType → Option (List SignType)
  | [], [] => some []
  | [], _ :: _ => none
  | .zero :: classifications, signs =>
      (SignType.zero :: ·) <$> restoreRow classifications signs
  | .constant sign :: classifications, signs =>
      (sign :: ·) <$> restoreRow classifications signs
  | .nonconstant _ :: _, [] => none
  | .nonconstant _ :: classifications, sign :: signs =>
      (sign :: ·) <$> restoreRow classifications signs

/-- Semantic correctness of one classification at a real environment. -/
def ClassifiesAt {n : Nat} (environment : Fin n → ℝ)
    (original : DensePolynomial (RingExpression n)) :
    PolynomialClassification n → Prop
  | .zero =>
      DensePolynomial.toPolynomial (RingExpression.realEvaluator environment)
        original = 0
  | .constant sign =>
      sign ≠ .zero ∧
        ∀ x, SignType.sign
          (DensePolynomial.evalMap (RingExpression.realEvaluator environment)
            original x) = sign
  | .nonconstant polynomial =>
      2 ≤ polynomial.length ∧
        CoefficientSignBranch.IsTrimmedAt environment original polynomial

/-- Pointwise exact signs for a family in its current column order. -/
def RowAt {n : Nat} (environment : Fin n → ℝ) (x : ℝ)
    (polynomials : List (DensePolynomial (RingExpression n)))
    (row : List SignType) : Prop :=
  List.Forall₂
    (fun polynomial sign =>
      SignType.sign
        (DensePolynomial.evalMap (RingExpression.realEvaluator environment)
          polynomial x) = sign)
    polynomials row

/-- Order-preserving semantic classification of an entire input family. -/
def ClassifiesFamilyAt {n : Nat} (environment : Fin n → ℝ)
    (originals : List (DensePolynomial (RingExpression n)))
    (classifications : List (PolynomialClassification n)) : Prop :=
  List.Forall₂ (ClassifiesAt environment) originals classifications

namespace CoefficientSignBranch

variable {n : Nat}

/-- Every selected single-polynomial preprocessing leaf has its stated semantics. -/
theorem classifiesAt_of_selects_preprocessPolynomial
    (environment : Fin n → ℝ)
    (original : DensePolynomial (RingExpression n))
    (classification : PolynomialClassification n)
    (hselected : (preprocessPolynomial original).Selects environment classification) :
    ClassifiesAt environment original classification := by
  rw [preprocessPolynomial, selects_bind_iff] at hselected
  obtain ⟨trimmed, htrimmed, hclassified⟩ := hselected
  have hcorrect := isTrimmedAt_of_selects_trimLeading
    environment original trimmed htrimmed
  rcases hcorrect with ⟨heval, hlength, hleading⟩
  cases trimmed with
  | nil =>
      simp [PolynomialClassification.classifyTrimmed, Selects] at hclassified
      subst classification
      apply Polynomial.funext
      intro x
      rw [DensePolynomial.toPolynomial_eval]
      simpa using heval x
  | cons coefficient rest =>
      cases rest with
      | nil =>
          cases hsign : SignType.sign (coefficient.evalReal environment) with
          | neg =>
              simp [PolynomialClassification.classifyTrimmed, Selects, hsign] at hclassified
              subst classification
              refine ⟨by simp, fun x => ?_⟩
              rw [heval x]
              simpa using hsign
          | zero =>
              simp [PolynomialClassification.classifyTrimmed, Selects, hsign] at hclassified
              subst classification
              apply Polynomial.funext
              intro x
              rw [DensePolynomial.toPolynomial_eval]
              rw [heval x]
              simpa using sign_eq_zero_iff.mp hsign
          | pos =>
              simp [PolynomialClassification.classifyTrimmed, Selects, hsign] at hclassified
              subst classification
              refine ⟨by simp, fun x => ?_⟩
              rw [heval x]
              simpa using hsign
      | cons next rest =>
          simp [PolynomialClassification.classifyTrimmed, Selects] at hclassified
          subst classification
          exact ⟨by simp, ⟨heval, hlength, hleading⟩⟩

/-- Every selected family leaf classifies all original columns in order. -/
theorem classifiesFamilyAt_of_selects_preprocessFamily
    (environment : Fin n → ℝ)
    (originals : List (DensePolynomial (RingExpression n)))
    (classifications : List (PolynomialClassification n))
    (hselected : (preprocessFamily originals).Selects environment classifications) :
    ClassifiesFamilyAt environment originals classifications := by
  induction originals generalizing classifications with
  | nil =>
      simp [preprocessFamily, Selects] at hselected
      subst classifications
      exact .nil
  | cons original originals ih =>
      rw [preprocessFamily, selects_bind_iff] at hselected
      obtain ⟨classification, hclassification, hrest⟩ := hselected
      rw [selects_map_iff] at hrest
      obtain ⟨classificationsTail, htail, heq⟩ := hrest
      subst classifications
      exact .cons
        (classifiesAt_of_selects_preprocessPolynomial
          environment original classification hclassification)
        (ih classificationsTail htail)

/-- Family preprocessing is exhaustive and single-valued at every environment. -/
theorem existsUnique_preprocessFamily
    (environment : Fin n → ℝ)
    (originals : List (DensePolynomial (RingExpression n))) :
    ∃! classifications, (preprocessFamily originals).Selects environment classifications :=
  (preprocessFamily originals).existsUnique_selects environment

end CoefficientSignBranch

/-- A correct recursive row reconstructs a correct row for all original columns. -/
theorem exists_restoreRow_rowAt {n : Nat}
    (environment : Fin n → ℝ) (x : ℝ)
    {originals : List (DensePolynomial (RingExpression n))}
    {classifications : List (PolynomialClassification n)}
    (hclassified : ClassifiesFamilyAt environment originals classifications)
    {recursiveRow : List SignType}
    (hrow : RowAt environment x
      (nonconstantPolynomials classifications) recursiveRow) :
    ∃ restoredRow,
      restoreRow classifications recursiveRow = some restoredRow ∧
      RowAt environment x originals restoredRow := by
  induction hclassified generalizing recursiveRow with
  | nil =>
      simp [nonconstantPolynomials, RowAt] at hrow
      subst recursiveRow
      exact ⟨[], rfl, .nil⟩
  | @cons original classification originals classifications hhead htail ih =>
      cases classification with
      | zero =>
          obtain ⟨restored, hrestore, hrestored⟩ := ih hrow
          refine ⟨.zero :: restored, by simp [restoreRow, hrestore], .cons ?_ hrestored⟩
          rw [← DensePolynomial.toPolynomial_eval, hhead]
          simp
      | constant sign =>
          obtain ⟨restored, hrestore, hrestored⟩ := ih hrow
          exact ⟨sign :: restored, by simp [restoreRow, hrestore],
            .cons (hhead.2 x) hrestored⟩
      | nonconstant polynomial =>
          cases recursiveRow with
          | nil => cases hrow
          | cons sign signs =>
              cases hrow with
              | cons hpolynomial hrowTail =>
                  obtain ⟨restored, hrestore, hrestored⟩ := ih hrowTail
                  have horiginal :
                      SignType.sign
                        (DensePolynomial.evalMap
                          (RingExpression.realEvaluator environment) original x) = sign := by
                    rw [hhead.2.1 x]
                    exact hpolynomial
                  exact ⟨sign :: restored, by simp [restoreRow, hrestore],
                    .cons horiginal hrestored⟩

end MathUE.RealQuantifierElimination

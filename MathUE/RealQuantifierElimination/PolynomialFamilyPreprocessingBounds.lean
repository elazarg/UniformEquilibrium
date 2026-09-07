import MathUE.RealQuantifierElimination.CoefficientSignBranchInvariants
import MathUE.RealQuantifierElimination.PolynomialFamilyPreprocessing
import MathUE.RealQuantifierElimination.PolynomialFamilyReduction

/-! # Structural size bounds for every preprocessing branch leaf -/

namespace MathUE.RealQuantifierElimination

open Math

namespace CoefficientSignBranch

variable {n : Nat} {α : Type*}

/-- Every syntactic trim leaf is no longer than its input. -/
theorem allLeaves_trimLeading_length_le
    (polynomial : DensePolynomial (RingExpression n)) :
    (trimLeading polynomial).AllLeaves fun trimmed =>
      trimmed.length ≤ polynomial.length := by
  induction hlength : polynomial.length using Nat.strong_induction_on generalizing polynomial with
  | h length ih =>
      cases polynomial with
      | nil => simp [trimLeading]
      | cons coefficient rest =>
          let polynomial : DensePolynomial (RingExpression n) := coefficient :: rest
          have hpolynomial : polynomial ≠ [] := List.cons_ne_nil coefficient rest
          have hshort : polynomial.dropLast.length < length := by
            calc
              polynomial.dropLast.length < polynomial.length := by
                rw [List.length_dropLast]
                have hpositive : 0 < polynomial.length :=
                  List.length_pos_iff.mpr hpolynomial
                omega
              _ = length := by simpa [polynomial] using hlength
          have hpolynomialLength : polynomial.length = length := by
            simpa [polynomial] using hlength
          have ihDrop := ih polynomial.dropLast.length hshort polynomial.dropLast rfl
          rw [trimLeading, allLeaves_test_iff]
          refine ⟨hpolynomialLength.le, ?_, hpolynomialLength.le⟩
          exact ihDrop.mono fun _ hle =>
            hle.trans hshort.le

end CoefficientSignBranch

/-- A classification never retains a polynomial longer than its original column. -/
def ClassificationLengthBound {n : Nat}
    (original : DensePolynomial (RingExpression n)) :
    PolynomialClassification n → Prop
  | .zero => True
  | .constant _ => True
  | .nonconstant polynomial =>
      2 ≤ polynomial.length ∧ polynomial.length ≤ original.length

/-- Structural alignment and length bounds for all original columns. -/
def FamilyLengthBound {n : Nat}
    (originals : List (DensePolynomial (RingExpression n)))
    (classifications : List (PolynomialClassification n)) : Prop :=
  List.Forall₂ ClassificationLengthBound originals classifications

namespace CoefficientSignBranch

variable {n : Nat}

theorem allLeaves_classifyTrimmed_lengthBound
    (polynomial : DensePolynomial (RingExpression n)) :
    (PolynomialClassification.classifyTrimmed polynomial).AllLeaves
      (ClassificationLengthBound polynomial) := by
  cases polynomial with
  | nil => trivial
  | cons coefficient rest =>
      cases rest with
      | nil => exact ⟨trivial, trivial, trivial⟩
      | cons next rest => exact ⟨by simp, le_rfl⟩

theorem allLeaves_preprocessPolynomial_lengthBound
    (polynomial : DensePolynomial (RingExpression n)) :
    (preprocessPolynomial polynomial).AllLeaves
      (ClassificationLengthBound polynomial) := by
  rw [preprocessPolynomial, allLeaves_bind_iff]
  exact (allLeaves_trimLeading_length_le polynomial).mono fun trimmed hlength =>
    (allLeaves_classifyTrimmed_lengthBound trimmed).mono fun classification hbound => by
      cases classification with
      | zero => trivial
      | constant sign => trivial
      | nonconstant retained => exact ⟨hbound.1, hbound.2.trans hlength⟩

/-- Every syntactic family-preprocessing leaf has aligned column-size bounds. -/
theorem allLeaves_preprocessFamily_lengthBound
    (originals : List (DensePolynomial (RingExpression n))) :
    (preprocessFamily originals).AllLeaves (FamilyLengthBound originals) := by
  induction originals with
  | nil => exact .nil
  | cons original originals ih =>
      rw [preprocessFamily, allLeaves_bind_iff]
      exact (allLeaves_preprocessPolynomial_lengthBound original).mono
        fun classification hclassification => by
          rw [allLeaves_map_iff]
          exact ih.mono fun classifications hclassifications =>
            .cons hclassification hclassifications

end CoefficientSignBranch

theorem familyMaximumLength_nonconstantPolynomials_le {n : Nat}
    {originals : List (DensePolynomial (RingExpression n))}
    {classifications : List (PolynomialClassification n)}
    (hbound : FamilyLengthBound originals classifications) :
    familyMaximumLength (nonconstantPolynomials classifications) ≤
      familyMaximumLength originals := by
  induction hbound with
  | nil => rfl
  | @cons original classification originals classifications hhead htail ih =>
      cases classification with
      | zero =>
          simp only [nonconstantPolynomials, familyMaximumLength_cons]
          exact ih.trans (Nat.le_max_right _ _)
      | constant sign =>
          simp only [nonconstantPolynomials, familyMaximumLength_cons]
          exact ih.trans (Nat.le_max_right _ _)
      | nonconstant polynomial =>
          simp only [nonconstantPolynomials, familyMaximumLength_cons]
          exact max_le_max hhead.2 ih

theorem familyTotalSize_nonconstantPolynomials_le {n : Nat}
    {originals : List (DensePolynomial (RingExpression n))}
    {classifications : List (PolynomialClassification n)}
    (hbound : FamilyLengthBound originals classifications) :
    familyTotalSize (nonconstantPolynomials classifications) ≤
      familyTotalSize originals := by
  induction hbound with
  | nil => rfl
  | @cons original classification originals classifications hhead htail ih =>
      cases classification with
      | zero =>
          simp only [nonconstantPolynomials, familyTotalSize_cons]
          omega
      | constant sign =>
          simp only [nonconstantPolynomials, familyTotalSize_cons]
          omega
      | nonconstant polynomial =>
          change 2 ≤ polynomial.length ∧ polynomial.length ≤ original.length at hhead
          simp only [nonconstantPolynomials, familyTotalSize_cons]
          omega

theorem familyCountLength_nonconstantPolynomials_le {n : Nat}
    {originals : List (DensePolynomial (RingExpression n))}
    {classifications : List (PolynomialClassification n)}
    (hbound : FamilyLengthBound originals classifications) (length : Nat)
    (horiginal : ∀ polynomial ∈ originals, polynomial.length ≤ length) :
    familyCountLength length (nonconstantPolynomials classifications) ≤
      familyCountLength length originals := by
  induction hbound with
  | nil => rfl
  | @cons original classification originals classifications hhead htail ih =>
      have horiginalHead : original.length ≤ length := horiginal original (by simp)
      have horiginalTail : ∀ polynomial ∈ originals, polynomial.length ≤ length :=
        fun polynomial hmem => horiginal polynomial (by simp [hmem])
      have ihTail := ih horiginalTail
      cases classification with
      | zero =>
          simp only [nonconstantPolynomials, familyCountLength_cons]
          omega
      | constant sign =>
          simp only [nonconstantPolynomials, familyCountLength_cons]
          omega
      | nonconstant polynomial =>
          change 2 ≤ polynomial.length ∧ polynomial.length ≤ original.length at hhead
          simp only [nonconstantPolynomials, familyCountLength_cons]
          by_cases hpolynomial : polynomial.length = length
          · have horiginalEq : original.length = length := by omega
            simp [hpolynomial, horiginalEq]
            omega
          · simp [hpolynomial]
            omega

/-- Every retained family member is structurally nonconstant. -/
theorem nonconstantPolynomials_length_two_le {n : Nat}
    {originals : List (DensePolynomial (RingExpression n))}
    {classifications : List (PolynomialClassification n)}
    (hbound : FamilyLengthBound originals classifications) :
    ∀ polynomial ∈ nonconstantPolynomials classifications, 2 ≤ polynomial.length := by
  induction hbound with
  | nil => simp [nonconstantPolynomials]
  | @cons original classification originals classifications hhead htail ih =>
      cases classification with
      | zero => simpa [nonconstantPolynomials] using ih
      | constant sign => simpa [nonconstantPolynomials] using ih
      | nonconstant polynomial =>
          intro retained hmem
          rw [nonconstantPolynomials, List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact hhead.1
          · exact ih retained hmem

/-- Every structurally bounded preprocessing result has nonincreasing recursion measure. -/
theorem familyRecursionMeasure_nonconstantPolynomials_atMost {n : Nat}
    {originals : List (DensePolynomial (RingExpression n))}
    {classifications : List (PolynomialClassification n)}
    (hbound : FamilyLengthBound originals classifications) :
    (familyRecursionMeasure (nonconstantPolynomials classifications)).AtMost
      (familyRecursionMeasure originals) := by
  have hmaximum := familyMaximumLength_nonconstantPolynomials_le hbound
  have htotal := familyTotalSize_nonconstantPolynomials_le hbound
  rcases hmaximum.lt_or_eq with hmaximumLt | hmaximumEq
  · exact Or.inl hmaximumLt
  · right
    refine ⟨hmaximumEq, ?_⟩
    have hmember : ∀ polynomial ∈ originals,
        polynomial.length ≤ familyMaximumLength originals :=
      fun _ => length_le_familyMaximumLength
    have hcount := familyCountLength_nonconstantPolynomials_le hbound
      (familyMaximumLength originals) hmember
    have hmaximalCount :
        familyMaximalCount (nonconstantPolynomials classifications) ≤
          familyMaximalCount originals := by
      rw [familyMaximalCount_eq_countLength, familyMaximalCount_eq_countLength,
        hmaximumEq]
      exact hcount
    rcases hmaximalCount.lt_or_eq with hcountLt | hcountEq
    · exact Or.inl hcountLt
    · exact Or.inr ⟨hcountEq, htotal⟩

/-- The all-leaves form required by executable well-founded recursion. -/
theorem allLeaves_preprocessFamily_measure_atMost {n : Nat}
    (originals : List (DensePolynomial (RingExpression n))) :
    (CoefficientSignBranch.preprocessFamily originals).AllLeaves fun classifications =>
      (familyRecursionMeasure (nonconstantPolynomials classifications)).AtMost
        (familyRecursionMeasure originals) :=
  (CoefficientSignBranch.allLeaves_preprocessFamily_lengthBound originals).mono
    fun _ => familyRecursionMeasure_nonconstantPolynomials_atMost

end MathUE.RealQuantifierElimination

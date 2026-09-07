import MathUE.Polynomial.DensePolynomial

/-!
# Recursion measure for dense polynomial families

The sign-diagram producer orders family transformations lexicographically by
maximum formal list length, the number of columns attaining that maximum, and
a positive additive family size.
-/

namespace MathUE.RealQuantifierElimination

open Math

/-- Largest formal list length, with zero for the empty family. -/
def familyMaximumLength {A : Type*} (family : List (DensePolynomial A)) : Nat :=
  family.foldr (fun polynomial current => max polynomial.length current) 0

/-- Number of family members attaining the largest formal list length. -/
def familyMaximalCount {A : Type*} (family : List (DensePolynomial A)) : Nat :=
  family.countP fun polynomial => polynomial.length = familyMaximumLength family

/-- Positive additive size used after maximum length and maximal count tie. -/
def familyTotalSize {A : Type*} (family : List (DensePolynomial A)) : Nat :=
  family.foldr (fun polynomial current => polynomial.length + 1 + current) 0

/-- The three components of the sign-diagram recursion measure. -/
structure FamilyRecursionMeasure where
  maximumLength : Nat
  maximalCount : Nat
  totalSize : Nat
  deriving DecidableEq, Repr

/-- Compute all three recursion-measure components. -/
def familyRecursionMeasure {A : Type*}
    (family : List (DensePolynomial A)) : FamilyRecursionMeasure where
  maximumLength := familyMaximumLength family
  maximalCount := familyMaximalCount family
  totalSize := familyTotalSize family

/-- The standard nested product encoding of the three measure components. -/
def FamilyRecursionMeasure.toTriple
    (measure : FamilyRecursionMeasure) : Nat × (Nat × Nat) :=
  (measure.maximumLength, measure.maximalCount, measure.totalSize)

/-- Strict lexicographic comparison of family recursion measures. -/
def FamilyRecursionMeasure.Less
    (left right : FamilyRecursionMeasure) : Prop :=
  WellFoundedRelation.rel left.toTriple right.toTriple

instance : LT FamilyRecursionMeasure := ⟨FamilyRecursionMeasure.Less⟩

instance : WellFoundedRelation FamilyRecursionMeasure where
  rel := FamilyRecursionMeasure.Less
  wf := InvImage.wf FamilyRecursionMeasure.toTriple WellFoundedRelation.wf

theorem FamilyRecursionMeasure.less_iff
    {left right : FamilyRecursionMeasure} :
    left < right ↔
      left.maximumLength < right.maximumLength ∨
        (left.maximumLength = right.maximumLength ∧
          (left.maximalCount < right.maximalCount ∨
            (left.maximalCount = right.maximalCount ∧
              left.totalSize < right.totalSize))) := by
  change
    Prod.Lex (fun a b : Nat => a < b)
      (Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b))
      (left.maximumLength, left.maximalCount, left.totalSize)
      (right.maximumLength, right.maximalCount, right.totalSize) ↔ _
  rw [Prod.lex_def, Prod.lex_def]

@[simp]
theorem familyMaximumLength_nil {A : Type*} :
    familyMaximumLength ([] : List (DensePolynomial A)) = 0 :=
  rfl

@[simp]
theorem familyMaximumLength_cons {A : Type*}
    (polynomial : DensePolynomial A) (family : List (DensePolynomial A)) :
    familyMaximumLength (polynomial :: family) =
      max polynomial.length (familyMaximumLength family) :=
  rfl

@[simp]
theorem familyTotalSize_nil {A : Type*} :
    familyTotalSize ([] : List (DensePolynomial A)) = 0 :=
  rfl

@[simp]
theorem familyTotalSize_cons {A : Type*}
    (polynomial : DensePolynomial A) (family : List (DensePolynomial A)) :
    familyTotalSize (polynomial :: family) =
      polynomial.length + 1 + familyTotalSize family :=
  rfl

end MathUE.RealQuantifierElimination

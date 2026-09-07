import MathUE.RealQuantifierElimination.PolynomialFamilyMeasure
import Mathlib.Data.List.Count

/-!
# Lower-degree polynomial-family measure decreases

Removing or strictly shortening a column below the current maximum preserves
the first two recursion-measure components and strictly lowers total size.
-/

namespace MathUE.RealQuantifierElimination

open Math

/-- Count columns having one specified formal list length. -/
def familyCountLength {A : Type*}
    (length : Nat) (family : List (DensePolynomial A)) : Nat :=
  family.countP fun polynomial => polynomial.length = length

@[simp]
theorem familyCountLength_nil {A : Type*} (length : Nat) :
    familyCountLength length ([] : List (DensePolynomial A)) = 0 :=
  rfl

@[simp]
theorem familyCountLength_cons {A : Type*}
    (length : Nat) (polynomial : DensePolynomial A)
    (family : List (DensePolynomial A)) :
    familyCountLength length (polynomial :: family) =
      (if polynomial.length = length then 1 else 0) +
        familyCountLength length family :=
  by
    unfold familyCountLength
    by_cases hlength : polynomial.length = length
    · simp [hlength]
      omega
    · simp [hlength]

theorem familyCountLength_append {A : Type*}
    (length : Nat) (left right : List (DensePolynomial A)) :
    familyCountLength length (left ++ right) =
      familyCountLength length left + familyCountLength length right := by
  induction left with
  | nil => simp
  | cons polynomial left ih =>
      simp only [List.cons_append, familyCountLength_cons, ih]
      omega

theorem familyMaximalCount_eq_countLength {A : Type*}
    (family : List (DensePolynomial A)) :
    familyMaximalCount family =
      familyCountLength (familyMaximumLength family) family :=
  rfl

theorem familyMaximumLength_append {A : Type*}
    (left right : List (DensePolynomial A)) :
    familyMaximumLength (left ++ right) =
      max (familyMaximumLength left) (familyMaximumLength right) := by
  induction left with
  | nil => simp
  | cons polynomial left ih =>
      simp only [List.cons_append, familyMaximumLength_cons, ih]
      omega

theorem familyTotalSize_append {A : Type*}
    (left right : List (DensePolynomial A)) :
    familyTotalSize (left ++ right) =
      familyTotalSize left + familyTotalSize right := by
  induction left with
  | nil => simp
  | cons polynomial left ih =>
      simp only [List.cons_append, familyTotalSize_cons, ih]
      omega

/-- Strictly shortening a lower-degree focused column decreases the lexicographic measure. -/
theorem familyRecursionMeasure_replace_lower_shorter {A : Type*}
    (before after : List (DensePolynomial A))
    (original replacement : DensePolynomial A)
    (hlower : original.length <
      familyMaximumLength (before ++ original :: after))
    (hshorter : replacement.length < original.length) :
    familyRecursionMeasure (before ++ replacement :: after) <
      familyRecursionMeasure (before ++ original :: after) := by
  let maximum := familyMaximumLength (before ++ original :: after)
  have horiginalNe : original.length ≠ maximum := ne_of_lt hlower
  have hreplacementLower : replacement.length < maximum :=
    hshorter.trans hlower
  have hreplacementNe : replacement.length ≠ maximum :=
    ne_of_lt hreplacementLower
  have hmaximumOriginal :
      maximum = max (familyMaximumLength before)
        (max original.length (familyMaximumLength after)) := by
    simp [maximum, familyMaximumLength_append]
  have hmaximumReplacement :
      familyMaximumLength (before ++ replacement :: after) = maximum := by
    simp only [familyMaximumLength_append, familyMaximumLength_cons]
    omega
  have hcount :
      familyMaximalCount (before ++ replacement :: after) =
        familyMaximalCount (before ++ original :: after) := by
    rw [familyMaximalCount_eq_countLength, familyMaximalCount_eq_countLength,
      hmaximumReplacement]
    change familyCountLength maximum (before ++ replacement :: after) =
      familyCountLength maximum (before ++ original :: after)
    simp only [familyCountLength_append, familyCountLength_cons]
    simp [horiginalNe, hreplacementNe]
  have htotal :
      familyTotalSize (before ++ replacement :: after) <
        familyTotalSize (before ++ original :: after) := by
    simp only [familyTotalSize_append, familyTotalSize_cons]
    omega
  rw [FamilyRecursionMeasure.less_iff]
  exact Or.inr ⟨hmaximumReplacement,
    Or.inr ⟨hcount, htotal⟩⟩

/-- Removing a lower-degree focused column decreases the lexicographic measure. -/
theorem familyRecursionMeasure_remove_lower {A : Type*}
    (before after : List (DensePolynomial A))
    (original : DensePolynomial A)
    (hlower : original.length <
      familyMaximumLength (before ++ original :: after)) :
    familyRecursionMeasure (before ++ after) <
      familyRecursionMeasure (before ++ original :: after) := by
  let maximum := familyMaximumLength (before ++ original :: after)
  have horiginalNe : original.length ≠ maximum := ne_of_lt hlower
  have hmaximumOriginal :
      maximum = max (familyMaximumLength before)
        (max original.length (familyMaximumLength after)) := by
    simp [maximum, familyMaximumLength_append]
  have hmaximumRemoved :
      familyMaximumLength (before ++ after) = maximum := by
    simp only [familyMaximumLength_append]
    omega
  have hcount :
      familyMaximalCount (before ++ after) =
        familyMaximalCount (before ++ original :: after) := by
    rw [familyMaximalCount_eq_countLength, familyMaximalCount_eq_countLength,
      hmaximumRemoved]
    change familyCountLength maximum (before ++ after) =
      familyCountLength maximum (before ++ original :: after)
    simp only [familyCountLength_append, familyCountLength_cons]
    simp [horiginalNe]
  have htotal :
      familyTotalSize (before ++ after) <
        familyTotalSize (before ++ original :: after) := by
    simp only [familyTotalSize_append, familyTotalSize_cons]
    omega
  rw [FamilyRecursionMeasure.less_iff]
  exact Or.inr ⟨hmaximumRemoved,
    Or.inr ⟨hcount, htotal⟩⟩

end MathUE.RealQuantifierElimination

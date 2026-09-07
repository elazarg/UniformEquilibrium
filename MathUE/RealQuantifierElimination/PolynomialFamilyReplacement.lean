import MathUE.Polynomial.DensePolynomial
import MathUE.RealQuantifierElimination.PolynomialFamilyMeasure

/-!
# Polynomial-family replacement for sign-diagram recursion

A zipper records the chosen polynomial without losing its position in the
original family.  The replacement family puts its derivative first, retains
all other inputs in their original order, and appends pseudo-remainders in the
same order as an explicit divisor list.
-/

namespace MathUE.RealQuantifierElimination

open Math.DensePolynomial

variable {A : Type*}

/-- A polynomial family focused at one selected member. -/
structure PolynomialFamilyFocus (A : Type*) where
  before : List (Math.DensePolynomial A)
  selected : Math.DensePolynomial A
  after : List (Math.DensePolynomial A)

namespace PolynomialFamilyFocus

/-- The original family represented by a focus. -/
def original (focus : PolynomialFamilyFocus A) : List (Math.DensePolynomial A) :=
  focus.before ++ focus.selected :: focus.after

/-- The original family with the selected polynomial removed. -/
def retained (focus : PolynomialFamilyFocus A) : List (Math.DensePolynomial A) :=
  focus.before ++ focus.after

/-- Divisors required to reconstruct the selected polynomial's signs: its
derivative, followed by the retained formally nonconstant inputs. -/
def replacementDivisors [Zero A] [Add A] (focus : PolynomialFamilyFocus A) :
    List (Math.DensePolynomial A) :=
  derivative focus.selected ::
    focus.retained.filter (fun polynomial => decide (1 < polynomial.length))

/-- Pseudo-remainders aligned position-for-position with
`replacementDivisors`. -/
def replacementRemainders [Zero A] [Add A] [Neg A] [Mul A]
    (focus : PolynomialFamilyFocus A) : List (Math.DensePolynomial A) :=
  focus.replacementDivisors.map fun divisor =>
    (pseudoDivide focus.selected divisor).remainder

/-- One Cohen-Hormander recursion family. -/
def replacement [Zero A] [Add A] [Neg A] [Mul A]
    (focus : PolynomialFamilyFocus A) : List (Math.DensePolynomial A) :=
  derivative focus.selected :: focus.retained ++ focus.replacementRemainders

@[simp] theorem replacement_head [Zero A] [Add A] [Neg A] [Mul A]
    (focus : PolynomialFamilyFocus A) :
    focus.replacement.head? = some (derivative focus.selected) :=
  rfl

/-- Dropping the derivative and taking the retained-family length recovers the
retained inputs in their original order. -/
theorem replacement_retained_slice [Zero A] [Add A] [Neg A] [Mul A]
    (focus : PolynomialFamilyFocus A) :
    focus.replacement.tail.take focus.retained.length = focus.retained := by
  simp [replacement]

/-- Dropping the derivative and retained prefix recovers the aligned remainder
suffix exactly. -/
theorem replacement_remainder_suffix [Zero A] [Add A] [Neg A] [Mul A]
    (focus : PolynomialFamilyFocus A) :
    focus.replacement.tail.drop focus.retained.length = focus.replacementRemainders := by
  simp [replacement]

@[simp] theorem length_replacementRemainders [Zero A] [Add A] [Neg A] [Mul A]
    (focus : PolynomialFamilyFocus A) :
    focus.replacementRemainders.length = focus.replacementDivisors.length := by
  simp [replacementRemainders]

/-- After preprocessing has classified every retained input as nonconstant,
the divisor list is literally the derivative followed by the retained family. -/
theorem replacementDivisors_eq_derivative_cons_retained [Zero A] [Add A]
    (focus : PolynomialFamilyFocus A)
    (hnonconstant : ∀ polynomial ∈ focus.retained, 1 < polynomial.length) :
    focus.replacementDivisors = derivative focus.selected :: focus.retained := by
  rw [replacementDivisors]
  congr 1
  apply List.filter_eq_self.mpr
  intro polynomial hmem
  exact decide_eq_true (hnonconstant polynomial hmem)

/-- Under the all-nonconstant preprocessing invariant, successor divisor
indices point to the same retained base columns. -/
theorem replacementDivisors_get?_succ [Zero A] [Add A]
    (focus : PolynomialFamilyFocus A)
    (hnonconstant : ∀ polynomial ∈ focus.retained, 1 < polynomial.length)
    (index : Nat) :
    focus.replacementDivisors[index + 1]? = focus.retained[index]? := by
  rw [replacementDivisors_eq_derivative_cons_retained focus hnonconstant]
  simp

/-- The `index`th remainder corresponds to the `index`th explicit divisor. -/
theorem replacementRemainders_getElem [Zero A] [Add A] [Neg A] [Mul A]
    (focus : PolynomialFamilyFocus A) (index : Nat)
    (hindex : index < focus.replacementDivisors.length) :
    focus.replacementRemainders[index]'(by simpa using hindex) =
      (pseudoDivide focus.selected focus.replacementDivisors[index]).remainder := by
  simp [replacementRemainders]

theorem derivative_length_lt_selected [Zero A] [Add A]
    (focus : PolynomialFamilyFocus A) (hnonconstant : 2 ≤ focus.selected.length) :
    (derivative focus.selected).length < focus.selected.length := by
  rw [length_derivative]
  omega

theorem replacementDivisors_nonempty [Zero A] [Add A]
    (focus : PolynomialFamilyFocus A) (hnonconstant : 2 ≤ focus.selected.length) :
    ∀ divisor ∈ focus.replacementDivisors, divisor ≠ [] := by
  intro divisor hdivisor
  rw [replacementDivisors, List.mem_cons] at hdivisor
  rcases hdivisor with rfl | hretained
  · intro hempty
    have := congrArg List.length hempty
    rw [length_derivative] at this
    simp only [List.length_nil] at this
    omega
  · have hlength : 1 < divisor.length := by
      exact of_decide_eq_true (List.mem_filter.mp hretained).2
    exact List.length_pos_iff.mp (by omega)

theorem replacementDivisors_length_le_selected [Zero A] [Add A]
    (focus : PolynomialFamilyFocus A)
    (hmaximal : ∀ polynomial ∈ focus.retained,
      polynomial.length ≤ focus.selected.length) :
    ∀ divisor ∈ focus.replacementDivisors,
      divisor.length ≤ focus.selected.length := by
  intro divisor hdivisor
  rw [replacementDivisors, List.mem_cons] at hdivisor
  rcases hdivisor with rfl | hretained
  · rw [length_derivative]
    omega
  · exact hmaximal divisor (List.mem_filter.mp hretained).1

theorem replacementRemainders_length_lt_selected
    [Zero A] [Add A] [Neg A] [Mul A]
    (focus : PolynomialFamilyFocus A) (hnonconstant : 2 ≤ focus.selected.length)
    (hmaximal : ∀ polynomial ∈ focus.retained,
      polynomial.length ≤ focus.selected.length) :
    ∀ remainder ∈ focus.replacementRemainders,
      remainder.length < focus.selected.length := by
  intro remainder hremainder
  rw [replacementRemainders, List.mem_map] at hremainder
  obtain ⟨divisor, hdivisor, rfl⟩ := hremainder
  exact (pseudoDivide_remainder_length_lt focus.selected
    (focus.replacementDivisors_nonempty hnonconstant divisor hdivisor)).trans_le
      (focus.replacementDivisors_length_le_selected hmaximal divisor hdivisor)

theorem replacement_length_le_selected [Zero A] [Add A] [Neg A] [Mul A]
    (focus : PolynomialFamilyFocus A) (hnonconstant : 2 ≤ focus.selected.length)
    (hmaximal : ∀ polynomial ∈ focus.retained,
      polynomial.length ≤ focus.selected.length) :
    ∀ polynomial ∈ focus.replacement,
      polynomial.length ≤ focus.selected.length := by
  intro polynomial hpolynomial
  simp only [PolynomialFamilyFocus.replacement, List.mem_cons,
    List.mem_append] at hpolynomial
  rcases hpolynomial with (rfl | hretained) | hremainder
  · exact (focus.derivative_length_lt_selected hnonconstant).le
  · exact hmaximal polynomial hretained
  · exact (focus.replacementRemainders_length_lt_selected
      hnonconstant hmaximal polynomial hremainder).le

end PolynomialFamilyFocus


theorem familyMaximumLength_le {family : List (Math.DensePolynomial A)} {bound : Nat}
    (hbound : ∀ polynomial ∈ family, polynomial.length ≤ bound) :
    familyMaximumLength family ≤ bound := by
  induction family with
  | nil => simp [familyMaximumLength]
  | cons head tail ih =>
      rw [familyMaximumLength_cons, max_le_iff]
      exact ⟨hbound head (by simp), ih fun polynomial hmem =>
        hbound polynomial (by simp [hmem])⟩

theorem familyMaximumLength_eq {family : List (Math.DensePolynomial A)} {bound : Nat}
    (hbound : ∀ polynomial ∈ family, polynomial.length ≤ bound)
    (hwitness : ∃ polynomial ∈ family, polynomial.length = bound) :
    familyMaximumLength family = bound := by
  apply Nat.le_antisymm (familyMaximumLength_le hbound)
  obtain ⟨polynomial, hmem, rfl⟩ := hwitness
  exact length_le_familyMaximumLength hmem

theorem familyMaximumLength_lt {family : List (Math.DensePolynomial A)} {bound : Nat}
    (hboundPos : 0 < bound)
    (hbound : ∀ polynomial ∈ family, polynomial.length < bound) :
    familyMaximumLength family < bound := by
  cases bound with
  | zero => omega
  | succ bound =>
      apply Nat.lt_succ_iff.mpr
      apply familyMaximumLength_le
      intro polynomial hmem
      exact Nat.le_of_lt_succ (hbound polynomial hmem)

theorem PolynomialFamilyFocus.original_length_le_selected
    (focus : PolynomialFamilyFocus A)
    (hmaximal : ∀ polynomial ∈ focus.retained,
      polynomial.length ≤ focus.selected.length) :
    ∀ polynomial ∈ focus.original, polynomial.length ≤ focus.selected.length := by
  intro polynomial hpolynomial
  simp only [PolynomialFamilyFocus.original, List.mem_append,
    List.mem_cons] at hpolynomial
  rcases hpolynomial with hbefore | rfl | hafter
  · exact hmaximal polynomial (by
      simp [PolynomialFamilyFocus.retained, hbefore])
  · exact le_rfl
  · exact hmaximal polynomial (by
      simp [PolynomialFamilyFocus.retained, hafter])

theorem PolynomialFamilyFocus.selected_mem_original
    (focus : PolynomialFamilyFocus A) : focus.selected ∈ focus.original := by
  simp [PolynomialFamilyFocus.original]

theorem PolynomialFamilyFocus.original_maximum_eq_selected
    (focus : PolynomialFamilyFocus A)
    (hmaximal : ∀ polynomial ∈ focus.retained,
      polynomial.length ≤ focus.selected.length) :
    familyMaximumLength focus.original = focus.selected.length := by
  apply familyMaximumLength_eq (focus.original_length_le_selected hmaximal)
  exact ⟨focus.selected, focus.selected_mem_original, rfl⟩

theorem PolynomialFamilyFocus.retained_mem_replacement
    [Zero A] [Add A] [Neg A] [Mul A]
    (focus : PolynomialFamilyFocus A) {polynomial : Math.DensePolynomial A}
    (hpolynomial : polynomial ∈ focus.retained) :
    polynomial ∈ focus.replacement := by
  simp [PolynomialFamilyFocus.replacement, hpolynomial]

theorem PolynomialFamilyFocus.replacement_maximum_eq_selected_of_retained_tie
    [Zero A] [Add A] [Neg A] [Mul A]
    (focus : PolynomialFamilyFocus A) (hnonconstant : 2 ≤ focus.selected.length)
    (hmaximal : ∀ polynomial ∈ focus.retained,
      polynomial.length ≤ focus.selected.length)
    (htie : ∃ polynomial ∈ focus.retained,
      polynomial.length = focus.selected.length) :
    familyMaximumLength focus.replacement = focus.selected.length := by
  apply familyMaximumLength_eq (focus.replacement_length_le_selected
    hnonconstant hmaximal)
  obtain ⟨polynomial, hretained, hlength⟩ := htie
  exact ⟨polynomial, focus.retained_mem_replacement hretained, hlength⟩

theorem PolynomialFamilyFocus.replacement_maximum_lt_selected_of_no_retained_tie
    [Zero A] [Add A] [Neg A] [Mul A]
    (focus : PolynomialFamilyFocus A) (hnonconstant : 2 ≤ focus.selected.length)
    (hmaximal : ∀ polynomial ∈ focus.retained,
      polynomial.length ≤ focus.selected.length)
    (hnoTie : ∀ polynomial ∈ focus.retained,
      polynomial.length ≠ focus.selected.length) :
    familyMaximumLength focus.replacement < focus.selected.length := by
  apply familyMaximumLength_lt (by omega)
  intro polynomial hpolynomial
  simp only [PolynomialFamilyFocus.replacement, List.mem_append,
    List.mem_cons] at hpolynomial
  rcases hpolynomial with (rfl | hretained) | hremainder
  · exact focus.derivative_length_lt_selected hnonconstant
  · exact (hmaximal polynomial hretained).lt_of_ne (hnoTie polynomial hretained)
  · exact focus.replacementRemainders_length_lt_selected
      hnonconstant hmaximal polynomial hremainder

theorem countP_length_eq_zero_of_forall_ne
    (family : List (Math.DensePolynomial A)) (length : Nat)
    (hne : ∀ polynomial ∈ family, polynomial.length ≠ length) :
    family.countP (fun polynomial => polynomial.length = length) = 0 := by
  induction family with
  | nil => rfl
  | cons polynomial family ih =>
      rw [List.countP_cons]
      have hhead := hne polynomial (by simp)
      have hdecide : decide (polynomial.length = length) ≠ true := by
        simp [hhead]
      rw [if_neg hdecide, ih]
      intro member hmember
      exact hne member (by simp [hmember])

theorem PolynomialFamilyFocus.original_maximalCount_eq_retained_add_one
    (focus : PolynomialFamilyFocus A)
    (hmaximum : familyMaximumLength focus.original = focus.selected.length) :
    familyMaximalCount focus.original =
      focus.retained.countP
        (fun polynomial => polynomial.length = focus.selected.length) + 1 := by
  rw [familyMaximalCount, hmaximum]
  simp only [PolynomialFamilyFocus.original, PolynomialFamilyFocus.retained,
    List.countP_append, List.countP_cons]
  rw [if_pos (by simp)]
  omega

theorem PolynomialFamilyFocus.replacement_maximalCount_eq_retained
    [Zero A] [Add A] [Neg A] [Mul A]
    (focus : PolynomialFamilyFocus A) (hnonconstant : 2 ≤ focus.selected.length)
    (hmaximal : ∀ polynomial ∈ focus.retained,
      polynomial.length ≤ focus.selected.length)
    (hmaximum : familyMaximumLength focus.replacement = focus.selected.length) :
    familyMaximalCount focus.replacement =
      focus.retained.countP
        (fun polynomial => polynomial.length = focus.selected.length) := by
  rw [familyMaximalCount, hmaximum]
  simp only [PolynomialFamilyFocus.replacement, List.countP_append,
    List.countP_cons]
  have hderivative :
      decide ((derivative focus.selected).length = focus.selected.length) ≠ true := by
    simp [ne_of_lt (focus.derivative_length_lt_selected hnonconstant)]
  rw [if_neg hderivative]
  have hremainders :
      focus.replacementRemainders.countP
          (fun polynomial => polynomial.length = focus.selected.length) = 0 := by
    apply countP_length_eq_zero_of_forall_ne
    intro remainder hremainder
    exact ne_of_lt (focus.replacementRemainders_length_lt_selected
      hnonconstant hmaximal remainder hremainder)
  rw [hremainders]
  omega

/-- Replacing one chosen maximal nonconstant input by its derivative and
aligned pseudo-remainders strictly decreases the shared lexicographic family
measure. -/
theorem PolynomialFamilyFocus.replacement_recursionMeasure_lt
    [Zero A] [Add A] [Neg A] [Mul A]
    (focus : PolynomialFamilyFocus A) (hnonconstant : 2 ≤ focus.selected.length)
    (hmaximal : ∀ polynomial ∈ focus.retained,
      polynomial.length ≤ focus.selected.length) :
    familyRecursionMeasure focus.replacement < familyRecursionMeasure focus.original := by
  rw [FamilyRecursionMeasure.less_iff]
  have horiginal := focus.original_maximum_eq_selected hmaximal
  by_cases htie : ∃ polynomial ∈ focus.retained,
      polynomial.length = focus.selected.length
  · right
    have hreplacement := focus.replacement_maximum_eq_selected_of_retained_tie
      hnonconstant hmaximal htie
    refine ⟨?_, Or.inl ?_⟩
    · change familyMaximumLength focus.replacement = familyMaximumLength focus.original
      exact hreplacement.trans horiginal.symm
    · change familyMaximalCount focus.replacement < familyMaximalCount focus.original
      rw [focus.replacement_maximalCount_eq_retained hnonconstant hmaximal hreplacement,
        focus.original_maximalCount_eq_retained_add_one horiginal]
      omega
  · left
    change familyMaximumLength focus.replacement < familyMaximumLength focus.original
    have hnoTie : ∀ polynomial ∈ focus.retained,
        polynomial.length ≠ focus.selected.length := by
      intro polynomial hretained hequal
      exact htie ⟨polynomial, hretained, hequal⟩
    exact (focus.replacement_maximum_lt_selected_of_no_retained_tie
      hnonconstant hmaximal hnoTie).trans_eq horiginal.symm

end MathUE.RealQuantifierElimination

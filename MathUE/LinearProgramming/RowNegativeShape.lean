import MathUE.LinearProgramming.ColumnSumQ

/-! # A row-scaling and relabeling invariant obstructing circulant matrices -/

noncomputable section

namespace Math.LinearProgramming

variable {I : Type} [Fintype I] [DecidableEq I]

def negativeColumns (M : Matrix I I ℝ) (i : I) : Finset I :=
  Finset.univ.filter fun j ↦ M i j < 0

def negativeRowSum (M : Matrix I I ℝ) (i : I) : ℝ :=
  ∑ j ∈ negativeColumns M i, M i j

def negativeRowSquareSum (M : Matrix I I ℝ) (i : I) : ℝ :=
  ∑ j ∈ negativeColumns M i, (M i j) ^ 2

/-- The squared sum divided by the sum of squares of negative entries is
the same in every row, expressed without division to include zero rows. -/
def HasUniformNegativeRowShape (M : Matrix I I ℝ) : Prop :=
  ∀ i k, (negativeRowSum M i) ^ 2 * negativeRowSquareSum M k =
    (negativeRowSum M k) ^ 2 * negativeRowSquareSum M i

def positiveRowScale (scale : I → ℝ) (M : Matrix I I ℝ) : Matrix I I ℝ :=
  fun i j ↦ scale i * M i j

omit [DecidableEq I] in
theorem negativeColumns_positiveRowScale (scale : I → ℝ)
    (M : Matrix I I ℝ) (hscale : ∀ i, 0 < scale i) (i : I) :
    negativeColumns (positiveRowScale scale M) i = negativeColumns M i := by
  ext j
  simp [negativeColumns, positiveRowScale, mul_neg_iff, hscale i,
    not_lt_of_ge (hscale i).le]

omit [DecidableEq I] in
theorem negativeRowSum_positiveRowScale (scale : I → ℝ)
    (M : Matrix I I ℝ) (hscale : ∀ i, 0 < scale i) (i : I) :
    negativeRowSum (positiveRowScale scale M) i =
      scale i * negativeRowSum M i := by
  rw [negativeRowSum, negativeColumns_positiveRowScale scale M hscale]
  simp [negativeRowSum, positiveRowScale, Finset.mul_sum]

omit [DecidableEq I] in
theorem negativeRowSquareSum_positiveRowScale (scale : I → ℝ)
    (M : Matrix I I ℝ) (hscale : ∀ i, 0 < scale i) (i : I) :
    negativeRowSquareSum (positiveRowScale scale M) i =
      (scale i) ^ 2 * negativeRowSquareSum M i := by
  rw [negativeRowSquareSum, negativeColumns_positiveRowScale scale M hscale]
  simp [negativeRowSquareSum, positiveRowScale, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq I] in
theorem hasUniformNegativeRowShape_positiveRowScale_iff
    (scale : I → ℝ) (M : Matrix I I ℝ) (hscale : ∀ i, 0 < scale i) :
    HasUniformNegativeRowShape (positiveRowScale scale M) ↔
      HasUniformNegativeRowShape M := by
  simp only [HasUniformNegativeRowShape,
    negativeRowSum_positiveRowScale scale M hscale,
    negativeRowSquareSum_positiveRowScale scale M hscale]
  constructor <;> intro h i k
  · have hik := h i k
    have hnonzero : (scale i) ^ 2 * (scale k) ^ 2 ≠ 0 := by
      exact mul_ne_zero (pow_ne_zero _ (ne_of_gt (hscale i)))
        (pow_ne_zero _ (ne_of_gt (hscale k)))
    apply (mul_left_cancel₀ hnonzero)
    convert hik using 1 <;> ring
  · specialize h i k
    calc
      (scale i * negativeRowSum M i) ^ 2 *
          ((scale k) ^ 2 * negativeRowSquareSum M k) =
        (scale i) ^ 2 * (scale k) ^ 2 *
          ((negativeRowSum M i) ^ 2 * negativeRowSquareSum M k) := by ring
      _ = (scale i) ^ 2 * (scale k) ^ 2 *
          ((negativeRowSum M k) ^ 2 * negativeRowSquareSum M i) := by rw [h]
      _ = (scale k * negativeRowSum M k) ^ 2 *
          ((scale i) ^ 2 * negativeRowSquareSum M i) := by ring

omit [DecidableEq I] in
theorem negativeRowSum_eq_sum_ite (M : Matrix I I ℝ) (i : I) :
    negativeRowSum M i = ∑ j, if M i j < 0 then M i j else 0 := by
  simp [negativeRowSum, negativeColumns, Finset.sum_filter]

omit [DecidableEq I] in
theorem negativeRowSquareSum_eq_sum_ite (M : Matrix I I ℝ) (i : I) :
    negativeRowSquareSum M i = ∑ j, if M i j < 0 then (M i j) ^ 2 else 0 := by
  simp [negativeRowSquareSum, negativeColumns, Finset.sum_filter]

variable {K : Type} [Fintype K]

omit [DecidableEq I] in
theorem negativeRowSum_reindexMatrix (e : I ≃ K) (M : Matrix I I ℝ) (i : K) :
    negativeRowSum (reindexMatrix e M) i = negativeRowSum M (e.symm i) := by
  rw [negativeRowSum_eq_sum_ite, negativeRowSum_eq_sum_ite]
  change (∑ j : K, if M (e.symm i) (e.symm j) < 0 then
    M (e.symm i) (e.symm j) else 0) = _
  exact Equiv.sum_comp e.symm
    (fun j : I ↦ if M (e.symm i) j < 0 then M (e.symm i) j else 0)

omit [DecidableEq I] in
theorem negativeRowSquareSum_reindexMatrix
    (e : I ≃ K) (M : Matrix I I ℝ) (i : K) :
    negativeRowSquareSum (reindexMatrix e M) i =
      negativeRowSquareSum M (e.symm i) := by
  rw [negativeRowSquareSum_eq_sum_ite, negativeRowSquareSum_eq_sum_ite]
  change (∑ j : K, if M (e.symm i) (e.symm j) < 0 then
    (M (e.symm i) (e.symm j)) ^ 2 else 0) = _
  exact Equiv.sum_comp e.symm
    (fun j : I ↦ if M (e.symm i) j < 0 then (M (e.symm i) j) ^ 2 else 0)

omit [DecidableEq I] in
theorem hasUniformNegativeRowShape_reindexMatrix_iff
    (e : I ≃ K) (M : Matrix I I ℝ) :
    HasUniformNegativeRowShape (reindexMatrix e M) ↔
      HasUniformNegativeRowShape M := by
  constructor
  · intro h i k
    simpa [HasUniformNegativeRowShape, negativeRowSum_reindexMatrix,
      negativeRowSquareSum_reindexMatrix] using h (e i) (e k)
  · intro h i k
    simpa [HasUniformNegativeRowShape, negativeRowSum_reindexMatrix,
      negativeRowSquareSum_reindexMatrix] using h (e.symm i) (e.symm k)

section Circulant

variable [AddCommGroup I]

omit [DecidableEq I] in
theorem negativeRowSum_rowCirculant (m : I → ℝ) (i : I) :
    negativeRowSum (rowCirculant m) i = negativeRowSum (rowCirculant m) 0 := by
  rw [negativeRowSum_eq_sum_ite, negativeRowSum_eq_sum_ite]
  apply Fintype.sum_equiv (Equiv.subRight i)
  intro j
  simp [rowCirculant]

omit [DecidableEq I] in
theorem negativeRowSquareSum_rowCirculant (m : I → ℝ) (i : I) :
    negativeRowSquareSum (rowCirculant m) i =
      negativeRowSquareSum (rowCirculant m) 0 := by
  rw [negativeRowSquareSum_eq_sum_ite, negativeRowSquareSum_eq_sum_ite]
  apply Fintype.sum_equiv (Equiv.subRight i)
  intro j
  simp [rowCirculant]

omit [DecidableEq I] in
theorem hasUniformNegativeRowShape_rowCirculant (m : I → ℝ) :
    HasUniformNegativeRowShape (rowCirculant m) := by
  intro i k
  rw [negativeRowSum_rowCirculant m i, negativeRowSum_rowCirculant m k,
    negativeRowSquareSum_rowCirculant m i,
    negativeRowSquareSum_rowCirculant m k]

/-- A simultaneous row/column relabeling followed by positive row scaling
makes the matrix circulant with respect to the given additive indexing. -/
def IsPositiveRowScaledRelabelingRowCirculant (M : Matrix I I ℝ) : Prop :=
  ∃ (e : I ≃ I) (scale margin : I → ℝ), (∀ i, 0 < scale i) ∧
    positiveRowScale scale (reindexMatrix e M) = rowCirculant margin

omit [DecidableEq I] in
theorem hasUniformNegativeRowShape_of_positiveRowScaledRelabelingRowCirculant
    {M : Matrix I I ℝ} (h : IsPositiveRowScaledRelabelingRowCirculant M) :
    HasUniformNegativeRowShape M := by
  obtain ⟨e, scale, margin, hscale, heq⟩ := h
  have hcirc : HasUniformNegativeRowShape
      (positiveRowScale scale (reindexMatrix e M)) := by
    rw [heq]
    exact hasUniformNegativeRowShape_rowCirculant margin
  have hreindexed :=
    (hasUniformNegativeRowShape_positiveRowScale_iff scale _ hscale).1 hcirc
  exact (hasUniformNegativeRowShape_reindexMatrix_iff e M).1 hreindexed

end Circulant

end Math.LinearProgramming

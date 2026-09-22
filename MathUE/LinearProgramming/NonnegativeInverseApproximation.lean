import MathUE.LinearProgramming.PositiveInverseOpenness
import MathUE.LinearAlgebra.UniformNonsingularity
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Strict inverse approximation preserving the diagonal

In dimension at least three, subtracting a sufficiently small positive multiple
of the off-diagonal-ones matrix turns an entrywise nonnegative inverse into a
strictly positive inverse. The second-order Neumann coefficient fills the
entries which the first-order coefficient misses. No diagonal hypothesis is
imposed on the original matrix.
-/

noncomputable section

namespace Math.LinearProgramming

open Filter Math.LinearAlgebra
open scoped Topology Matrix.Norms.Operator

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem nonneg_matrix_mul {A B : Matrix ι ι ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j) :
    ∀ i j, 0 ≤ (A * B) i j := by
  intro i j
  exact Finset.sum_nonneg fun k _ => mul_nonneg (hA i k) (hB k j)

omit [DecidableEq ι] in
private theorem pos_matrix_mul {A B : Matrix ι ι ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j)
    (i k j : ι) (ha : 0 < A i k) (hb : 0 < B k j) : 0 < (A * B) i j := by
  exact Finset.sum_pos' (fun l _ => mul_nonneg (hA i l) (hB l j))
    ⟨k, Finset.mem_univ k, mul_pos ha hb⟩

omit [Fintype ι] in
private theorem offDiagonalOnes_nonneg (i j : ι) : 0 ≤ offDiagonalOnes ι i j := by
  simp only [offDiagonalOnes]
  split_ifs <;> norm_num

private theorem exists_positive_permutation (B : Matrix ι ι ℝ)
    (hdet : B.det ≠ 0) (hB : ∀ i j, 0 ≤ B i j) :
    ∃ order : Equiv.Perm ι, ∀ j, 0 < B (order j) j := by
  by_contra hnone
  push Not at hnone
  apply hdet
  rw [Matrix.det_apply']
  apply Finset.sum_eq_zero
  intro order _
  obtain ⟨j, hj⟩ := hnone order
  have hzero : B (order j) j = 0 := le_antisymm hj (hB _ _)
  have hprod : (∏ k, B (order k) k) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ j) hzero
  rw [hprod, mul_zero]

private theorem exists_positive_entry_away (B : Matrix ι ι ℝ)
    (hcard : 3 ≤ Fintype.card ι) (hdet : B.det ≠ 0)
    (hB : ∀ i j, 0 ≤ B i j) (k : ι) :
    ∃ u v, u ≠ k ∧ v ≠ k ∧ 0 < B u v := by
  obtain ⟨order, horder⟩ := exists_positive_permutation B hdet hB
  have hexists : ∃ v : ι, v ∉ ({k, order.symm k} : Finset ι) := by
    by_contra hnone
    push Not at hnone
    have hsubset : (Finset.univ : Finset ι) ⊆ {k, order.symm k} :=
      fun v _ => hnone v
    have hle := Finset.card_le_card hsubset
    have hpair : ({k, order.symm k} : Finset ι).card ≤ 2 := by
      exact (Finset.card_insert_le _ _).trans (by simp)
    rw [Finset.card_univ] at hle
    omega
  obtain ⟨v, hv⟩ := hexists
  have hvk : v ≠ k := fun h => hv (by simp [h])
  have hvother : v ≠ order.symm k := fun h => hv (by simp [h])
  refine ⟨order v, v, ?_, hvk, horder v⟩
  intro h
  exact hvother (order.injective (by simpa using h))

/-- One of the first two correction coefficients is positive at every entry.
Invertibility and dimension at least three supply an entry outside any selected
row and column; no irreducibility or positive diagonal is required. -/
theorem first_or_second_inverse_correction_pos
    (B : Matrix ι ι ℝ) (hcard : 3 ≤ Fintype.card ι)
    (hdet : B.det ≠ 0) (hB : ∀ i j, 0 ≤ B i j) (i j : ι) :
    0 < (B * offDiagonalOnes ι * B) i j ∨
      0 < (B * offDiagonalOnes ι * B * offDiagonalOnes ι * B) i j := by
  obtain ⟨order, horder⟩ := exists_positive_permutation B hdet hB
  let k := order.symm i
  let l := order j
  have hik : 0 < B i k := by simpa [k] using horder (order.symm i)
  have hlj : 0 < B l j := horder j
  have hK := offDiagonalOnes_nonneg (ι := ι)
  have hBK := nonneg_matrix_mul hB hK
  have hBKB := nonneg_matrix_mul hBK hB
  have hBKBK := nonneg_matrix_mul hBKB hK
  by_cases hkl : k = l
  · obtain ⟨u, v, huk, hvk, huv⟩ := exists_positive_entry_away B hcard hdet hB k
    have hiku : 0 < (B * offDiagonalOnes ι) i u :=
      pos_matrix_mul hB hK i k u hik (by simp [offDiagonalOnes, Ne.symm huk])
    have hikuv : 0 < (B * offDiagonalOnes ι * B) i v :=
      pos_matrix_mul hBK hB i u v hiku huv
    have hikuvk : 0 < (B * offDiagonalOnes ι * B * offDiagonalOnes ι) i k :=
      pos_matrix_mul hBKB hK i v k hikuv (by simp [offDiagonalOnes, hvk])
    exact Or.inr (pos_matrix_mul hBKBK hB i k j hikuvk (hkl.symm ▸ hlj))
  · have hikl : 0 < (B * offDiagonalOnes ι) i l :=
      pos_matrix_mul hB hK i k l hik (by simp [offDiagonalOnes, hkl])
    exact Or.inl (pos_matrix_mul hBK hB i l j hikl hlj)

private theorem nonneg_matrix_pow {A : Matrix ι ι ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (power : ℕ) : ∀ i j, 0 ≤ (A ^ power) i j := by
  induction power with
  | zero =>
    intro i j
    simp only [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ power ih =>
    rw [pow_succ]
    exact nonneg_matrix_mul ih hA

private theorem strictlyPositiveInverse_sub_offDiagonalOnes_of_norm_lt_one
    (M : Matrix ι ι ℝ) (hcard : 3 ≤ Fintype.card ι) (hdet : M.det ≠ 0)
    (hinverse : ∀ i j, 0 ≤ M⁻¹ i j) {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hnorm : ‖epsilon • (M⁻¹ * offDiagonalOnes ι)‖ < 1) :
    HasStrictlyPositiveInverse (M - epsilon • offDiagonalOnes ι) := by
  let B : Matrix ι ι ℝ := M⁻¹
  let A : Matrix ι ι ℝ := epsilon • (B * offDiagonalOnes ι)
  let series : Matrix ι ι ℝ := ∑' power : ℕ, A ^ power
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have hBdet : B.det ≠ 0 :=
    isUnit_iff_ne_zero.mp (M.isUnit_nonsing_inv_det hunit)
  have hB : ∀ i j, 0 ≤ B i j := hinverse
  have hA : ∀ i j, 0 ≤ A i j := by
    intro i j
    exact mul_nonneg hepsilon.le
      (nonneg_matrix_mul hB offDiagonalOnes_nonneg i j)
  have hsummable : Summable (fun power : ℕ => A ^ power) :=
    summable_geometric_of_norm_lt_one hnorm
  have hseries : (1 - A) * series = 1 := mul_neg_geom_series A hnorm
  have hfactor : M - epsilon • offDiagonalOnes ι = M * (1 - A) := by
    dsimp only [A, B]
    rw [mul_sub, mul_one, mul_smul_comm, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv M hunit, one_mul]
  have hright : (M - epsilon • offDiagonalOnes ι) * (series * B) = 1 := by
    rw [hfactor, Matrix.mul_assoc, ← Matrix.mul_assoc (1 - A) series B,
      hseries, one_mul]
    exact Matrix.mul_nonsing_inv M hunit
  apply hasStrictlyPositiveInverse_of_rightInverse _ (series * B) hright
  intro i j
  have hsum : HasSum (fun power : ℕ => A ^ power * B) (series * B) :=
    hsummable.hasSum.mul_right B
  have hentry : HasSum (fun power : ℕ => (A ^ power * B) i j) ((series * B) i j) :=
    Pi.hasSum.mp (Pi.hasSum.mp hsum i) j
  have hnonnegative (power : ℕ) : 0 ≤ (A ^ power * B) i j :=
    nonneg_matrix_mul (nonneg_matrix_pow hA power) hB i j
  have hpositive : ∃ power : ℕ, 0 < (A ^ power * B) i j := by
    rcases first_or_second_inverse_correction_pos B hcard hBdet hB i j with hfirst | hsecond
    · refine ⟨1, ?_⟩
      simpa only [pow_one, A, smul_mul_assoc, Matrix.smul_apply, smul_eq_mul] using
        mul_pos hepsilon hfirst
    · refine ⟨2, ?_⟩
      have hequal : A ^ 2 * B = (epsilon * epsilon) •
          (B * offDiagonalOnes ι * B * offDiagonalOnes ι * B) := by
        simp only [A, pow_two, smul_mul_assoc, mul_smul_comm, smul_smul, Matrix.mul_assoc]
      rw [hequal]
      exact mul_pos (mul_pos hepsilon hepsilon) hsecond
  obtain ⟨power, hpower⟩ := hpositive
  have hpos := hentry.summable.tsum_pos hnonnegative power hpower
  rwa [hentry.tsum_eq] at hpos

/-- In dimension at least three, one positive threshold works for all positive
perturbations below it: the actual matrix inverse is strictly positive, the
determinant sign is preserved, and every diagonal entry is unchanged. -/
theorem exists_pos_strictlyPositiveInverse_sub_offDiagonalOnes
    (M : Matrix ι ι ℝ) (hcard : 3 ≤ Fintype.card ι) (hdet : M.det ≠ 0)
    (hinverse : ∀ i j, 0 ≤ M⁻¹ i j) :
    ∃ threshold : ℝ, 0 < threshold ∧ ∀ epsilon : ℝ,
      0 < epsilon → epsilon < threshold →
        HasStrictlyPositiveInverse (M - epsilon • offDiagonalOnes ι) ∧
        SignType.sign (M - epsilon • offDiagonalOnes ι).det = SignType.sign M.det ∧
        ∀ i, (M - epsilon • offDiagonalOnes ι) i i = M i i := by
  have hnormContinuous : Continuous (fun epsilon : ℝ =>
      ‖epsilon • (M⁻¹ * offDiagonalOnes ι)‖) := by fun_prop
  have hnorm : ∀ᶠ epsilon : ℝ in 𝓝 0,
      ‖epsilon • (M⁻¹ * offDiagonalOnes ι)‖ < 1 := by
    exact hnormContinuous.continuousAt.eventually
      (isOpen_Iio.mem_nhds (by simp))
  have hdetContinuous : Continuous (fun epsilon : ℝ =>
      (M - epsilon • offDiagonalOnes ι).det) := by fun_prop
  have hlimit : Tendsto (fun epsilon : ℝ => (M - epsilon • offDiagonalOnes ι).det)
      (𝓝 0) (𝓝 M.det) := by
    simpa only [zero_smul, sub_zero] using
      (hdetContinuous.continuousAt (x := (0 : ℝ))).tendsto
  have hsign : ∀ᶠ epsilon : ℝ in 𝓝 0,
      SignType.sign (M - epsilon • offDiagonalOnes ι).det = SignType.sign M.det := by
    rcases lt_or_gt_of_ne hdet with hnegative | hpositive
    · filter_upwards [hlimit.eventually (isOpen_Iio.mem_nhds hnegative)] with epsilon heps
      exact (sign_neg heps).trans (sign_neg hnegative).symm
    · filter_upwards [hlimit.eventually (isOpen_Ioi.mem_nhds hpositive)] with epsilon heps
      exact (sign_pos heps).trans (sign_pos hpositive).symm
  obtain ⟨threshold, hthreshold, hsmall⟩ :=
    Metric.eventually_nhds_iff.mp (hnorm.and hsign)
  refine ⟨threshold, hthreshold, ?_⟩
  intro epsilon hepsilon hbound
  have hnear : dist epsilon 0 < threshold := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hepsilon] using hbound
  obtain ⟨hnormSmall, hsignSmall⟩ := hsmall hnear
  refine ⟨strictlyPositiveInverse_sub_offDiagonalOnes_of_norm_lt_one
    M hcard hdet hinverse hepsilon hnormSmall, hsignSmall, ?_⟩
  intro i
  simp [offDiagonalOnes]

/-- Every zero-diagonal two-by-two matrix has zero diagonal in its matrix
inverse, including the singular case where the inverse convention gives zero. -/
theorem inverse_diagonal_eq_zero_fin_two
    (M : Matrix (Fin 2) (Fin 2) ℝ) (hdiagonal : ∀ i, M i i = 0) (i : Fin 2) :
    M⁻¹ i i = 0 := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two]
  fin_cases i <;> simp [hdiagonal]

/-- Consequently no perturbation preserving a zero diagonal in dimension two
can produce an entrywise strictly positive matrix inverse. -/
theorem not_hasStrictlyPositiveInverse_fin_two_of_diagonal_zero
    (M : Matrix (Fin 2) (Fin 2) ℝ) (hdiagonal : ∀ i, M i i = 0) :
    ¬HasStrictlyPositiveInverse M := by
  intro hpositive
  have hentry := hpositive.2 (0 : Fin 2) (0 : Fin 2)
  rw [inverse_diagonal_eq_zero_fin_two M hdiagonal] at hentry
  exact lt_irrefl (0 : ℝ) hentry

end Math.LinearProgramming

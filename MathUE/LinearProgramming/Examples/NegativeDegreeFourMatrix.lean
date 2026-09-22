import MathUE.LinearProgramming.SupportTest

/-!
# Exact support inventory of a four-dimensional three-root LCP

The zero-diagonal matrix below has three strictly complementary roots at the
negative test anchor `(1, 2, 3, 5)`. Their active principal determinants have
signs `-1, -1, +1`. The eleven-row inventory covers every support of size at
least two, including the inadmissible candidates. All entries are exact.
-/

noncomputable section

namespace Math.LinearProgramming.NegativeDegreeFourMatrix

/-- The signed zero-diagonal matrix with three test roots. -/
def matrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 7, -7, -1; 3, 0, -9, 9; 1, -1, 0, 7; -1, 5, 3, 0]

/-- A strictly positive test anchor, independent of any game payoff anchor. -/
def anchor : Fin 4 → ℝ := ![1, 2, 3, 5]

/-- All supports of size at least two, in increasing cardinality order. -/
def support : Fin 11 → Finset (Fin 4) :=
  ![{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3},
    {0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}, {0, 1, 2, 3}]

/-- Exact solutions of the active equations, extended by zero off support. -/
def candidate : Fin 11 → Fin 4 → ℝ :=
  ![![2 / 3, 1 / 7, 0, 0], ![3, 0, -1 / 7, 0], ![-5, 0, 0, -1],
    ![0, -3, -2 / 9, 0], ![0, 1, 0, 2 / 9], ![0, 0, 5 / 3, 3 / 7],
    ![92 / 21, 29 / 21, 26 / 21, 0], ![-10 / 3, 1 / 3, 0, 4 / 3],
    ![-275 / 46, 0, -15 / 46, 59 / 46], ![0, 46 / 57, 55 / 171, 31 / 57],
    ![634 / 249, 251 / 249, 208 / 249, 52 / 249]]

/-- The full residual vectors at the displayed candidates. -/
def residual : Fin 11 → Fin 4 → ℝ :=
  ![![0, 0, -52 / 21, -104 / 21], ![0, 58 / 7, 0, -59 / 7],
    ![0, -26, -15, 0], ![-184 / 9, 0, 0, -62 / 3], ![52 / 9, 0, -22 / 9, 0],
    ![-275 / 21, -92 / 7, 0, 0], ![0, 0, 0, 26 / 21], ![0, 0, 8 / 3, 0],
    ![0, -251 / 46, 0, 0], ![317 / 171, 0, 0, 0], ![0, 0, 0, 0]]

/-- The exact active principal determinants, in inventory order. -/
def determinant : Fin 11 → ℝ :=
  ![-21, 7, -1, -9, -45, -21, -42, -78, 46, -342, 249]

theorem diagonal_zero (who : Fin 4) : matrix who who = 0 := by
  fin_cases who <;> norm_num [matrix]

theorem anchor_pos (who : Fin 4) : 0 < anchor who := by
  fin_cases who <;> norm_num [anchor]

/-- The inventory covers all supports which can occur at the positive anchor. -/
theorem support_complete (selected : Finset (Fin 4)) (hcard : 2 ≤ selected.card) :
    ∃ row : Fin 11, selected = support row := by
  exact (by decide : ∀ selected : Finset (Fin 4), 2 ≤ selected.card →
    ∃ row : Fin 11, selected = support row) selected hcard

theorem candidate_zero_off_support (row : Fin 11) (who : Fin 4)
    (hwho : who ∉ support row) : candidate row who = 0 := by
  fin_cases row <;> fin_cases who <;> simp_all [support, candidate]

/-- Each tabulated residual is the literal standard-LCP residual. -/
theorem residual_eq (row : Fin 11) :
    lcpResidual matrix (-anchor) (candidate row) = residual row := by
  funext who
  fin_cases row <;> fin_cases who <;>
    norm_num [lcpResidual, matrix, anchor, candidate, residual, Fin.sum_univ_succ]

theorem residual_zero_on_support (row : Fin 11) (who : Fin 4)
    (hwho : who ∈ support row) : residual row who = 0 := by
  fin_cases row <;> fin_cases who <;> simp_all [support, residual]

/-- Each active principal determinant equals its exact tabulated value. -/
theorem principal_det_eq (row : Fin 11) :
    (matrix.toSquareBlockProp (fun who => who ∈ support row)).det = determinant row := by
  classical
  let selector : Fin 4 → ℝ := fun who => if who ∈ support row then 1 else 0
  have hpredicate (who : Fin 4) : who ∈ support row ↔ 0 < selector who := by
    dsimp only [selector]
    split_ifs <;> simp_all
  have hequal := (det_lcpSelectedMatrix matrix selector).trans
    (Matrix.equiv_block_det matrix hpredicate)
  have hfinite : Finset.Subtype.fintype (support row) =
      Subtype.fintype (fun who => who ∈ support row) := Subsingleton.elim _ _
  rw [hfinite, ← hequal, Matrix.det_succ_row_zero]
  fin_cases row <;>
    norm_num [selector, support, determinant, lcpSelectedMatrix, matrix,
      Matrix.det_fin_three, Fin.sum_univ_succ, Fin.succAbove,
      Matrix.submatrix, Matrix.one_apply]

theorem principal_det_ne_zero (row : Fin 11) :
    (matrix.toSquareBlockProp (fun who => who ∈ support row)).det ≠ 0 := by
  rw [principal_det_eq]
  fin_cases row <;> norm_num [determinant]

/-- Every column contains the explicitly displayed negative entry. -/
theorem negative_columns (column : Fin 4) : ∃ row : Fin 4, matrix row column < 0 := by
  fin_cases column
  · exact ⟨3, by norm_num [matrix]⟩
  · exact ⟨2, by norm_num [matrix]⟩
  · exact ⟨0, by norm_num [matrix]⟩
  · exact ⟨0, by norm_num [matrix]⟩

/-- The full homogeneous LCP has no nonzero solution. -/
theorem isR0Matrix : IsR0Matrix matrix := by
  apply isR0Matrix_of_negative_columns_of_nonsingular_principals matrix negative_columns
  intro selected hcard
  obtain ⟨row, rfl⟩ := support_complete selected hcard
  exact principal_det_ne_zero row

/-- Every actual test root is one of the eleven exact active-system candidates. -/
theorem exists_candidate_of_isStandardLCPSolution (root : Fin 4 → ℝ)
    (hroot : IsStandardLCPSolution matrix (-anchor) root) :
    ∃ row : Fin 11, root = candidate row := by
  classical
  let selected := Finset.univ.filter (fun who => 0 < root who)
  have hcard : 2 ≤ selected.card :=
    hroot.two_le_card_positive_support_of_zero_diagonal diagonal_zero anchor_pos
  obtain ⟨row, hrow⟩ := support_complete selected hcard
  refine ⟨row, hroot.eq_of_supported_linear_system (support row) ?_
    (principal_det_ne_zero row) (candidate row) (candidate_zero_off_support row) ?_⟩
  · intro who
    rw [← hrow]
    simp only [selected, Finset.mem_filter, Finset.mem_univ, true_and]
  · intro who hwho
    rw [residual_eq]
    exact residual_zero_on_support row who hwho

/-- Exact coordinate inequalities select precisely the three admissible rows. -/
theorem candidate_isStandardLCPSolution_iff (row : Fin 11) :
    IsStandardLCPSolution matrix (-anchor) (candidate row) ↔
      row = 6 ∨ row = 9 ∨ row = 10 := by
  have hcomplementary (who : Fin 4) : candidate row who * residual row who = 0 := by
    by_cases hwho : who ∈ support row
    · rw [residual_zero_on_support row who hwho, mul_zero]
    · rw [candidate_zero_off_support row who hwho, zero_mul]
  have hiff : IsStandardLCPSolution matrix (-anchor) (candidate row) ↔
      (∀ who, 0 ≤ candidate row who) ∧ (∀ who, 0 ≤ residual row who) := by
    constructor
    · intro hroot
      refine ⟨hroot.weight_nonneg, ?_⟩
      simpa only [residual_eq] using hroot.residual_nonneg
    · rintro ⟨hweight, hresidual⟩
      refine ⟨hweight, ?_, ?_⟩
      · simpa only [residual_eq] using hresidual
      · simpa only [residual_eq] using hcomplementary
  rw [hiff]
  fin_cases row <;> norm_num [candidate, residual, Fin.forall_fin_succ]

/-- The complete actual LCP solution set at the test anchor has three roots. -/
theorem isStandardLCPSolution_iff (root : Fin 4 → ℝ) :
    IsStandardLCPSolution matrix (-anchor) root ↔
      root = candidate 6 ∨ root = candidate 9 ∨ root = candidate 10 := by
  constructor
  · intro hroot
    obtain ⟨row, rfl⟩ := exists_candidate_of_isStandardLCPSolution root hroot
    rcases (candidate_isStandardLCPSolution_iff row).mp hroot with hrow | hrow | hrow
    · exact Or.inl (hrow ▸ rfl)
    · exact Or.inr (Or.inl (hrow ▸ rfl))
    · exact Or.inr (Or.inr (hrow ▸ rfl))
  · rintro (rfl | rfl | rfl) <;>
      apply (candidate_isStandardLCPSolution_iff _).mpr <;> simp

end Math.LinearProgramming.NegativeDegreeFourMatrix

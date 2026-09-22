import MathUE.LinearProgramming.SupportTest
import MathUE.LinearProgramming.R0DegreeSum
import Mathlib.Order.Interval.Set.Infinite

/-!
# Exact support inventory of a four-dimensional three-root LCP

The zero-diagonal matrix below has three strictly complementary roots at the
negative test anchor `(1, 2, 3, 5)`. Their active principal determinants have
signs `-1, -1, +1`. The eleven-row inventory covers every support of size at
least two, including the inadmissible candidates. All entries are exact.
The actual-root degree formula gives canonical R0 degree `-1`.
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

/-- At each admissible row the displayed support is the actual positive support. -/
theorem candidate_positive_support_iff (row : Fin 11)
    (hrow : row = 6 ∨ row = 9 ∨ row = 10) (who : Fin 4) :
    who ∈ support row ↔ 0 < candidate row who := by
  rcases hrow with rfl | rfl | rfl <;> fin_cases who <;> norm_num [support, candidate]

/-- The actual active determinant at every admissible row is its inventory value. -/
theorem candidate_active_det_eq (row : Fin 11)
    (hrow : row = 6 ∨ row = 9 ∨ row = 10) :
    (matrix.toSquareBlockProp (fun who => 0 < candidate row who)).det =
      determinant row := by
  classical
  have hvalue := principal_det_eq row
  have hfinite : Finset.Subtype.fintype (support row) =
      Subtype.fintype (fun who => who ∈ support row) := Subsingleton.elim _ _
  rw [hfinite] at hvalue
  exact (Matrix.equiv_block_det matrix (candidate_positive_support_iff row hrow)).trans
    hvalue

/-- Every actual test root has positive slack at each inactive coordinate. -/
theorem strict_complementarity (root : Fin 4 → ℝ)
    (hroot : IsStandardLCPSolution matrix (-anchor) root) :
    ∀ who, root who = 0 → 0 < lcpResidual matrix (-anchor) root who := by
  intro who hzero
  rcases (isStandardLCPSolution_iff root).mp hroot with rfl | rfl | rfl <;>
    rw [residual_eq] <;> fin_cases who <;> norm_num [candidate, residual] at *

/-- Every actual test root has a nonsingular active principal matrix. -/
theorem active_det_ne_zero (root : Fin 4 → ℝ)
    (hroot : IsStandardLCPSolution matrix (-anchor) root) :
    (matrix.toSquareBlockProp (fun who => 0 < root who)).det ≠ 0 := by
  obtain ⟨row, rfl⟩ := exists_candidate_of_isStandardLCPSolution root hroot
  rw [candidate_active_det_eq row ((candidate_isStandardLCPSolution_iff row).mp hroot)]
  fin_cases row <;> norm_num [determinant]

/-- The three actual roots, with duplicates excluded by the finite-set representation. -/
def roots : Finset (Fin 4 → ℝ) := by
  classical
  exact {candidate 6, candidate 9, candidate 10}

theorem mem_roots_iff (root : Fin 4 → ℝ) :
    root ∈ roots ↔ IsStandardLCPSolution matrix (-anchor) root := by
  classical
  simp only [roots, Finset.mem_insert, Finset.mem_singleton, isStandardLCPSolution_iff]

/-- The exact signed sum over the complete root set is `-1`, not merely odd. -/
theorem sum_sign_active_det_eq_neg_one :
    (∑ root ∈ roots,
      (SignType.sign (matrix.toSquareBlockProp (fun who => 0 < root who)).det : ℤ)) = -1 := by
  classical
  have h69 : candidate 6 ≠ candidate 9 := by
    intro hequal
    have hcoordinate := congrFun hequal 0
    norm_num [candidate] at hcoordinate
  have h610 : candidate 6 ≠ candidate 10 := by
    intro hequal
    have hcoordinate := congrFun hequal 3
    norm_num [candidate] at hcoordinate
  have h910 : candidate 9 ≠ candidate 10 := by
    intro hequal
    have hcoordinate := congrFun hequal 0
    norm_num [candidate] at hcoordinate
  simp only [roots, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    h69, h610, h910, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [candidate_active_det_eq 6 (by simp), candidate_active_det_eq 9 (by simp),
    candidate_active_det_eq 10 (by simp)]
  norm_num [determinant]

/-- Canonical total degree, computed from every actual root at the test anchor. -/
theorem r0Degree_eq_neg_one : r0Degree matrix isR0Matrix = -1 := by
  classical
  obtain ⟨actualRoots, hactualRoots, hdegree⟩ :=
    exists_finset_r0Degree_eq_sum_sign_det matrix isR0Matrix (-anchor)
      strict_complementarity active_det_ne_zero
  have hroots : actualRoots = roots := by
    ext root
    exact (hactualRoots root).trans (mem_roots_iff root).symm
  rw [hroots] at hdegree
  exact hdegree.trans sum_sign_active_det_eq_neg_one

/-- The nonzero canonical degree makes the full matrix standard Q. -/
theorem isStandardQ : IsStandardQ matrix := by
  apply isStandardQ_of_r0Degree_ne_zero matrix isR0Matrix
  rw [r0Degree_eq_neg_one]
  norm_num

/-- The full determinant is positive despite the negative total degree. -/
theorem det_eq : matrix.det = 249 := by
  have hselected : lcpSelectedMatrix matrix (candidate 10) = matrix := by
    ext who coordinate
    fin_cases who <;> simp [lcpSelectedMatrix, candidate]
  calc
    matrix.det = (lcpSelectedMatrix matrix (candidate 10)).det :=
      congrArg Matrix.det hselected.symm
    _ = (matrix.toSquareBlockProp (fun who => 0 < candidate 10 who)).det :=
      det_lcpSelectedMatrix matrix (candidate 10)
    _ = determinant 10 := candidate_active_det_eq 10 (by simp)
    _ = 249 := by norm_num [determinant]

theorem det_pos : 0 < matrix.det := by
  rw [det_eq]
  norm_num

/-- The inverse is certified by exact matrix multiplication. -/
theorem inverse_eq : matrix⁻¹ = (1 / 249 : ℝ) •
    !![-342, 389, -549, 369; -27, 46, -63, 75;
      -69, 53, -78, 81; 45, -49, 105, -42] := by
  apply Matrix.inv_eq_left_inv
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [matrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

/-- Two literal inverse entries exhibit both signs. -/
theorem inverse_has_both_signs : matrix⁻¹ 0 0 < 0 ∧ 0 < matrix⁻¹ 0 1 := by
  rw [inverse_eq]
  norm_num

theorem not_inverse_nonnegative : ¬∀ row column, 0 ≤ matrix⁻¹ row column := by
  intro hnonnegative
  exact inverse_has_both_signs.1.not_ge (hnonnegative 0 0)

/-- The reciprocal negative pair on coordinates zero and three excludes copositivity. -/
theorem not_isCopositive : ¬IsCopositive matrix := by
  intro hcopositive
  have hvalue := hcopositive ![1, 0, 0, 1] (by
    intro who
    fin_cases who <;> norm_num)
  norm_num [matrix, Fin.sum_univ_succ] at hvalue

/-- A nonnegative test anchor with a zero coordinate, not a specified game anchor. -/
def degenerateAnchor : Fin 4 → ℝ := ![7, 0, 1, 10]

/-- A proper-support root at the degenerate test anchor. -/
def degenerateRoot : Fin 4 → ℝ := ![3, 2, 1, 0]

theorem degenerateAnchor_nonnegative (who : Fin 4) : 0 ≤ degenerateAnchor who := by
  fin_cases who <;> norm_num [degenerateAnchor]

theorem degenerateAnchor_one_eq_zero : degenerateAnchor 1 = 0 := rfl

/-- Every slack vanishes, including the inactive fourth coordinate. -/
theorem degenerateRoot_residual_eq_zero :
    lcpResidual matrix (-degenerateAnchor) degenerateRoot = 0 := by
  funext who
  fin_cases who <;>
    norm_num [lcpResidual, matrix, degenerateAnchor, degenerateRoot, Fin.sum_univ_succ]

theorem degenerateRoot_isStandardLCPSolution :
    IsStandardLCPSolution matrix (-degenerateAnchor) degenerateRoot := by
  refine ⟨?_, ?_, ?_⟩
  · intro who
    fin_cases who <;> norm_num [degenerateRoot]
  · intro who
    rw [degenerateRoot_residual_eq_zero]
    exact le_rfl
  · intro who
    rw [degenerateRoot_residual_eq_zero]
    exact mul_zero _

/-- R0 does not force strict complementarity at every inhomogeneous root. -/
theorem degenerateRoot_not_strict :
    ¬∀ who, degenerateRoot who = 0 →
      0 < lcpResidual matrix (-degenerateAnchor) degenerateRoot who := by
  intro hstrict
  have hpositive := hstrict 3 (by rfl)
  rw [degenerateRoot_residual_eq_zero] at hpositive
  exact lt_irrefl (0 : ℝ) hpositive

/-- An entire segment of roots at a different test offset. -/
theorem segment_isStandardLCPSolution (parameter : ℝ)
    (hparameter : parameter ∈ Set.Icc (0 : ℝ) 1) :
    IsStandardLCPSolution matrix ![0, 1, 1, 1] ![parameter, 0, 0, 0] := by
  refine ⟨?_, ?_, ?_⟩
  · intro who
    fin_cases who <;> norm_num
    exact hparameter.1
  · intro who
    fin_cases who <;> norm_num [lcpResidual, matrix, Fin.sum_univ_succ] <;>
      linarith [hparameter.1, hparameter.2]
  · intro who
    fin_cases who <;> norm_num [lcpResidual, matrix, Fin.sum_univ_succ]

/-- Even this R0 matrix has an infinite inhomogeneous solution set. -/
theorem infinite_standardLCPSolutions :
    {root | IsStandardLCPSolution matrix ![0, 1, 1, 1] root}.Infinite := by
  let segment : ℝ → Fin 4 → ℝ := fun parameter => ![parameter, 0, 0, 0]
  have hinjective : Function.Injective segment := by
    intro first second hequal
    exact congrFun hequal 0
  apply ((Set.Icc_infinite (show (0 : ℝ) < 1 by norm_num)).image hinjective.injOn).mono
  rintro root ⟨parameter, hparameter, rfl⟩
  exact segment_isStandardLCPSolution parameter hparameter

/-- Every recipient has a distinct quitter whose singleton gap is negative. -/
theorem negative_rows (row : Fin 4) :
    ∃ column : Fin 4, column ≠ row ∧ matrix row column < 0 := by
  fin_cases row
  · exact ⟨2, by decide, by norm_num [matrix]⟩
  · exact ⟨2, by decide, by norm_num [matrix]⟩
  · exact ⟨1, by decide, by norm_num [matrix]⟩
  · exact ⟨0, by decide, by norm_num [matrix]⟩

theorem row_one_negative_iff (column : Fin 4) : matrix 1 column < 0 ↔ column = 2 := by
  fin_cases column <;> norm_num [matrix]

theorem row_two_negative_iff (column : Fin 4) : matrix 2 column < 0 ↔ column = 1 := by
  fin_cases column <;> norm_num [matrix]

/-- The negative graph has no Hamiltonian cycle, under any ordering of the coordinates. -/
theorem not_negative_hamiltonianCycle (order : Equiv.Perm (Fin 4)) :
    ¬∀ coordinate, matrix (order coordinate) (order (coordinate + 1)) < 0 := by
  intro hcycle
  let coordinate := order.symm 1
  have hone : order coordinate = 1 := order.apply_symm_apply 1
  have hnext : order (coordinate + 1) = 2 := by
    apply (row_one_negative_iff _).mp
    simpa only [hone] using hcycle coordinate
  have hreturn : order ((coordinate + 1) + 1) = 1 := by
    apply (row_two_negative_iff _).mp
    simpa only [hnext] using hcycle (coordinate + 1)
  have hequal : (coordinate + 1) + 1 = coordinate :=
    order.injective (hreturn.trans hone.symm)
  exact (by decide : ∀ coordinate : Fin 4, (coordinate + 1) + 1 ≠ coordinate)
    coordinate hequal

/-- Positive row and column factors cannot create a negative Hamiltonian cycle. -/
theorem not_negative_hamiltonianCycle_of_positive_scaling
    (order : Equiv.Perm (Fin 4)) (left right : Fin 4 → ℝ)
    (hleft : ∀ who, 0 < left who) (hright : ∀ who, 0 < right who) :
    ¬∀ coordinate, left coordinate * matrix (order coordinate) (order (coordinate + 1)) *
      right (coordinate + 1) < 0 := by
  intro hcycle
  apply not_negative_hamiltonianCycle order
  intro coordinate
  by_contra hnonnegative
  have hproduct : 0 ≤ left coordinate *
      matrix (order coordinate) (order (coordinate + 1)) * right (coordinate + 1) :=
    mul_nonneg (mul_nonneg (hleft coordinate).le (le_of_not_gt hnonnegative))
      (hright (coordinate + 1)).le
  exact (hcycle coordinate).not_ge hproduct

end Math.LinearProgramming.NegativeDegreeFourMatrix

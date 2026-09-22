import MathUE.LinearProgramming.FiniteSolutions

/-!
# Exact support tests for standard linear complementarity

An exact solution of the active linear system, extended by zero off its
support, is the only possible LCP root on that support when the principal
matrix is nonsingular. Positivity and the inactive residual inequalities
then decide admissibility. These tests avoid computing a matrix inverse
when an exact candidate is already displayed.

Negative entries in every column and nonsingularity of all principal blocks
of size at least two imply R0. For a zero-diagonal matrix and a strictly
positive test anchor on a nonempty coordinate type, every LCP root at the
negative anchor has at least two positive coordinates. The candidate tests
and the R0 criterion also apply in dimension zero.
-/

noncomputable section

namespace Math.LinearProgramming

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- On an exact positive support, the active equations and inactive
inequalities are precisely the existing standard LCP predicate. -/
theorem isStandardLCPSolution_iff_support_conditions
    (matrix : Matrix ι ι ℝ) (offset root : ι → ℝ) (support : Finset ι)
    (hpositive : ∀ who ∈ support, 0 < root who)
    (hzero : ∀ who ∉ support, root who = 0) :
    IsStandardLCPSolution matrix offset root ↔
      (∀ who ∈ support, lcpResidual matrix offset root who = 0) ∧
        (∀ who ∉ support, 0 ≤ lcpResidual matrix offset root who) := by
  constructor
  · intro hroot
    exact ⟨fun who hwho =>
      (mul_eq_zero.mp (hroot.complementary who)).resolve_left (hpositive who hwho).ne',
      fun who _ => hroot.residual_nonneg who⟩
  · rintro ⟨hactive, hinactive⟩
    refine ⟨?_, ?_, ?_⟩
    · intro who
      by_cases hwho : who ∈ support
      · exact (hpositive who hwho).le
      · exact (hzero who hwho).ge
    · intro who
      by_cases hwho : who ∈ support
      · exact (hactive who hwho).ge
      · exact hinactive who hwho
    · intro who
      by_cases hwho : who ∈ support
      · rw [hactive who hwho, mul_zero]
      · rw [hzero who hwho, zero_mul]

/-- A displayed exact active-system candidate determines every LCP root
with that support, even when the candidate itself fails sign inequalities. -/
theorem IsStandardLCPSolution.eq_of_supported_linear_system
    {matrix : Matrix ι ι ℝ} {offset root : ι → ℝ}
    (hroot : IsStandardLCPSolution matrix offset root)
    (support : Finset ι) (hsupport : ∀ who, who ∈ support ↔ 0 < root who)
    (hnonsingular : (matrix.toSquareBlockProp (fun who => who ∈ support)).det ≠ 0)
    (candidate : ι → ℝ)
    (hzero : ∀ who ∉ support, candidate who = 0)
    (hactive : ∀ who ∈ support, lcpResidual matrix offset candidate who = 0) :
    root = candidate := by
  classical
  have hprincipal : (matrix.toSquareBlockProp (fun who => 0 < root who)).det ≠ 0 := by
    have hfinite : Finset.Subtype.fintype support =
        Subtype.fintype (fun who => who ∈ support) := Subsingleton.elim _ _
    rw [hfinite] at hnonsingular
    intro hzero
    exact hnonsingular ((Matrix.equiv_block_det matrix hsupport).symm.trans hzero)
  have hselected : (lcpSelectedMatrix matrix root).det ≠ 0 := by
    intro hdet
    exact hprincipal ((det_lcpSelectedMatrix matrix root).symm.trans hdet)
  have hinjective : Function.Injective (lcpSelectedMatrix matrix root).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hselected))
  apply hinjective
  rw [hroot.selectedMatrix_mulVec_eq]
  funext who
  rw [lcpSelectedMatrix_mulVec]
  by_cases hwho : 0 < root who
  · simp only [ite_eq_left hwho]
    have hresidual := hactive who ((hsupport who).mpr hwho)
    have hequal := congrFun (lcpResidual_eq_add_mulVec matrix offset candidate) who
    simp only [Pi.add_apply] at hequal
    linarith
  · simp only [ite_eq_right hwho]
    exact (hzero who (fun hmem => hwho ((hsupport who).mp hmem))).symm

omit [DecidableEq ι] in
private theorem lcpResidual_eq_of_unique_positive
    (matrix : Matrix ι ι ℝ) (offset root : ι → ℝ) (active : ι)
    (hnonneg : ∀ who, 0 ≤ root who)
    (hunique : ∀ who, 0 < root who → who = active) (who : ι) :
    lcpResidual matrix offset root who = offset who + root active * matrix who active := by
  classical
  change offset who + (∑ coordinate, root coordinate * matrix who coordinate) = _
  congr 1
  apply Finset.sum_eq_single active
  · intro other _hother hne
    have hzero : root other = 0 :=
      le_antisymm (le_of_not_gt (fun hpos => hne (hunique other hpos))) (hnonneg other)
    rw [hzero, zero_mul]
  · intro hnot
    exact (hnot (Finset.mem_univ active)).elim

/-- Negative entries in every column exclude singleton homogeneous supports;
nonsingular larger principals exclude every other nonzero homogeneous root. -/
theorem isR0Matrix_of_negative_columns_of_nonsingular_principals
    (matrix : Matrix ι ι ℝ)
    (hnegative : ∀ column, ∃ row, matrix row column < 0)
    (hprincipal : ∀ support : Finset ι, 2 ≤ support.card →
      (matrix.toSquareBlockProp (fun who => who ∈ support)).det ≠ 0) :
    IsR0Matrix matrix := by
  classical
  intro root hroot who
  let support := Finset.univ.filter (fun coordinate => 0 < root coordinate)
  have hsupport (coordinate : ι) : coordinate ∈ support ↔ 0 < root coordinate := by
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hlarge : 2 ≤ support.card
  · have hequal := hroot.eq_of_supported_linear_system support hsupport
      (hprincipal support hlarge) 0 (by simp) (by simp [lcpResidual])
    exact congrFun hequal who
  · by_contra hne
    have hpos : 0 < root who := lt_of_le_of_ne (hroot.weight_nonneg who) (Ne.symm hne)
    have hcard : support.card ≤ 1 := by omega
    have hunique : ∀ coordinate, 0 < root coordinate → coordinate = who := by
      intro coordinate hcoordinate
      exact Finset.card_le_one.mp hcard coordinate ((hsupport coordinate).mpr hcoordinate)
        who ((hsupport who).mpr hpos)
    obtain ⟨row, hrow⟩ := hnegative who
    have hresidual := hroot.residual_nonneg row
    rw [lcpResidual_eq_of_unique_positive matrix 0 root who
      hroot.weight_nonneg hunique row] at hresidual
    have hnegativeProduct := mul_neg_of_pos_of_neg hpos hrow
    apply hnegativeProduct.not_ge
    simpa only [Pi.zero_apply, zero_add] using hresidual

omit [DecidableEq ι] in
/-- On a nonempty coordinate type, a positive test anchor and zero diagonal
exclude both empty and singleton supports. -/
theorem IsStandardLCPSolution.two_le_card_positive_support_of_zero_diagonal
    [Nonempty ι]
    {matrix : Matrix ι ι ℝ} {anchor root : ι → ℝ}
    (hroot : IsStandardLCPSolution matrix (-anchor) root)
    (hdiagonal : ∀ who, matrix who who = 0)
    (hanchor : ∀ who, 0 < anchor who) :
    2 ≤ (Finset.univ.filter (fun who => 0 < root who)).card := by
  classical
  let support := Finset.univ.filter (fun who => 0 < root who)
  have hsupport (who : ι) : who ∈ support ↔ 0 < root who := by
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
  by_contra hlarge
  change ¬2 ≤ support.card at hlarge
  have hcard : support.card ≤ 1 := by omega
  obtain ⟨active⟩ := ‹Nonempty ι›
  by_cases hexists : ∃ who, 0 < root who
  · obtain ⟨who, hwho⟩ := hexists
    have hunique : ∀ coordinate, 0 < root coordinate → coordinate = who := by
      intro coordinate hcoordinate
      exact Finset.card_le_one.mp hcard coordinate ((hsupport coordinate).mpr hcoordinate)
        who ((hsupport who).mpr hwho)
    have hresidual := hroot.residual_nonneg who
    rw [lcpResidual_eq_of_unique_positive matrix (-anchor) root who
      hroot.weight_nonneg hunique who, hdiagonal who, mul_zero, add_zero] at hresidual
    exact (neg_neg_of_pos (hanchor who)).not_ge hresidual
  · have hzero : root = 0 := by
      funext who
      exact le_antisymm (le_of_not_gt (fun hpos => hexists ⟨who, hpos⟩))
        (hroot.weight_nonneg who)
    have hresidual := hroot.residual_nonneg active
    rw [hzero] at hresidual
    have : 0 ≤ -anchor active := by simpa [lcpResidual] using hresidual
    exact (neg_neg_of_pos (hanchor active)).not_ge this

end Math.LinearProgramming

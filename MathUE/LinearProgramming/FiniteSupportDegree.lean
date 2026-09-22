import MathUE.LinearProgramming.SupportTest
import MathUE.LinearProgramming.R0DegreeSum

/-!
# Finite support computation of linear-complementarity degree

An inverse-principal candidate is extended by zero outside its prescribed
support. Exact active-system certificates can be used in its place. For a
zero-diagonal matrix at a strictly negative test offset, the admissible
supports of size at least two enumerate all actual roots, provided those
principal matrices are nonsingular.

The positive-dimensional enumeration uses a nonempty coordinate type.
The canonical degree in dimension zero is handled by `r0Degree_fin_zero`.
-/

noncomputable section

namespace Math.LinearProgramming

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The inverse-principal solution at the negative anchor, extended by zero. -/
def principalInverseCandidate (matrix : Matrix ι ι ℝ) (anchor : ι → ℝ)
    (support : Finset ι) : ι → ℝ :=
  fun who => if hwho : who ∈ support then
    ((matrix.toSquareBlockProp (fun coordinate => coordinate ∈ support))⁻¹.mulVec
      (fun coordinate : support => anchor coordinate)) ⟨who, hwho⟩ else 0

omit [Fintype ι] in
theorem principalInverseCandidate_zero_off_support
    (matrix : Matrix ι ι ℝ) (anchor : ι → ℝ) (support : Finset ι)
    (who : ι) (hwho : who ∉ support) :
    principalInverseCandidate matrix anchor support who = 0 := by
  simp only [principalInverseCandidate, dite_eq_right hwho]

omit [DecidableEq ι] in
private theorem principal_mulVec_restrict_of_zero_off_support
    (matrix : Matrix ι ι ℝ) (support : Finset ι) (vector : ι → ℝ)
    (hzero : ∀ who ∉ support, vector who = 0) (who : support) :
    (matrix.toSquareBlockProp (fun coordinate => coordinate ∈ support)).mulVec
      (fun coordinate : support => vector coordinate) who = matrix.mulVec vector who := by
  change (∑ coordinate : support, matrix who coordinate * vector coordinate) =
    ∑ coordinate, matrix who coordinate * vector coordinate
  calc
    _ = ∑ coordinate ∈ support, matrix who coordinate * vector coordinate :=
      Finset.sum_coe_sort support (fun coordinate : ι => matrix who coordinate * vector coordinate)
    _ = _ := by
      apply Finset.sum_subset (Finset.subset_univ support)
      intro coordinate _hcoordinate hnot
      rw [hzero coordinate hnot, mul_zero]

/-- Nonsingularity gives the literal active residual equations. -/
theorem principalInverseCandidate_residual_eq_zero
    (matrix : Matrix ι ι ℝ) (anchor : ι → ℝ) (support : Finset ι)
    (hnonsingular : (matrix.toSquareBlockProp (fun who => who ∈ support)).det ≠ 0)
    (who : ι) (hwho : who ∈ support) :
    lcpResidual matrix (-anchor) (principalInverseCandidate matrix anchor support) who = 0 := by
  classical
  let principal := matrix.toSquareBlockProp (fun coordinate => coordinate ∈ support)
  let vector : support → ℝ := principal⁻¹.mulVec (fun coordinate => anchor coordinate)
  have hlinear : principal.mulVec vector = fun coordinate : support => anchor coordinate := by
    dsimp only [vector]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr hnonsingular), Matrix.one_mulVec]
  have hsum : matrix.mulVec (principalInverseCandidate matrix anchor support) who =
      principal.mulVec vector ⟨who, hwho⟩ := by
    have hrestriction : (fun coordinate : support =>
        principalInverseCandidate matrix anchor support coordinate) = vector := by
      funext coordinate
      simp only [principalInverseCandidate, dite_eq_left coordinate.property]
      rfl
    rw [← principal_mulVec_restrict_of_zero_off_support matrix support
      (principalInverseCandidate matrix anchor support)
      (principalInverseCandidate_zero_off_support matrix anchor support) ⟨who, hwho⟩,
      hrestriction]
  rw [lcpResidual_eq_add_mulVec]
  change -anchor who + matrix.mulVec (principalInverseCandidate matrix anchor support) who = 0
  rw [hsum, hlinear]
  exact neg_add_cancel _

/-- Exact active equations determine the inverse-principal candidate even
when its signs reject it as an LCP root. -/
theorem principalInverseCandidate_eq_of_supported_linear_system
    (matrix : Matrix ι ι ℝ) (anchor : ι → ℝ) (support : Finset ι)
    (hdet : (matrix.toSquareBlockProp (fun who => who ∈ support)).det ≠ 0)
    (candidate : ι → ℝ) (hzero : ∀ who ∉ support, candidate who = 0)
    (hactive : ∀ who ∈ support, lcpResidual matrix (-anchor) candidate who = 0) :
    principalInverseCandidate matrix anchor support = candidate := by
  let principal := matrix.toSquareBlockProp (fun who => who ∈ support)
  have hlinear : principal.mulVec (fun who : support => candidate who) =
      fun who : support => anchor who := by
    funext who
    rw [principal_mulVec_restrict_of_zero_off_support matrix support candidate hzero who]
    have hresidual := hactive who who.property
    have hequal := congrFun (lcpResidual_eq_add_mulVec matrix (-anchor) candidate) who
    simp only [Pi.add_apply, Pi.neg_apply] at hequal
    linarith
  have hrestricted := congrArg principal⁻¹.mulVec hlinear
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec] at hrestricted
  funext who
  by_cases hwho : who ∈ support
  · simp only [principalInverseCandidate, dite_eq_left hwho]
    exact (congrFun hrestricted ⟨who, hwho⟩).symm
  · rw [principalInverseCandidate_zero_off_support matrix anchor support who hwho,
      hzero who hwho]

/-- Literal positivity and inactive-slack tests on the large supports. -/
def admissibleLCPSupports (matrix : Matrix ι ι ℝ) (anchor : ι → ℝ)
    (candidate : Finset ι → ι → ℝ) : Finset (Finset ι) := by
  classical
  exact Finset.univ.filter (fun support => 2 ≤ support.card ∧
    (∀ who ∈ support, 0 < candidate support who) ∧
    ∀ who ∉ support, 0 ≤ lcpResidual matrix (-anchor) (candidate support) who)

theorem mem_admissibleLCPSupports_iff
    (matrix : Matrix ι ι ℝ) (anchor : ι → ℝ) (candidate : Finset ι → ι → ℝ)
    (support : Finset ι) :
    support ∈ admissibleLCPSupports matrix anchor candidate ↔
      2 ≤ support.card ∧ (∀ who ∈ support, 0 < candidate support who) ∧
        ∀ who ∉ support, 0 ≤ lcpResidual matrix (-anchor) (candidate support) who := by
  classical
  simp only [admissibleLCPSupports, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Exact active-system candidates enumerate the entire actual root set.
Neither strict inactive slacks nor a root-finiteness premise is needed. -/
theorem isStandardLCPSolution_iff_exists_admissible_support
    [Nonempty ι] (matrix : Matrix ι ι ℝ) (anchor : ι → ℝ)
    (hdiagonal : ∀ who, matrix who who = 0) (hanchor : ∀ who, 0 < anchor who)
    (hprincipal : ∀ support : Finset ι, 2 ≤ support.card →
      (matrix.toSquareBlockProp (fun who => who ∈ support)).det ≠ 0)
    (candidate : Finset ι → ι → ℝ)
    (hzero : ∀ support, 2 ≤ support.card → ∀ who ∉ support, candidate support who = 0)
    (hactive : ∀ support, 2 ≤ support.card → ∀ who ∈ support,
      lcpResidual matrix (-anchor) (candidate support) who = 0)
    (root : ι → ℝ) :
    IsStandardLCPSolution matrix (-anchor) root ↔
      ∃ support ∈ admissibleLCPSupports matrix anchor candidate, root = candidate support := by
  classical
  constructor
  · intro hroot
    let support := Finset.univ.filter (fun who => 0 < root who)
    have hsupport (who : ι) : who ∈ support ↔ 0 < root who := by
      simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
    have hlarge : 2 ≤ support.card :=
      hroot.two_le_card_positive_support_of_zero_diagonal hdiagonal hanchor
    have hequal := hroot.eq_of_supported_linear_system support hsupport
      (hprincipal support hlarge) (candidate support)
      (hzero support hlarge) (hactive support hlarge)
    refine ⟨support, (mem_admissibleLCPSupports_iff _ _ _ _).mpr ⟨hlarge, ?_, ?_⟩, hequal⟩
    · intro who hwho
      rw [← hequal]
      exact (hsupport who).mp hwho
    · intro who _hwho
      rw [← hequal]
      exact hroot.residual_nonneg who
  · rintro ⟨support, hsupport, rfl⟩
    obtain ⟨hlarge, hpositive, hinactive⟩ :=
      (mem_admissibleLCPSupports_iff _ _ _ _).mp hsupport
    exact (isStandardLCPSolution_iff_support_conditions matrix (-anchor)
      (candidate support) support hpositive (hzero support hlarge)).mpr
      ⟨hactive support hlarge, hinactive⟩

/-- The inverse-principal tests enumerate all actual roots without supplying
any candidate equations or root-set conclusions. -/
theorem isStandardLCPSolution_iff_exists_admissible_inverse_support
    [Nonempty ι] (matrix : Matrix ι ι ℝ) (anchor : ι → ℝ)
    (hdiagonal : ∀ who, matrix who who = 0) (hanchor : ∀ who, 0 < anchor who)
    (hprincipal : ∀ support : Finset ι, 2 ≤ support.card →
      (matrix.toSquareBlockProp (fun who => who ∈ support)).det ≠ 0)
    (root : ι → ℝ) :
    IsStandardLCPSolution matrix (-anchor) root ↔
      ∃ support ∈ admissibleLCPSupports matrix anchor (principalInverseCandidate matrix anchor),
        root = principalInverseCandidate matrix anchor support :=
  isStandardLCPSolution_iff_exists_admissible_support matrix anchor hdiagonal hanchor
    hprincipal (principalInverseCandidate matrix anchor)
    (fun support _ => principalInverseCandidate_zero_off_support matrix anchor support)
    (fun support hlarge => principalInverseCandidate_residual_eq_zero matrix anchor support
      (hprincipal support hlarge)) root

/-- The support sign sum computes the canonical degree. All roots and their
regularity are derived from the finite candidate tests. -/
theorem r0Degree_eq_sum_admissible_supports
    {n : ℕ} [Nonempty (Fin n)]
    (matrix : Matrix (Fin n) (Fin n) ℝ) (anchor : Fin n → ℝ)
    (hdiagonal : ∀ who, matrix who who = 0) (hanchor : ∀ who, 0 < anchor who)
    (hnegative : ∀ column, ∃ row, matrix row column < 0)
    (hprincipal : ∀ support : Finset (Fin n), 2 ≤ support.card →
      (matrix.toSquareBlockProp (fun who => who ∈ support)).det ≠ 0)
    (candidate : Finset (Fin n) → Fin n → ℝ)
    (hzero : ∀ support, 2 ≤ support.card → ∀ who ∉ support, candidate support who = 0)
    (hactive : ∀ support, 2 ≤ support.card → ∀ who ∈ support,
      lcpResidual matrix (-anchor) (candidate support) who = 0)
    (hstrict : ∀ support ∈ admissibleLCPSupports matrix anchor candidate,
      ∀ who ∉ support, 0 < lcpResidual matrix (-anchor) (candidate support) who) :
    r0Degree matrix (isR0Matrix_of_negative_columns_of_nonsingular_principals
      matrix hnegative hprincipal) =
      ∑ support ∈ admissibleLCPSupports matrix anchor candidate,
        (SignType.sign (matrix.toSquareBlockProp (fun who => who ∈ support)).det : ℤ) := by
  classical
  have hsupport (support : Finset (Fin n))
      (hsupport : support ∈ admissibleLCPSupports matrix anchor candidate) (who : Fin n) :
      who ∈ support ↔ 0 < candidate support who := by
    obtain ⟨hlarge, hpositive, _hinactive⟩ :=
      (mem_admissibleLCPSupports_iff _ _ _ _).mp hsupport
    constructor
    · exact hpositive who
    · intro hpos
      by_contra hnot
      rw [hzero support hlarge who hnot] at hpos
      exact lt_irrefl _ hpos
  have hdet (support : Finset (Fin n))
      (hmem : support ∈ admissibleLCPSupports matrix anchor candidate) :
      (matrix.toSquareBlockProp (fun who => 0 < candidate support who)).det =
        (matrix.toSquareBlockProp (fun who => who ∈ support)).det := by
    have hfinite : Finset.Subtype.fintype support =
        Subtype.fintype (fun who => who ∈ support) := Subsingleton.elim _ _
    rw [hfinite]
    exact Matrix.equiv_block_det matrix (hsupport support hmem)
  have hrootIff := isStandardLCPSolution_iff_exists_admissible_support
    matrix anchor hdiagonal hanchor hprincipal candidate hzero hactive
  have hrootStrict (root : Fin n → ℝ)
      (hroot : IsStandardLCPSolution matrix (-anchor) root)
      (who : Fin n) (hrootZero : root who = 0) :
      0 < lcpResidual matrix (-anchor) root who := by
    obtain ⟨support, hmem, rfl⟩ := (hrootIff root).mp hroot
    apply hstrict support hmem who
    intro hwho
    have hpos := (hsupport support hmem who).mp hwho
    rw [hrootZero] at hpos
    exact lt_irrefl _ hpos
  have hrootPrincipal (root : Fin n → ℝ)
      (hroot : IsStandardLCPSolution matrix (-anchor) root) :
      (matrix.toSquareBlockProp (fun who => 0 < root who)).det ≠ 0 := by
    obtain ⟨support, hmem, rfl⟩ := (hrootIff root).mp hroot
    rw [hdet support hmem]
    exact hprincipal support ((mem_admissibleLCPSupports_iff _ _ _ _).mp hmem).1
  obtain ⟨roots, hroots, hdegree⟩ := exists_finset_r0Degree_eq_sum_sign_det matrix
    (isR0Matrix_of_negative_columns_of_nonsingular_principals matrix hnegative hprincipal)
    (-anchor) hrootStrict hrootPrincipal
  have hrootSet : roots = (admissibleLCPSupports matrix anchor candidate).image candidate := by
    ext root
    rw [hroots, hrootIff]
    constructor
    · rintro ⟨support, hmem, hequal⟩
      exact Finset.mem_image.mpr ⟨support, hmem, hequal.symm⟩
    · intro hmem
      obtain ⟨support, hsupport, hequal⟩ := Finset.mem_image.mp hmem
      exact ⟨support, hsupport, hequal.symm⟩
  have hinjective : Set.InjOn candidate
      (admissibleLCPSupports matrix anchor candidate : Set (Finset (Fin n))) := by
    intro first hfirst second hsecond hequal
    ext who
    rw [hsupport first hfirst, hsupport second hsecond, hequal]
  rw [hrootSet, Finset.sum_image hinjective] at hdegree
  exact hdegree.trans (Finset.sum_congr rfl (fun support hmem =>
    congrArg (fun value : ℝ => (SignType.sign value : ℤ)) (hdet support hmem)))

/-- A canonical finite raw-matrix computation, using only inverse-principal
candidates and the strict inactive-slack test on admissible supports. -/
theorem r0Degree_eq_sum_admissible_inverse_supports
    {n : ℕ} [Nonempty (Fin n)]
    (matrix : Matrix (Fin n) (Fin n) ℝ) (anchor : Fin n → ℝ)
    (hdiagonal : ∀ who, matrix who who = 0) (hanchor : ∀ who, 0 < anchor who)
    (hnegative : ∀ column, ∃ row, matrix row column < 0)
    (hprincipal : ∀ support : Finset (Fin n), 2 ≤ support.card →
      (matrix.toSquareBlockProp (fun who => who ∈ support)).det ≠ 0)
    (hstrict : ∀ support ∈
      admissibleLCPSupports matrix anchor (principalInverseCandidate matrix anchor),
      ∀ who ∉ support,
        0 < lcpResidual matrix (-anchor) (principalInverseCandidate matrix anchor support) who) :
    r0Degree matrix (isR0Matrix_of_negative_columns_of_nonsingular_principals
      matrix hnegative hprincipal) =
      ∑ support ∈ admissibleLCPSupports matrix anchor (principalInverseCandidate matrix anchor),
        (SignType.sign (matrix.toSquareBlockProp (fun who => who ∈ support)).det : ℤ) :=
  r0Degree_eq_sum_admissible_supports matrix anchor hdiagonal hanchor hnegative hprincipal
    (principalInverseCandidate matrix anchor)
    (fun support _ => principalInverseCandidate_zero_off_support matrix anchor support)
    (fun support hlarge => principalInverseCandidate_residual_eq_zero matrix anchor support
      (hprincipal support hlarge)) hstrict

end Math.LinearProgramming

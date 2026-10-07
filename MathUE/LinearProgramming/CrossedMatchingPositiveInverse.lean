import MathUE.LinearProgramming.ZMatrixPositiveVector
import MathUE.LinearProgramming.CompactPositiveInverseBounds
import MathUE.LinearProgramming.CrossedMatchingMaps

/-! # Literal crossed matchings and the positive vector produced by Q

All matrices use receiver rows and singleton-owner columns. The positive
vector is produced from the standard LCP at offset minus one.
-/

noncomputable section

namespace Math.CrossedMatching

open LinearProgramming
open scoped Matrix

structure HasStrictMatchingSigns (matrix : Matrix (Fin 4) (Fin 4) ℝ) : Prop where
  diagonal : ∀ i, matrix i i = 0
  favorite_pos : ∀ i, 0 < matrix i (favorite i)
  scheduled_neg : ∀ i, matrix i (scheduled i) < 0
  other_neg : ∀ i, matrix i (other i) < 0

theorem HasStrictMatchingSigns.nonpositive_off_favorite
    {matrix : Matrix (Fin 4) (Fin 4) ℝ} (hsigns : HasStrictMatchingSigns matrix)
    (i j : Fin 4) (hne : j ≠ favorite i) : matrix i j ≤ 0 := by
  have hcases : j = i ∨ j = favorite i ∨ j = scheduled i ∨ j = other i := by
    fin_cases i <;> fin_cases j <;> simp [favorite, scheduled, other]
  rcases hcases with hdiagonal | hfavorite | hscheduled | hother
  · rw [hdiagonal]
    exact (hsigns.diagonal i).le
  · exact False.elim (hne hfavorite)
  · rw [hscheduled]
    exact (hsigns.scheduled_neg i).le
  · rw [hother]
    exact (hsigns.other_neg i).le

/-- Standard Q produces a strictly positive vector whose actual matrix
image is exactly one; no inverse or nonsingularity is an input. -/
theorem exists_positive_vector_mulVec_eq_one_of_standardQ
    (matrix : Matrix (Fin 4) (Fin 4) ℝ) (hsigns : HasStrictMatchingSigns matrix)
    (hQ : IsStandardQ matrix) :
    ∃ vector : Fin 4 → ℝ, (∀ i, 0 < vector i) ∧ matrix *ᵥ vector = fun _ => 1 := by
  obtain ⟨vector, hsolution⟩ := hQ (fun _ => -1)
  have himage : ∀ i, 1 ≤ (matrix *ᵥ vector) i := by
    intro i
    have hres := hsolution.residual_nonneg i
    simp only [lcpResidual] at hres
    have hsum : (matrix *ᵥ vector) i = ∑ j, vector j * matrix i j := by
      simp only [Matrix.mulVec, dotProduct, mul_comm]
    rw [hsum]
    linarith
  have hfavorite : ∀ i, 0 < vector (favorite i) := by
    intro i
    have hrest : ∑ j ∈ Finset.univ.erase (favorite i), matrix i j * vector j ≤ 0 := by
      apply Finset.sum_nonpos
      intro j hj
      exact mul_nonpos_of_nonpos_of_nonneg
        (hsigns.nonpositive_off_favorite i j (Finset.ne_of_mem_erase hj))
        (hsolution.weight_nonneg j)
    have hsplit : (matrix *ᵥ vector) i = matrix i (favorite i) * vector (favorite i) +
        ∑ j ∈ Finset.univ.erase (favorite i), matrix i j * vector j := by
      simp only [Matrix.mulVec, dotProduct]
      exact (Finset.add_sum_erase _ _ (Finset.mem_univ (favorite i))).symm
    have hproduct : 0 < matrix i (favorite i) * vector (favorite i) := by
      have := himage i
      rw [hsplit] at this
      linarith
    exact pos_of_mul_pos_right hproduct (hsigns.favorite_pos i).le
  have hpositive : ∀ i, 0 < vector i := by
    intro i
    simpa only [favorite_involutive i] using hfavorite (favorite i)
  refine ⟨vector, hpositive, ?_⟩
  funext i
  have hzero := (mul_eq_zero.mp (hsolution.complementary i)).resolve_left (hpositive i).ne'
  have hnormalized : -1 + (matrix *ᵥ vector) i = 0 := by
    simpa only [lcpResidual, Matrix.mulVec, dotProduct, mul_comm] using hzero
  linarith

def favoritePermuted (matrix : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => matrix i (favorite j)

theorem irreducible_of_matching_negative_graph
    (matrix : Matrix (Fin 4) (Fin 4) ℝ) (hnonnegative : ∀ i j, 0 ≤ matrix i j)
    (hscheduled : ∀ i, 0 < matrix i (scheduled i))
    (hother : ∀ i, 0 < matrix i (other i)) : matrix.IsIrreducible := by
  apply (Matrix.isIrreducible_iff_exists_pow_pos hnonnegative).mpr
  intro i j
  have htwo (k : Fin 4) (hik : 0 < matrix i k) (hkj : 0 < matrix k j) :
      0 < (matrix ^ 2) i j := by
    rw [pow_two, Matrix.mul_apply]
    exact Finset.sum_pos' (fun l _ => mul_nonneg (hnonnegative i l) (hnonnegative l j))
      ⟨k, Finset.mem_univ k, mul_pos hik hkj⟩
  have hcases : j = scheduled i ∨ j = other i ∨ j = i ∨ j = favorite i := by
    fin_cases i <;> fin_cases j <;> simp [favorite, scheduled, other]
  rcases hcases with hscheduledCase | hotherCase | hdiagonal | hfavorite
  · refine ⟨1, by norm_num, ?_⟩
    simpa only [pow_one, hscheduledCase] using hscheduled i
  · refine ⟨1, by norm_num, ?_⟩
    simpa only [pow_one, hotherCase] using hother i
  · refine ⟨2, by norm_num, htwo (scheduled i) (hscheduled i) ?_⟩
    rw [hdiagonal]
    simpa only [scheduled_involutive i] using hscheduled (scheduled i)
  · refine ⟨2, by norm_num, htwo (scheduled i) (hscheduled i) ?_⟩
    rw [hfavorite]
    simpa only [other_scheduled_eq_favorite i] using hother (scheduled i)

/-- The literal matching graph and an actual positive image suffice for
inverse positivity. The caller supplies neither a graph nor an inverse. -/
theorem hasStrictlyPositiveInverse_of_matching_positive_vector
    (matrix : Matrix (Fin 4) (Fin 4) ℝ) (hsigns : HasStrictMatchingSigns matrix)
    (vector : Fin 4 → ℝ) (hvector : ∀ i, 0 < vector i)
    (himage : ∀ i, 0 < (matrix *ᵥ vector) i) : HasStrictlyPositiveInverse matrix := by
  let M := favoritePermuted matrix
  let u : Fin 4 → ℝ := fun i => vector (favorite i)
  have hu : ∀ i, 0 < u i := fun i => hvector (favorite i)
  have hoff : ∀ i j, i ≠ j → M i j ≤ 0 := by
    intro i j hij
    exact hsigns.nonpositive_off_favorite i (favorite j)
      (fun heq => hij (favorite_involutive.injective heq).symm)
  have hMu : ∀ i, (M *ᵥ u) i = (matrix *ᵥ vector) i := by
    intro i
    exact Equiv.sum_comp favoriteEquiv (fun j => matrix i j * vector j)
  have himageM : ∀ i, 0 < (M *ᵥ u) i := by
    intro i
    rw [hMu]
    exact himage i
  let C := zMatrixPositiveVectorContraction M u
  have hCnonnegative := zMatrixPositiveVectorContraction_nonnegative M u hoff hu himageM
  have hentry (i j : Fin 4) (hne : i ≠ j) (hnegative : M i j < 0) : 0 < C i j := by
    have hdiag := diagonal_pos_of_zMatrix_positive_vector M u hoff hu himageM i
    simp only [C, zMatrixPositiveVectorContraction, Matrix.sub_apply, Matrix.one_apply,
      Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [hne, ite_false, zero_sub]
    exact neg_pos.mpr (mul_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg (inv_pos.mpr (mul_pos hdiag (hu i))) hnegative) (hu j))
  have hCs : ∀ i, 0 < C i (scheduled i) := by
    intro i
    apply hentry i (scheduled i)
    · fin_cases i <;> simp [scheduled]
    · change matrix i (favorite (scheduled i)) < 0
      rw [← other_eq_favorite_scheduled]
      exact hsigns.other_neg i
  have hCo : ∀ i, 0 < C i (other i) := by
    intro i
    apply hentry i (other i)
    · fin_cases i <;> simp [other]
    · change matrix i (favorite (other i)) < 0
      have heq : favorite (other i) = scheduled i := by fin_cases i <;> rfl
      rw [heq]
      exact hsigns.scheduled_neg i
  have hM := hasStrictlyPositiveInverse_of_zMatrix_positive_vector M u hoff hu himageM
    (irreducible_of_matching_negative_graph C hCnonnegative hCs hCo)
  let inverse : Matrix (Fin 4) (Fin 4) ℝ := fun i j => M⁻¹ (favorite i) j
  have hright : matrix * inverse = 1 := by
    have hMright := Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM.1)
    ext i j
    have hsum := Equiv.sum_comp favoriteEquiv
      (fun k => matrix i k * M⁻¹ (favorite k) j)
    change (∑ k, matrix i (favorite k) * M⁻¹ (favorite (favorite k)) j) =
      ∑ k, matrix i k * M⁻¹ (favorite k) j at hsum
    have hentryEq : (matrix * inverse) i j = (M * M⁻¹) i j := by
      change (∑ k, matrix i k * M⁻¹ (favorite k) j) =
        ∑ k, matrix i (favorite k) * M⁻¹ k j
      exact hsum.symm
    rw [hentryEq, hMright]
  exact hasStrictlyPositiveInverse_of_rightInverse matrix inverse hright
    (fun i j => hM.2 (favorite i) j)

theorem hasStrictlyPositiveInverse_of_matching_standardQ
    (matrix : Matrix (Fin 4) (Fin 4) ℝ) (hsigns : HasStrictMatchingSigns matrix)
    (hQ : IsStandardQ matrix) : HasStrictlyPositiveInverse matrix := by
  obtain ⟨vector, hvector, himage⟩ :=
    exists_positive_vector_mulVec_eq_one_of_standardQ matrix hsigns hQ
  apply hasStrictlyPositiveInverse_of_matching_positive_vector matrix hsigns vector hvector
  intro i
  rw [himage]
  norm_num

def variableMatrix (matrix : Matrix (Fin 4) (Fin 4) ℝ)
    (premium passive point : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => matrix i j +
    (if j = scheduled i then max (-premium i) 0 *
      (point (scheduled i) / (1 + point (scheduled i))) else 0) +
    (if j = favorite i then max (passive i) 0 * point (other i) else 0)

theorem variableMatrix_ge
    (matrix : Matrix (Fin 4) (Fin 4) ℝ) (premium passive point : Fin 4 → ℝ)
    (hpoint : ∀ i, 0 ≤ point i) :
    ∀ i j, matrix i j ≤ variableMatrix matrix premium passive point i j := by
  intro i j
  have htheta : 0 ≤ point (scheduled i) / (1 + point (scheduled i)) :=
    div_nonneg (hpoint _) (by linarith [hpoint (scheduled i)])
  have hpremium : 0 ≤ max (-premium i) 0 := le_max_right _ _
  have hpassive : 0 ≤ max (passive i) 0 := le_max_right _ _
  unfold variableMatrix
  split_ifs <;>
    nlinarith [mul_nonneg hpremium htheta, mul_nonneg hpassive (hpoint (other i))]

theorem variableMatrix_hasStrictMatchingSigns
    (matrix : Matrix (Fin 4) (Fin 4) ℝ) (hsigns : HasStrictMatchingSigns matrix)
    (premium passive point : Fin 4 → ℝ)
    (hpremium : ∀ i, matrix i (scheduled i) < premium i)
    (hpoint : ∀ i, 0 ≤ point i) :
    HasStrictMatchingSigns (variableMatrix matrix premium passive point) := by
  have hfavoriteNe : ∀ i, favorite i ≠ i := by intro i; fin_cases i <;> decide
  have hscheduledNe : ∀ i, scheduled i ≠ i := by intro i; fin_cases i <;> decide
  have hmatchNe : ∀ i, favorite i ≠ scheduled i := by intro i; fin_cases i <;> decide
  have hotherFavorite : ∀ i, other i ≠ favorite i := by intro i; fin_cases i <;> decide
  have hotherScheduled : ∀ i, other i ≠ scheduled i := by intro i; fin_cases i <;> decide
  constructor
  · intro i
    simpa only [variableMatrix, Ne.symm (hscheduledNe i), Ne.symm (hfavoriteNe i),
      ite_false, add_zero] using hsigns.diagonal i
  · intro i
    exact lt_of_lt_of_le (hsigns.favorite_pos i)
      (variableMatrix_ge matrix premium passive point hpoint i (favorite i))
  · intro i
    have hdenom : 0 < 1 + point (scheduled i) := by linarith [hpoint (scheduled i)]
    have htheta : point (scheduled i) / (1 + point (scheduled i)) < 1 :=
      (div_lt_one hdenom).mpr (by linarith)
    have halpha : max (-premium i) 0 < -matrix i (scheduled i) :=
      max_lt (neg_lt_neg (hpremium i)) (neg_pos.mpr (hsigns.scheduled_neg i))
    have hprod : max (-premium i) 0 *
        (point (scheduled i) / (1 + point (scheduled i))) ≤ max (-premium i) 0 := by
      have := mul_le_mul_of_nonneg_left htheta.le (le_max_right (-premium i) 0)
      simpa only [mul_one] using this
    simp only [variableMatrix, eq_self, ite_true, Ne.symm (hmatchNe i), ite_false, add_zero]
    linarith
  · intro i
    simpa only [variableMatrix, hotherScheduled i, hotherFavorite i, ite_false, add_zero]
      using hsigns.other_neg i

/-- Arbitrary passive increments and signed participant increments are
allowed. The printed strict participant comparison is the only extra sign test. -/
theorem hasStrictlyPositiveInverse_variableMatrix_of_standardQ
    (matrix : Matrix (Fin 4) (Fin 4) ℝ) (hsigns : HasStrictMatchingSigns matrix)
    (hQ : IsStandardQ matrix) (premium passive point : Fin 4 → ℝ)
    (hpremium : ∀ i, matrix i (scheduled i) < premium i)
    (hpoint : ∀ i, 0 ≤ point i) :
    HasStrictlyPositiveInverse (variableMatrix matrix premium passive point) := by
  obtain ⟨vector, hvector, himage⟩ :=
    exists_positive_vector_mulVec_eq_one_of_standardQ matrix hsigns hQ
  apply hasStrictlyPositiveInverse_of_matching_positive_vector
    (variableMatrix matrix premium passive point)
    (variableMatrix_hasStrictMatchingSigns matrix hsigns premium passive point hpremium hpoint)
    vector hvector
  intro i
  have hle : (matrix *ᵥ vector) i ≤
      (variableMatrix matrix premium passive point *ᵥ vector) i := by
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_right
      (variableMatrix_ge matrix premium passive point hpoint i j)
      (hvector j).le
  rw [himage] at hle
  linarith

theorem continuousOn_variableMatrix_nonnegative
    (matrix : Matrix (Fin 4) (Fin 4) ℝ) (premium passive : Fin 4 → ℝ) :
    ContinuousOn (variableMatrix matrix premium passive) (Set.Ici (0 : Fin 4 → ℝ)) := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  have hratio : ContinuousOn (fun point : Fin 4 → ℝ =>
      point (scheduled i) / (1 + point (scheduled i))) (Set.Ici (0 : Fin 4 → ℝ)) := by
    apply (continuous_apply (scheduled i)).continuousOn.div
      (continuous_const.add (continuous_apply (scheduled i))).continuousOn
    intro point hpoint hzero
    have hnonnegative : 0 ≤ point (scheduled i) := hpoint (scheduled i)
    change 1 + point (scheduled i) = 0 at hzero
    linarith
  have hfirst : ContinuousOn (fun point : Fin 4 → ℝ => max (-premium i) 0 *
      (point (scheduled i) / (1 + point (scheduled i)))) (Set.Ici (0 : Fin 4 → ℝ)) :=
    continuous_const.continuousOn.mul hratio
  have hsecond : ContinuousOn (fun point : Fin 4 → ℝ =>
      max (passive i) 0 * point (other i)) (Set.Ici (0 : Fin 4 → ℝ)) :=
    (continuous_const.mul (continuous_apply (other i))).continuousOn
  change ContinuousOn
    (fun point : Fin 4 → ℝ => variableMatrix matrix premium passive point i j) _
  unfold variableMatrix
  split_ifs <;> first
    | exact (continuous_const.continuousOn.add hfirst).add hsecond
    | exact (continuous_const.continuousOn.add hfirst).add continuous_const.continuousOn
    | exact (continuous_const.continuousOn.add continuous_const.continuousOn).add hsecond
    | exact continuous_const.continuousOn

/-- The radius is fixed before the inverse bounds; no unbounded-domain
uniform inverse estimate is asserted. Empty negative-radius cubes are allowed. -/
theorem exists_variableMatrix_inverse_bounds_on_cube
    (matrix : Matrix (Fin 4) (Fin 4) ℝ) (hsigns : HasStrictMatchingSigns matrix)
    (hQ : IsStandardQ matrix) (premium passive : Fin 4 → ℝ)
    (hpremium : ∀ i, matrix i (scheduled i) < premium i) (radius : ℝ) :
    ∃ lower upper : ℝ, 0 < lower ∧ ∀ point : Fin 4 → ℝ,
      (∀ i, 0 ≤ point i ∧ point i ≤ radius) → ∀ i j,
        lower ≤ (variableMatrix matrix premium passive point)⁻¹ i j ∧
          (variableMatrix matrix premium passive point)⁻¹ i j ≤ upper := by
  let cube : Set (Fin 4 → ℝ) := Set.Icc 0 (fun _ => radius)
  have hcontinuous : ContinuousOn (variableMatrix matrix premium passive) cube :=
    (continuousOn_variableMatrix_nonnegative matrix premium passive).mono
      (fun _ hpoint => hpoint.1)
  obtain ⟨lower, upper, hlower, hbounds⟩ :=
    exists_uniform_positive_inverse_entry_bounds_on_compact
      (variableMatrix matrix premium passive) cube isCompact_Icc hcontinuous
      (fun point hpoint => hasStrictlyPositiveInverse_variableMatrix_of_standardQ
        matrix hsigns hQ premium passive point hpremium hpoint.1)
  refine ⟨lower, upper, hlower, ?_⟩
  intro point hpoint
  exact hbounds point ⟨fun i => (hpoint i).1, fun i => (hpoint i).2⟩

end Math.CrossedMatching

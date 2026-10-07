import MathUE.LinearProgramming.CrossedMatchingPositiveInverse

/-! # The actual crossed-matching odds map and its scaled-eigenpoint bound

The passive vector is unrestricted. Negative participant increments are moved
into the matrix, not discarded from the original indifference equations.
-/

noncomputable section

namespace Math.CrossedMatching

open LinearProgramming
open scoped Matrix

def positiveNumerator (matrix : Matrix (Fin 4) (Fin 4) ℝ)
    (premium passive point : Fin 4 → ℝ) : Fin 4 → ℝ := fun i =>
  (premium i - matrix i (scheduled i)) * point (scheduled i) *
      (point (favorite i) + point (other i) + point (favorite i) * point (other i)) +
    max (premium i) 0 * point (scheduled i) ^ 2 / (1 + point (scheduled i)) +
    max (-passive i) 0 * point (favorite i) * point (other i)

def oddsMap (matrix : Matrix (Fin 4) (Fin 4) ℝ)
    (premium passive point : Fin 4 → ℝ) : Fin 4 → ℝ :=
  (variableMatrix matrix premium passive point)⁻¹ *ᵥ
    positiveNumerator matrix premium passive point

def scaledEigenpointBound (matrix : Matrix (Fin 4) (Fin 4) ℝ)
    (premium passive : Fin 4 → ℝ) : ℝ :=
  ∑ i, max (matrix i (favorite i)) (max (passive i) 0) /
    (premium i - matrix i (scheduled i))

theorem matching_mulVec_lt_favorite
    (matrix : Matrix (Fin 4) (Fin 4) ℝ) (hsigns : HasStrictMatchingSigns matrix)
    (point : Fin 4 → ℝ) (hpoint : ∀ i, 0 < point i) (i : Fin 4) :
    (matrix *ᵥ point) i < matrix i (favorite i) * point (favorite i) := by
  have hscheduledNe : scheduled i ≠ favorite i := by
    fin_cases i <;> decide
  have hrest : ∑ j ∈ Finset.univ.erase (favorite i), matrix i j * point j < 0 := by
    have hsum : (∑ j ∈ Finset.univ.erase (favorite i), matrix i j * point j) <
        ∑ j ∈ Finset.univ.erase (favorite i), (0 : ℝ) := by
      apply Finset.sum_lt_sum
      · intro j hj
        exact mul_nonpos_of_nonpos_of_nonneg
          (hsigns.nonpositive_off_favorite i j (Finset.ne_of_mem_erase hj)) (hpoint j).le
      · exact ⟨scheduled i, Finset.mem_erase.mpr ⟨hscheduledNe, Finset.mem_univ _⟩,
          mul_neg_of_neg_of_pos (hsigns.scheduled_neg i) (hpoint _)⟩
    simpa only [Finset.sum_const_zero] using hsum
  have hsplit : (matrix *ᵥ point) i = matrix i (favorite i) * point (favorite i) +
      ∑ j ∈ Finset.univ.erase (favorite i), matrix i j * point j := by
    simp only [Matrix.mulVec, dotProduct]
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ (favorite i))).symm
  rw [hsplit]
  linarith

theorem positiveNumerator_lower
    (matrix : Matrix (Fin 4) (Fin 4) ℝ) (premium passive point : Fin 4 → ℝ)
    (hpremium : ∀ i, matrix i (scheduled i) < premium i)
    (hpoint : ∀ i, 0 ≤ point i) (i : Fin 4) :
    (premium i - matrix i (scheduled i)) * point (scheduled i) *
      point (favorite i) * (1 + point (other i)) ≤
        positiveNumerator matrix premium passive point i := by
  have hc : 0 ≤ premium i - matrix i (scheduled i) := (sub_pos.mpr (hpremium i)).le
  have hsecond : 0 ≤ max (premium i) 0 * point (scheduled i) ^ 2 /
      (1 + point (scheduled i)) := div_nonneg
    (mul_nonneg (le_max_right _ _) (sq_nonneg _)) (by linarith [hpoint (scheduled i)])
  have hthird : 0 ≤ max (-passive i) 0 * point (favorite i) * point (other i) :=
    mul_nonneg (mul_nonneg (le_max_right _ _) (hpoint _)) (hpoint _)
  have hextra : 0 ≤ (premium i - matrix i (scheduled i)) *
      point (scheduled i) * point (other i) :=
    mul_nonneg (mul_nonneg hc (hpoint _)) (hpoint _)
  unfold positiveNumerator
  nlinarith

theorem scaled_eigenpoint_coordinate_bound
    (matrix : Matrix (Fin 4) (Fin 4) ℝ) (hsigns : HasStrictMatchingSigns matrix)
    (hQ : IsStandardQ matrix) (premium passive point : Fin 4 → ℝ)
    (hpremium : ∀ i, matrix i (scheduled i) < premium i)
    (hpoint : ∀ i, 0 < point i) {scale : ℝ} (hscale : 0 < scale)
    (hscaleLe : scale ≤ 1) (heigen : oddsMap matrix premium passive point = scale • point)
    (i : Fin 4) : point (scheduled i) <
      max (matrix i (favorite i)) (max (passive i) 0) /
        (premium i - matrix i (scheduled i)) := by
  let B := variableMatrix matrix premium passive point
  have hpointLe : ∀ i, 0 ≤ point i := fun i => (hpoint i).le
  have hB := hasStrictlyPositiveInverse_variableMatrix_of_standardQ
    matrix hsigns hQ premium passive point hpremium hpointLe
  have hback : B *ᵥ oddsMap matrix premium passive point =
      positiveNumerator matrix premium passive point := by
    rw [oddsMap, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B
      (isUnit_iff_ne_zero.mpr hB.1), Matrix.one_mulVec]
  rw [heigen, Matrix.mulVec_smul] at hback
  have hcomponent : scale * (B *ᵥ point) i =
      positiveNumerator matrix premium passive point i := congrFun hback i
  have hrow := matching_mulVec_lt_favorite B
    (variableMatrix_hasStrictMatchingSigns matrix hsigns premium passive point
      hpremium hpointLe) point hpoint i
  have hmatchNe : favorite i ≠ scheduled i := by fin_cases i <;> decide
  have hBfavorite : B i (favorite i) =
      matrix i (favorite i) + max (passive i) 0 * point (other i) := by
    simp only [B, variableMatrix, hmatchNe, ite_false, eq_self, ite_true, add_zero]
  rw [hBfavorite] at hrow
  have hstrict := mul_lt_mul_of_pos_left hrow hscale
  rw [hcomponent] at hstrict
  have hfavoritePositive : 0 <
      (matrix i (favorite i) + max (passive i) 0 * point (other i)) *
        point (favorite i) := mul_pos
    (add_pos_of_pos_of_nonneg (hsigns.favorite_pos i)
      (mul_nonneg (le_max_right _ _) (hpointLe _))) (hpoint _)
  have hscaleBound := mul_le_mul_of_nonneg_right hscaleLe hfavoritePositive.le
  rw [one_mul] at hscaleBound
  have hmaxFavorite := le_max_left (matrix i (favorite i)) (max (passive i) 0)
  have hmaxPassive := le_max_right (matrix i (favorite i)) (max (passive i) 0)
  have hmax : matrix i (favorite i) + max (passive i) 0 * point (other i) ≤
      max (matrix i (favorite i)) (max (passive i) 0) * (1 + point (other i)) := by
    nlinarith [mul_le_mul_of_nonneg_right hmaxPassive (hpointLe (other i))]
  have hmaxBound := mul_le_mul_of_nonneg_right hmax (hpointLe (favorite i))
  have hlower := positiveNumerator_lower matrix premium passive point hpremium hpointLe i
  have hproduct : 0 < point (favorite i) * (1 + point (other i)) :=
    mul_pos (hpoint _) (by linarith [hpoint (other i)])
  have hcoreBound := hlower.trans_lt (hstrict.trans_le (hscaleBound.trans hmaxBound))
  have hcap : (premium i - matrix i (scheduled i)) * point (scheduled i) <
      max (matrix i (favorite i)) (max (passive i) 0) := by
    by_contra hnot
    have hreverse := mul_le_mul_of_nonneg_right (le_of_not_gt hnot) hproduct.le
    have hstrictProduct : ((premium i - matrix i (scheduled i)) * point (scheduled i)) *
        (point (favorite i) * (1 + point (other i))) <
      max (matrix i (favorite i)) (max (passive i) 0) *
        (point (favorite i) * (1 + point (other i))) := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hcoreBound
    exact (not_lt_of_ge hreverse) hstrictProduct
  apply (lt_div_iff₀ (sub_pos.mpr (hpremium i))).mpr
  simpa only [mul_comm] using hcap

theorem scaled_eigenpoint_sum_lt_bound
    (matrix : Matrix (Fin 4) (Fin 4) ℝ) (hsigns : HasStrictMatchingSigns matrix)
    (hQ : IsStandardQ matrix) (premium passive point : Fin 4 → ℝ)
    (hpremium : ∀ i, matrix i (scheduled i) < premium i)
    (hpoint : ∀ i, 0 < point i) {scale : ℝ} (hscale : 0 < scale)
    (hscaleLe : scale ≤ 1) (heigen : oddsMap matrix premium passive point = scale • point) :
    ∑ i, point i < scaledEigenpointBound matrix premium passive := by
  let scheduledEquiv : Fin 4 ≃ Fin 4 :=
    ⟨scheduled, scheduled, scheduled_involutive, scheduled_involutive⟩
  have hsum : (∑ i, point (scheduled i)) = ∑ i, point i :=
    Equiv.sum_comp scheduledEquiv point
  rw [← hsum]
  apply Finset.sum_lt_sum
  · intro i _
    exact (scaled_eigenpoint_coordinate_bound matrix hsigns hQ premium passive point
      hpremium hpoint hscale hscaleLe heigen i).le
  · exact ⟨0, Finset.mem_univ _, scaled_eigenpoint_coordinate_bound
      matrix hsigns hQ premium passive point hpremium hpoint hscale hscaleLe heigen 0⟩

end Math.CrossedMatching

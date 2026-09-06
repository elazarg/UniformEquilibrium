import MathUE.LinearProgramming.PositiveInverseOpenness
import UniformEquilibrium.Diagnostics.Quitting.SignedFourCycleMatrixFixtures

noncomputable section

namespace GameTheory.QuittingLCPClassification.SignedFourCycleMatrixRegimeOpenness

open Math.LinearProgramming SignedFourCycleMatrixFixtures

def openRegime : Set (Matrix (Fin 4) (Fin 4) ℝ) :=
  {M | HasStrictlyPositiveInverse M ∧
    M 0 1 < 0 ∧ M 1 2 < 0 ∧ M 2 3 < 0 ∧ M 3 0 < 0 ∧
    M 0 2 < 0 ∧ M 2 0 < 0}

theorem isOpen_openRegime : IsOpen openRegime := by
  unfold openRegime
  exact isOpen_hasStrictlyPositiveInverse.inter
    ((isOpen_lt (continuous_apply_apply 0 1) continuous_const).inter
      ((isOpen_lt (continuous_apply_apply 1 2) continuous_const).inter
        ((isOpen_lt (continuous_apply_apply 2 3) continuous_const).inter
          ((isOpen_lt (continuous_apply_apply 3 0) continuous_const).inter
            ((isOpen_lt (continuous_apply_apply 0 2) continuous_const).inter
              (isOpen_lt (continuous_apply_apply 2 0) continuous_const))))))

theorem gammaDagger_mem_openRegime : gammaDagger ∈ openRegime := by
  refine ⟨hasStrictlyPositiveInverse_of_rightInverse gammaDagger gammaDaggerInverse
    gammaDagger_twoSidedInverse.1 gammaDaggerInverse_positive, ?_⟩
  norm_num [gammaDagger, Matrix.cons_val_two, Matrix.cons_val_three]

theorem gammaDoubleDagger_mem_openRegime : gammaDoubleDagger ∈ openRegime := by
  refine ⟨hasStrictlyPositiveInverse_of_rightInverse gammaDoubleDagger
    gammaDoubleDaggerInverse gammaDoubleDagger_twoSidedInverse.1
    gammaDoubleDaggerInverse_positive, ?_⟩
  norm_num [gammaDoubleDagger, Matrix.cons_val_two, Matrix.cons_val_three]

theorem openRegime_classification (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hM : M ∈ openRegime) (hdiag : ∀ i, M i i = 0) :
    normalCore M = Finset.univ ∧ IsStandardQMatrix M ∧
      ¬HasHomogeneousSimplexSolution M ∧ ¬IsProjectiveQBarMatrix M := by
  rcases hM with ⟨hinverse, h01, h12, h23, h30, h02, h20⟩
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hinverse.1
  have hright : M * M⁻¹ = 1 := M.mul_nonsing_inv hunit
  have hleft : M⁻¹ * M = 1 := M.nonsing_inv_mul hunit
  have hcore : normalCore M = Finset.univ := by
    apply normalCore_eq_univ_of_fixed_blocker M cycleSuccessor cycleSuccessor_ne
    intro i
    fin_cases i
    · simpa [cycleSuccessor] using h01.le
    · simpa [cycleSuccessor] using h12.le
    · simpa [cycleSuccessor] using h23.le
    · simpa [cycleSuccessor] using h30.le
  have hstandard : IsStandardQMatrix M :=
    isStandardQMatrix_of_positive_rightInverse M M⁻¹ hright hinverse.2
  have hhomogeneous : ¬HasHomogeneousSimplexSolution M :=
    noHomogeneousSimplexSolution_of_positive_leftInverse M M⁻¹ hleft hinverse.2
  have hopposite : reindexMatrix oppositePairEquiv.symm
      (principalMatrix M oppositePair) = negativePairMatrix (-M 0 2) (-M 2 0) := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [reindexMatrix, principalMatrix, oppositePairEquiv,
      negativePairMatrix, hdiag]
  have hqbar : ¬IsProjectiveQBarMatrix M :=
    not_projectiveQBar_of_oppositePair M (-M 0 2) (-M 2 0)
      (neg_pos.mpr h02) (neg_pos.mpr h20) hopposite
  exact ⟨hcore, hstandard, hhomogeneous, hqbar⟩

/-- Both heterogeneous fixtures lie in one explicit ambient open set whose
zero-diagonal matrices retain the full matrix-classification regime. -/
theorem exists_common_open_matrix_regime_neighborhood :
    ∃ U : Set (Matrix (Fin 4) (Fin 4) ℝ), IsOpen U ∧
      gammaDagger ∈ U ∧ gammaDoubleDagger ∈ U ∧
      ∀ M ∈ U, (∀ i, M i i = 0) →
        normalCore M = Finset.univ ∧ IsStandardQMatrix M ∧
          ¬HasHomogeneousSimplexSolution M ∧ ¬IsProjectiveQBarMatrix M := by
  exact ⟨openRegime, isOpen_openRegime, gammaDagger_mem_openRegime,
    gammaDoubleDagger_mem_openRegime, openRegime_classification⟩

end GameTheory.QuittingLCPClassification.SignedFourCycleMatrixRegimeOpenness

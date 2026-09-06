import UniformEquilibrium.Quitting.Classification.LCP.PositiveInverse
import UniformEquilibrium.Quitting.Classification.LCP.ElementaryMatrixObstructions
import MathUE.LinearProgramming.RowNegativeShape

noncomputable section

namespace GameTheory.QuittingLCPClassification.SignedFourCycleMatrixFixtures

open Math.LinearProgramming

def gammaStar : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, -1, -1, 6;
     6, 0, -1, -1;
     -1, 6, 0, -1;
     -1, -1, 6, 0]

def gammaStarInverse : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / 1200 : ℝ) •
    !![37, 209, 13, 41;
       41, 37, 209, 13;
       13, 41, 37, 209;
       209, 13, 41, 37]

theorem gammaStar_twoSidedInverse :
    gammaStar * gammaStarInverse = 1 ∧ gammaStarInverse * gammaStar = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [gammaStar, gammaStarInverse, Matrix.mul_apply, Fin.sum_univ_succ]

theorem gammaStarInverse_positive : HasStrictlyPositiveEntries gammaStarInverse := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [gammaStarInverse]

def gammaDagger : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, -1, -9 / 10, 29 / 5;
     6, 0, -1, -1;
     -1, 6, 0, -1;
     -1, -1, 6, 0]

def gammaDaggerInverse : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / 11595 : ℝ) •
    !![370, 2019, 127, 392;
       410, 357, 2021, 121;
       130, 396, 358, 2018;
       2090, 123, 404, 334]

theorem gammaDagger_twoSidedInverse :
    gammaDagger * gammaDaggerInverse = 1 ∧ gammaDaggerInverse * gammaDagger = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [gammaDagger, gammaDaggerInverse, Matrix.mul_apply, Fin.sum_univ_succ]

theorem gammaDaggerInverse_positive : HasStrictlyPositiveEntries gammaDaggerInverse := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [gammaDaggerInverse]

def gammaDoubleDagger : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, -1, -1, 6;
     9, 0, -1, -1;
     -1, 4, 0, -1;
     -1, -1, 4, 0]

def gammaDoubleDaggerInverse : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / 781 : ℝ) •
    !![17, 91, 11, 27;
       39, 25, 209, 16;
       14, 29, 55, 206;
       139, 9, 44, 37]

theorem gammaDoubleDagger_twoSidedInverse :
    gammaDoubleDagger * gammaDoubleDaggerInverse = 1 ∧
      gammaDoubleDaggerInverse * gammaDoubleDagger = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [gammaDoubleDagger, gammaDoubleDaggerInverse,
      Matrix.mul_apply, Fin.sum_univ_succ]

theorem gammaDoubleDaggerInverse_positive :
    HasStrictlyPositiveEntries gammaDoubleDaggerInverse := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [gammaDoubleDaggerInverse]

theorem gammaStar_standardQ_and_noHomogeneous :
    IsStandardQMatrix gammaStar ∧ ¬HasHomogeneousSimplexSolution gammaStar := by
  obtain ⟨hleft, hright⟩ := gammaStar_twoSidedInverse
  exact ⟨isStandardQMatrix_of_positive_rightInverse
      gammaStar gammaStarInverse hleft gammaStarInverse_positive,
    noHomogeneousSimplexSolution_of_positive_leftInverse
      gammaStar gammaStarInverse hright gammaStarInverse_positive⟩

theorem gammaDagger_standardQ_and_noHomogeneous :
    IsStandardQMatrix gammaDagger ∧ ¬HasHomogeneousSimplexSolution gammaDagger := by
  obtain ⟨hleft, hright⟩ := gammaDagger_twoSidedInverse
  exact ⟨isStandardQMatrix_of_positive_rightInverse
      gammaDagger gammaDaggerInverse hleft gammaDaggerInverse_positive,
    noHomogeneousSimplexSolution_of_positive_leftInverse
      gammaDagger gammaDaggerInverse hright gammaDaggerInverse_positive⟩

theorem gammaDoubleDagger_standardQ_and_noHomogeneous :
    IsStandardQMatrix gammaDoubleDagger ∧
      ¬HasHomogeneousSimplexSolution gammaDoubleDagger := by
  obtain ⟨hleft, hright⟩ := gammaDoubleDagger_twoSidedInverse
  exact ⟨isStandardQMatrix_of_positive_rightInverse
      gammaDoubleDagger gammaDoubleDaggerInverse hleft
        gammaDoubleDaggerInverse_positive,
    noHomogeneousSimplexSolution_of_positive_leftInverse
      gammaDoubleDagger gammaDoubleDaggerInverse hright
        gammaDoubleDaggerInverse_positive⟩

def oppositePair : Finset (Fin 4) := {0, 2}

def oppositePairEquiv : Fin 2 ≃ oppositePair where
  toFun i := if i = 0 then ⟨0, by decide⟩ else ⟨2, by decide⟩
  invFun i := if i.1 = 0 then 0 else 1
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by
    apply Subtype.ext
    have hi : i.1 = 0 ∨ i.1 = 2 := by
      simpa only [oppositePair, Finset.mem_insert, Finset.mem_singleton] using i.2
    rcases hi with hi | hi <;> simp [hi]

theorem reindex_oppositePair_gammaStar :
    reindexMatrix oppositePairEquiv.symm (principalMatrix gammaStar oppositePair) =
      negativePairMatrix 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reindexMatrix, principalMatrix, oppositePairEquiv, gammaStar,
      negativePairMatrix, Matrix.cons_val_two]

theorem reindex_oppositePair_gammaDagger :
    reindexMatrix oppositePairEquiv.symm (principalMatrix gammaDagger oppositePair) =
      negativePairMatrix (9 / 10) 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reindexMatrix, principalMatrix, oppositePairEquiv, gammaDagger,
      negativePairMatrix, Matrix.cons_val_two]

theorem reindex_oppositePair_gammaDoubleDagger :
    reindexMatrix oppositePairEquiv.symm
        (principalMatrix gammaDoubleDagger oppositePair) =
      negativePairMatrix 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reindexMatrix, principalMatrix, oppositePairEquiv, gammaDoubleDagger,
      negativePairMatrix, Matrix.cons_val_two]

theorem not_projectiveQBar_of_oppositePair
    (M : Matrix (Fin 4) (Fin 4) ℝ) (u v : ℝ) (hu : 0 < u) (hv : 0 < v)
    (hmatrix : reindexMatrix oppositePairEquiv.symm
      (principalMatrix M oppositePair) = negativePairMatrix u v) :
    ¬IsProjectiveQBarMatrix M := by
  intro hQbar
  have hprincipal := hQbar oppositePair (by simp [oppositePair])
  have hreindexed := (isProjectiveQMatrix_reindexMatrix_iff
    oppositePairEquiv.symm (principalMatrix M oppositePair)).2 hprincipal
  rw [hmatrix] at hreindexed
  exact negativePairMatrix_not_projectiveQ u v hu hv hreindexed

theorem gammaStar_not_projectiveQBar : ¬IsProjectiveQBarMatrix gammaStar :=
  not_projectiveQBar_of_oppositePair gammaStar 1 1 (by norm_num) (by norm_num)
    reindex_oppositePair_gammaStar

theorem gammaDagger_not_projectiveQBar : ¬IsProjectiveQBarMatrix gammaDagger :=
  not_projectiveQBar_of_oppositePair gammaDagger (9 / 10) 1 (by norm_num)
    (by norm_num) reindex_oppositePair_gammaDagger

theorem gammaDoubleDagger_not_projectiveQBar :
    ¬IsProjectiveQBarMatrix gammaDoubleDagger :=
  not_projectiveQBar_of_oppositePair gammaDoubleDagger 1 1 (by norm_num)
    (by norm_num) reindex_oppositePair_gammaDoubleDagger

def cycleSuccessor : Fin 4 → Fin 4
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 0

theorem cycleSuccessor_ne (i : Fin 4) : cycleSuccessor i ≠ i := by
  fin_cases i <;> decide

theorem gammaStar_normalCore : normalCore gammaStar = Finset.univ := by
  apply normalCore_eq_univ_of_fixed_blocker gammaStar cycleSuccessor cycleSuccessor_ne
  intro i
  fin_cases i <;> norm_num [gammaStar, cycleSuccessor,
    Matrix.cons_val_two, Matrix.cons_val_three]

theorem gammaDagger_normalCore : normalCore gammaDagger = Finset.univ := by
  apply normalCore_eq_univ_of_fixed_blocker gammaDagger cycleSuccessor cycleSuccessor_ne
  intro i
  fin_cases i <;> norm_num [gammaDagger, cycleSuccessor,
    Matrix.cons_val_two, Matrix.cons_val_three]

theorem gammaDoubleDagger_normalCore :
    normalCore gammaDoubleDagger = Finset.univ := by
  apply normalCore_eq_univ_of_fixed_blocker
    gammaDoubleDagger cycleSuccessor cycleSuccessor_ne
  intro i
  fin_cases i <;> norm_num [gammaDoubleDagger, cycleSuccessor,
    Matrix.cons_val_two, Matrix.cons_val_three]

/-- The heterogeneous table has different negative-entry shapes in its first
two rows. This obstruction is invariant under positive row scaling. -/
theorem gammaDagger_not_uniformNegativeRowShape :
    ¬HasUniformNegativeRowShape gammaDagger := by
  intro h
  have h01 := h 0 1
  simp only [negativeRowSum_eq_sum_ite, negativeRowSquareSum_eq_sum_ite] at h01
  norm_num [gammaDagger, Fin.sum_univ_succ, Matrix.cons_val_two,
    Matrix.cons_val_three] at h01

/-- No simultaneous relabeling and positive row scaling makes this table circulant. -/
theorem gammaDagger_not_positiveRowScaledRelabelingRowCirculant :
    ¬IsPositiveRowScaledRelabelingRowCirculant gammaDagger := by
  exact fun h ↦ gammaDagger_not_uniformNegativeRowShape
    (hasUniformNegativeRowShape_of_positiveRowScaledRelabelingRowCirculant h)

end GameTheory.QuittingLCPClassification.SignedFourCycleMatrixFixtures

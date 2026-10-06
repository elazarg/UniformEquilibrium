import MathUE.LinearProgramming.CyclicChildSharedFixtureScreens
import UniformEquilibrium.Quitting.Classification.LCP.QuittingRewardAdapter
import UniformEquilibrium.Quitting.Examples.BoxedNashChargeFullCoreFixture
import UniformEquilibrium.Quitting.Examples.BoxedNashChargeTripleFixture

/-! # Actual boxed tables share one cyclic-child matrix

The full-core table has the literal shared matrix. The proper-triple table
has it after the displayed cyclic relabeling. Its regular-offset census and
degree are therefore supplied by the canonical mathematical fixture, not by
fresh LCP computations for either reward table.
-/

noncomputable section

namespace GameTheory.BoxedNashChargeSharedMatrix

open QuittingLCPClassification Math.LinearProgramming
open scoped Matrix

abbrev Gamma := Math.CyclicChildJointPhase.SharedFixture.matrix

/-- Canonical matrix coordinates to the proper-triple table coordinates. -/
def canonicalToTriple : Fin 4 ≃ Fin 4 where
  toFun player := player + 3
  invFun player := player + 1
  left_inv := by intro player; fin_cases player <;> rfl
  right_inv := by intro player; fin_cases player <;> rfl

theorem full_singletonMatrix_eq :
    quittingSingletonMatrix BoxedNashChargeFullCoreFixture.reward = Gamma := by
  change quittingSingletonMatrix BoxedNashChargeFullCoreFixture.reward =
    Math.CyclicChildJointPhase.SharedFixture.matrix
  rw [Math.CyclicChildJointPhase.SharedFixture.matrix_eq]
  funext receiver owner
  fin_cases receiver <;> fin_cases owner <;>
    norm_num [quittingSingletonMatrix, BoxedNashChargeFullCoreFixture.reward,
      Math.FiniteCoalition.binaryCode_finFour, Math.FiniteCoalition.binaryCode]

theorem triple_singletonMatrix_relabel_eq :
    (quittingSingletonMatrix BoxedNashChargeTripleFixture.reward).submatrix
      canonicalToTriple canonicalToTriple = Gamma := by
  change (quittingSingletonMatrix BoxedNashChargeTripleFixture.reward).submatrix
    canonicalToTriple canonicalToTriple = Math.CyclicChildJointPhase.SharedFixture.matrix
  rw [Math.CyclicChildJointPhase.SharedFixture.matrix_eq]
  funext receiver owner
  fin_cases receiver <;> fin_cases owner <;>
    norm_num [Matrix.submatrix, canonicalToTriple, quittingSingletonMatrix,
      BoxedNashChargeTripleFixture.reward,
      Math.FiniteCoalition.binaryCode_finFour, Math.FiniteCoalition.binaryCode]

theorem full_singletonMatrix_isR0 :
    IsR0Matrix (quittingSingletonMatrix BoxedNashChargeFullCoreFixture.reward) := by
  rw [full_singletonMatrix_eq]
  exact Math.CyclicChildJointPhase.SharedFixture.matrix_isR0

theorem full_regularOffset_solution_iff (weights : Fin 4 → ℝ) :
    IsStandardLCPSolution (quittingSingletonMatrix BoxedNashChargeFullCoreFixture.reward)
      Math.CyclicChildJointPhase.SharedFixture.offset weights ↔
        weights = Math.CyclicChildJointPhase.SharedFixture.root := by
  rw [full_singletonMatrix_eq]
  exact Math.CyclicChildJointPhase.SharedFixture.solution_iff weights

theorem full_singletonMatrix_degree_eq_one :
    r0Degree (quittingSingletonMatrix BoxedNashChargeFullCoreFixture.reward)
      full_singletonMatrix_isR0 = 1 := by
  simpa only [full_singletonMatrix_eq] using
    Math.CyclicChildJointPhase.SharedFixture.matrix_r0Degree_eq_one

theorem triple_relabel_regularOffset_solution_iff (weights : Fin 4 → ℝ) :
    IsStandardLCPSolution
      ((quittingSingletonMatrix BoxedNashChargeTripleFixture.reward).submatrix
        canonicalToTriple canonicalToTriple)
      Math.CyclicChildJointPhase.SharedFixture.offset weights ↔
        weights = Math.CyclicChildJointPhase.SharedFixture.root := by
  rw [triple_singletonMatrix_relabel_eq]
  exact Math.CyclicChildJointPhase.SharedFixture.solution_iff weights

theorem triple_relabel_singletonMatrix_isR0 :
    IsR0Matrix ((quittingSingletonMatrix BoxedNashChargeTripleFixture.reward).submatrix
      canonicalToTriple canonicalToTriple) := by
  rw [triple_singletonMatrix_relabel_eq]
  exact Math.CyclicChildJointPhase.SharedFixture.matrix_isR0

theorem triple_relabel_singletonMatrix_degree_eq_one :
    r0Degree ((quittingSingletonMatrix BoxedNashChargeTripleFixture.reward).submatrix
      canonicalToTriple canonicalToTriple) triple_relabel_singletonMatrix_isR0 = 1 := by
  simpa only [triple_singletonMatrix_relabel_eq] using
    Math.CyclicChildJointPhase.SharedFixture.matrix_r0Degree_eq_one

theorem full_singletonMatrix_inverse_not_nonnegative :
    ¬∀ receiver owner,
      0 ≤ (quittingSingletonMatrix BoxedNashChargeFullCoreFixture.reward)⁻¹ receiver owner := by
  rw [full_singletonMatrix_eq]
  exact Math.CyclicChildJointPhase.SharedFixture.full_inverse_not_nonnegative

theorem full_no_positive_singleton_pair (first second : Fin 4) :
    ¬(0 < quittingSingletonMatrix BoxedNashChargeFullCoreFixture.reward first second ∧
      0 < quittingSingletonMatrix BoxedNashChargeFullCoreFixture.reward second first) := by
  rw [full_singletonMatrix_eq]
  exact Math.CyclicChildJointPhase.SharedFixture.no_positive_pair first second

theorem full_no_nonnegative_deleted_inverse_and_passive_row (deleted : Fin 4) :
    let singleton := quittingSingletonMatrix BoxedNashChargeFullCoreFixture.reward
    let child := singleton.submatrix deleted.succAbove deleted.succAbove
    ¬((∀ receiver owner, 0 ≤ child⁻¹ receiver owner) ∧ ∀ receiver,
      0 ≤ ((fun owner => singleton deleted (deleted.succAbove owner)) ᵥ* child⁻¹) receiver) := by
  dsimp only
  rw [full_singletonMatrix_eq]
  exact Math.CyclicChildJointPhase.SharedFixture.no_nonnegative_deleted_inverse_and_passive_row
    deleted

theorem triple_relabel_inverse_not_nonnegative :
    ¬∀ receiver owner,
      0 ≤ ((quittingSingletonMatrix BoxedNashChargeTripleFixture.reward).submatrix
        canonicalToTriple canonicalToTriple)⁻¹ receiver owner := by
  rw [triple_singletonMatrix_relabel_eq]
  exact Math.CyclicChildJointPhase.SharedFixture.full_inverse_not_nonnegative

theorem full_principal_zero_three_not_standardQ :
    ¬IsStandardQ ((quittingSingletonMatrix BoxedNashChargeFullCoreFixture.reward).submatrix
      (![0, 3] : Fin 2 → Fin 4) ![0, 3]) := by
  rw [full_singletonMatrix_eq]
  exact Math.CyclicChildJointPhase.SharedFixture.pairZeroThree_not_standardQ

end GameTheory.BoxedNashChargeSharedMatrix

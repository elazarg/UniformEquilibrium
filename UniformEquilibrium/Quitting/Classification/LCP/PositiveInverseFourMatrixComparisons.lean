import MathUE.LinearProgramming.Examples.PositiveInverseFourMatrices
import MathUE.LinearProgramming.NonnegativeInverseDegree
import UniformEquilibrium.Quitting.Classification.LCP.PositiveInverse
import UniformEquilibrium.Quitting.Classification.LCP.ElementaryMatrixObstructions
import UniformEquilibrium.Quitting.Cycles.SignedFourCycleRewardAdapter

/-!
# Named matrix-class comparisons for the negative-determinant strict-inverse example

The full matrix is standard Q and has no nonzero homogeneous complementary
solution. Its principal on players zero, one, and three is not projective Q,
so the full matrix is not projective Q-bar. Every player survives normal-core
deletion. No relabeling supplies the named signed-four-cycle singleton data.

The underlying negative graph nevertheless has a covering six-edge closed
walk, proved in the matrix fixture. The cycle comparison concerns only the
once-per-owner signed-four-cycle hypothesis, not arbitrary repeated-owner
calendars or other reward-dependent equilibrium constructions.
-/

noncomputable section

namespace GameTheory.PositiveInverseFourMatrixComparisons

open _root_.Math.LinearProgramming QuittingLCPClassification
open _root_.Math.LinearProgramming.PositiveInverseFourMatrices
open _root_.Math.LinearProgramming.PositiveInverseFourMatrices.NegativeDeterminant

/-- Strict inverse positivity places the full matrix in the standard-Q class. -/
theorem isStandardQMatrix : QuittingLCPClassification.IsStandardQMatrix matrix :=
  isStandardQMatrix_of_positive_rightInverse matrix matrix⁻¹
    (Matrix.mul_nonsing_inv matrix (isUnit_iff_ne_zero.mpr det_neg.ne)) inverse_pos

/-- The same literal inverse excludes the full homogeneous simplex branch. -/
theorem noHomogeneous : ¬HasHomogeneousSimplexSolution matrix :=
  noHomogeneousSimplexSolution_of_positive_leftInverse matrix matrix⁻¹
    (Matrix.nonsing_inv_mul matrix (isUnit_iff_ne_zero.mpr det_neg.ne)) inverse_pos

theorem isR0Matrix : _root_.Math.LinearProgramming.IsR0Matrix matrix :=
  (isR0Matrix_iff_not_singletonLCPFeasible matrix).mpr noHomogeneous

def principalPlayers : Finset (Fin 4) := {0, 1, 3}

private def principalEquiv : Fin 3 ≃ principalPlayers where
  toFun i := ⟨![0, 1, 3] i, by fin_cases i <;> decide⟩
  invFun i := if i.1 = 0 then 0 else if i.1 = 1 then 1 else 2
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by
    apply Subtype.ext
    have hi : i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 3 := by
      simpa only [principalPlayers, Finset.mem_insert, Finset.mem_singleton] using i.2
    rcases hi with hi | hi | hi <;> simp [hi]

private theorem reindex_principal :
    reindexMatrix principalEquiv.symm (principalMatrix matrix principalPlayers) =
      !![0, 2, -3; -3, 0, 3; 3, -3, 0] := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [reindexMatrix, principalMatrix, principalEquiv, matrix]

/-- At offset minus one the three residual inequalities already contradict
projective normalization; complementarity is not needed for this obstruction. -/
theorem principal_noProjectiveSolution_neg_one :
    ¬HasProjectiveLCPSolution (principalMatrix matrix principalPlayers) (fun _ => -1) := by
  rintro ⟨original⟩
  have solution : ProjectiveLCPSolution
      (reindexMatrix principalEquiv.symm (principalMatrix matrix principalPlayers))
      (fun _ => -1) := original.reindex principalEquiv.symm
  rw [reindex_principal] at solution
  have hzero := solution.residual_nonneg 0
  have hone := solution.residual_nonneg 1
  have htwo := solution.residual_nonneg 2
  norm_num [Fin.sum_univ_succ] at hzero hone htwo
  have hc := solution.cemetery_nonneg
  have hx := solution.singleton_nonneg 0
  have hy := solution.singleton_nonneg 1
  have hz := solution.singleton_nonneg 2
  have htotal := solution.total
  norm_num [Fin.sum_univ_succ] at htotal
  linarith

/-- In particular, the ordinary principal LCP fails at the literal offset minus one. -/
theorem principal_noStandardSolution_neg_one :
    ¬HasStandardLCPSolution (principalMatrix matrix principalPlayers) (fun _ => -1) := by
  rintro ⟨solution⟩
  exact principal_noProjectiveSolution_neg_one ⟨solution.toProjective⟩

theorem principal_not_projectiveQ :
    ¬IsProjectiveQMatrix (principalMatrix matrix principalPlayers) := by
  intro hprincipal
  exact principal_noProjectiveSolution_neg_one (hprincipal (fun _ => -1))

theorem principal_noHomogeneous :
    ¬HasHomogeneousSimplexSolution (principalMatrix matrix principalPlayers) := by
  intro hhomogeneous
  exact principal_not_projectiveQ
    ((isProjectiveQMatrix_iff_standard_or_homogeneous _).mpr (Or.inr hhomogeneous))

theorem not_projectiveQBar : ¬IsProjectiveQBarMatrix matrix := by
  intro hQbar
  exact principal_not_projectiveQ (hQbar principalPlayers (by simp [principalPlayers]))

/-- The displayed negative blocker in every row preserves the full normal core. -/
theorem normalCore_eq_univ : normalCore matrix = Finset.univ :=
  normalCore_eq_univ_of_fixed_blocker matrix negativeBlocker negativeBlocker_ne
    (fun player => (negativeBlocker_entry player).le)

/-- No relabeling of the literal matrix supplies the named once-per-owner
signed-four-cycle input. The covering repeated-owner walk remains available. -/
theorem not_nonempty_signedFourCycleSingletonData_of_reindex
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (order : Equiv.Perm (Fin 4))
    (hmatrix : ∀ row column,
      quittingSingletonMatrix reward row column = matrix (order row) (order column)) :
    ¬Nonempty (SignedFourCycleSingletonData reward) := by
  rintro ⟨data⟩
  apply not_negative_hamiltonianCycle order
  intro phase
  rw [← hmatrix, data.successor]
  exact neg_neg_of_pos (data.b_pos phase)

/-- The paired positive-determinant example also has full R0, obtained from
its actual strictly positive inverse and the homogeneous dictionary. -/
theorem paired_isR0Matrix : _root_.Math.LinearProgramming.IsR0Matrix Paired.matrix := by
  apply (isR0Matrix_iff_not_singletonLCPFeasible Paired.matrix).mpr
  exact noHomogeneousSimplexSolution_of_positive_leftInverse Paired.matrix Paired.matrix⁻¹
    (Matrix.nonsing_inv_mul Paired.matrix (isUnit_iff_ne_zero.mpr Paired.det_pos.ne'))
    Paired.inverse_pos

/-- Its canonical integer degree is plus one, so this matrix cannot trigger
the degree-different-from-one criterion. This is not a nonexistence claim. -/
theorem paired_r0Degree_eq_one : r0Degree Paired.matrix paired_isR0Matrix = 1 := by
  rw [r0Degree_eq_sign_det_of_nonnegative_inverse Paired.matrix paired_isR0Matrix
    Paired.det_pos.ne' (fun row column => (Paired.inverse_pos row column).le),
    sign_pos Paired.det_pos]
  rfl

end GameTheory.PositiveInverseFourMatrixComparisons

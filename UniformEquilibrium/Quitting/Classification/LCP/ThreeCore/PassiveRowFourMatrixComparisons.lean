/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.PassiveRowFourDegreeNeighborhood
import UniformEquilibrium.Quitting.Classification.LCP.ElementaryMatrixObstructions
import UniformEquilibrium.Quitting.Cycles.SignedFourCycleRewardAdapter
import UniformEquilibrium.Quitting.Classification.LCP.QuittingRewardReindex
import MathUE.LinearProgramming.Tournament

/-!
# Named matrix-class comparisons for the passive-row fixture

The packet's full matrix has determinant three and a negative inverse entry.
Its principal on players zero and three is the canonical negative-pair
obstruction to projective Q, so the full matrix fails projective Q-bar.
Its negative graph excludes the named signed-four-cycle singleton input under
every player relabeling. Its negative corner quadratic form excludes the
literal fractional-tournament matrix family with parameter at least one.
These comparisons do not address arbitrary diagonal scaling, other cycle
classes, or a reward-dependent punishment-normal principal.
-/

noncomputable section

namespace GameTheory.PassiveRowFourMatrixComparisons

open _root_.Math.LinearProgramming QuittingLCPClassification
open PassiveRowFourFixture (matrix)

/-- The packet's full inverse is certified by exact matrix multiplication. -/
theorem matrix_inverse : matrix⁻¹ =
    (1 / 3 : ℝ) • !![2, 2, 2, -1; 5, 2, 8, -4; -4, -1, -7, 5; -8, -2, -11, 7] := by
  apply Matrix.inv_eq_left_inv
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [matrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

theorem inverse_entry_zero_three : matrix⁻¹ 0 3 = -(1 / 3 : ℝ) := by
  rw [matrix_inverse]
  norm_num

/-- The full matrix does not satisfy the entrywise nonnegative inverse test. -/
theorem not_nonnegative_inverse : ¬∀ row column, 0 ≤ matrix⁻¹ row column := by
  intro hnonnegative
  have hentry := hnonnegative 0 3
  rw [inverse_entry_zero_three] at hentry
  norm_num at hentry

/-- Reuse the existing full-support determinant from the finite inventory. -/
theorem det_eq : matrix.det = 3 := by
  have hselected : lcpSelectedMatrix matrix (1 : Fin 4 → ℝ) = matrix := by
    ext row column
    simp [lcpSelectedMatrix]
  have hfull (who : Fin 4) :
      who ∈ PassiveRowFourDegreeNeighborhood.support 10 ↔
        0 < (1 : Fin 4 → ℝ) who := by
    fin_cases who <;> norm_num [PassiveRowFourDegreeNeighborhood.support]
  calc
    matrix.det = (lcpSelectedMatrix matrix (1 : Fin 4 → ℝ)).det :=
      congrArg Matrix.det hselected.symm
    _ = (matrix.toSquareBlockProp (fun who => 0 < (1 : Fin 4 → ℝ) who)).det :=
      det_lcpSelectedMatrix matrix 1
    _ = (matrix.toSquareBlockProp
        (fun who => who ∈ PassiveRowFourDegreeNeighborhood.support 10)).det :=
      by
        have htransport := Matrix.equiv_block_det matrix hfull
        have hfinite :
            Finset.Subtype.fintype (PassiveRowFourDegreeNeighborhood.support 10) =
              Subtype.fintype
                (fun who => who ∈ PassiveRowFourDegreeNeighborhood.support 10) :=
          Subsingleton.elim _ _
        rw [← hfinite] at htransport
        exact htransport
    _ = PassiveRowFourDegreeNeighborhood.determinant 10 :=
      PassiveRowFourDegreeNeighborhood.principal_det_eq 10
    _ = 3 := by norm_num [PassiveRowFourDegreeNeighborhood.determinant]

theorem det_pos : 0 < matrix.det := by
  rw [det_eq]
  norm_num

theorem not_negative_determinant : ¬matrix.det < 0 := not_lt_of_ge det_pos.le

/-- The reciprocal negative corner pair used in the packet comparison. -/
def cornerPair : Finset (Fin 4) := {0, 3}

private def cornerPairEquiv : Fin 2 ≃ cornerPair where
  toFun who := if who = 0 then ⟨0, by decide⟩ else ⟨3, by decide⟩
  invFun who := if who.1 = 0 then 0 else 1
  left_inv who := by fin_cases who <;> rfl
  right_inv who := by
    apply Subtype.ext
    have hwho : who.1 = 0 ∨ who.1 = 3 := by
      simpa only [cornerPair, Finset.mem_insert, Finset.mem_singleton] using who.2
    rcases hwho with hwho | hwho <;> simp [hwho]

/-- The corner principal is the existing negative-pair matrix at parameters two and one. -/
private theorem reindex_cornerPair :
    reindexMatrix cornerPairEquiv.symm (principalMatrix matrix cornerPair) =
      negativePairMatrix 2 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [reindexMatrix, principalMatrix, cornerPairEquiv, matrix, negativePairMatrix]

theorem cornerPrincipal_not_projectiveQ :
    ¬IsProjectiveQMatrix (principalMatrix matrix cornerPair) := by
  intro hprincipal
  have hpair := (isProjectiveQMatrix_reindexMatrix_iff
    cornerPairEquiv.symm (principalMatrix matrix cornerPair)).mpr hprincipal
  rw [reindex_cornerPair] at hpair
  exact negativePairMatrix_not_projectiveQ 2 1 (by norm_num) (by norm_num) hpair

/-- Apply projective Q-bar's exact principal test to the corner pair. -/
theorem not_projectiveQBar : ¬IsProjectiveQBarMatrix matrix := by
  intro hQbar
  exact cornerPrincipal_not_projectiveQ (hQbar cornerPair (by simp [cornerPair]))

/-- The packet's negative-entry graph consists of exactly these five edges. -/
theorem negative_entry_iff (row column : Fin 4) : matrix row column < 0 ↔
    (row = 0 ∧ column = 1) ∨ (row = 0 ∧ column = 3) ∨
      (row = 1 ∧ column = 2) ∨ (row = 2 ∧ column = 0) ∨
        (row = 3 ∧ column = 0) := by
  fin_cases row <;> fin_cases column <;> norm_num [matrix]

private theorem row_two_negative_iff (column : Fin 4) :
    matrix 2 column < 0 ↔ column = 0 := by
  rw [negative_entry_iff]
  simp

private theorem row_three_negative_iff (column : Fin 4) :
    matrix 3 column < 0 ↔ column = 0 := by
  rw [negative_entry_iff]
  simp

/-- Two distinct vertices have the same unique negative successor, excluding
a negative Hamiltonian cycle under every player ordering. -/
theorem not_negative_hamiltonianCycle (order : Equiv.Perm (Fin 4)) :
    ¬∀ phase, matrix (order phase) (order (phase + 1)) < 0 := by
  intro hcycle
  have htwo : order (order.symm 2 + 1) = 0 := by
    apply (row_two_negative_iff _).mp
    simpa only [order.apply_symm_apply] using hcycle (order.symm 2)
  have hthree : order (order.symm 3 + 1) = 0 := by
    apply (row_three_negative_iff _).mp
    simpa only [order.apply_symm_apply] using hcycle (order.symm 3)
  have hsame : order.symm 2 = order.symm 3 :=
    add_right_cancel (order.injective (htwo.trans hthree.symm))
  have himpossible : (2 : Fin 4) = 3 := order.symm.injective hsame
  norm_num at himpossible

/-- Every relabeled literal singleton matrix fails the named negative-successor input. -/
theorem not_nonempty_signedFourCycleSingletonData_of_reindex
    (reward : PassiveRowFourFixture.Reward) (order : Equiv.Perm (Fin 4))
    (hmatrix : ∀ row column,
      quittingSingletonMatrix reward row column = matrix (order row) (order column)) :
    ¬Nonempty (SignedFourCycleSingletonData reward) := by
  rintro ⟨data⟩
  apply not_negative_hamiltonianCycle order
  intro phase
  rw [← hmatrix, data.successor]
  exact neg_neg_of_pos (data.b_pos phase)

private theorem singletonMatrix_rewardReindex
    (reward : PassiveRowFourFixture.Reward) (order : Equiv.Perm (Fin 4)) :
    quittingSingletonMatrix (quittingRewardReindex order reward) =
      reindexMatrix order (quittingSingletonMatrix reward) := by
  exact quittingSingletonMatrix_rewardReindex order reward

/-- No relabeling of any reward completion of the fixture supplies the named
signed-four-cycle singleton data. Own singleton and nonsingleton rewards are free. -/
theorem not_nonempty_signedFourCycleSingletonData_rewardReindex
    (reward : PassiveRowFourFixture.Reward)
    (hmatrix : quittingSingletonMatrix reward = matrix) (order : Equiv.Perm (Fin 4)) :
    ¬Nonempty (SignedFourCycleSingletonData (quittingRewardReindex order reward)) := by
  apply not_nonempty_signedFourCycleSingletonData_of_reindex _ order.symm
  intro row column
  rw [singletonMatrix_rewardReindex, hmatrix]
  rfl

/-- A nonnegative vector supported on the reciprocal negative corner pair. -/
def cornerVector : Fin 4 → ℝ := ![1, 0, 0, 1]

theorem cornerVector_nonnegative (who : Fin 4) : 0 ≤ cornerVector who := by
  fin_cases who <;> norm_num [cornerVector]

theorem corner_quadratic_eq_neg_three :
    (∑ row, cornerVector row * ∑ column, cornerVector column * matrix row column) = -3 := by
  norm_num [cornerVector, matrix, Fin.sum_univ_succ]

/-- The negative corner energy excludes even fractional tournament matrices
with parameter at least one, hence the packet's literal integral-tournament family. -/
theorem not_tournamentSkewMatrix (t : ℝ) (A : Fin 4 → Fin 4 → ℝ)
    (hA : IsFractionalTournament A) (ht : 1 ≤ t) :
    matrix ≠ tournamentSkewMatrix t A := by
  intro hequal
  have hquadratic := tournamentSkewMatrix_quadratic_nonneg
    t A hA ht cornerVector cornerVector_nonnegative
  rw [← hequal, corner_quadratic_eq_neg_three] at hquadratic
  norm_num at hquadratic

end GameTheory.PassiveRowFourMatrixComparisons

/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import UniformEquilibrium.Quitting.Classification.LCP.MatrixClasses
import UniformEquilibrium.Quitting.Examples.BlockPair.FourPlayerPairedSingleton

/-!
# No nonnegative-inverse triple in the paired singleton matrix

Every three-player principal contains one reciprocal positive pair and an
isolated member of the other pair. Its determinant is six, but the inverse
diagonal at that isolated member is negative. This excludes the literal
passive-row triple test, not equilibrium existence for any completion.
-/

noncomputable section

namespace GameTheory.FourPlayerPairedSingleton

open QuittingLCPClassification

private def tripleSupport (missing : Player) : Finset Player :=
  Finset.univ.erase missing

private def triplePlayer : Player → Fin 3 → Player :=
  ![![1, 2, 3], ![0, 2, 3], ![0, 1, 3], ![0, 1, 2]]

private theorem triplePlayer_mem (missing : Player) (index : Fin 3) :
    triplePlayer missing index ∈ tripleSupport missing := by
  exact (by decide : ∀ missing : Player, ∀ index : Fin 3,
    triplePlayer missing index ∈ tripleSupport missing) missing index

private def tripleEquiv (missing : Player) : Fin 3 ≃ tripleSupport missing :=
  Equiv.ofBijective (fun index => ⟨triplePlayer missing index, triplePlayer_mem _ _⟩) (by
    constructor
    · intro left right heq
      have hinjective := (by decide : ∀ missing : Player,
        Function.Injective (triplePlayer missing)) missing
      exact hinjective (congrArg Subtype.val heq)
    · intro who
      obtain ⟨index, hindex⟩ := (by decide : ∀ missing who : Player,
        who ∈ tripleSupport missing → ∃ index : Fin 3,
          triplePlayer missing index = who) missing who.1 who.2
      exact ⟨index, Subtype.ext hindex⟩)

private theorem tripleSupport_complete (players : Finset Player)
    (hcard : players.card = 3) : ∃ missing, players = tripleSupport missing := by
  exact (by decide : ∀ players : Finset Player, players.card = 3 →
    ∃ missing : Player, players = tripleSupport missing) players hcard

private def tripleMatrix (missing : Player) : Matrix (Fin 3) (Fin 3) ℝ :=
  (Matrix.of (principalMatrix pairedSingletonMatrix (tripleSupport missing))).submatrix
    (tripleEquiv missing) (tripleEquiv missing)

private theorem tripleMatrix_apply (missing : Player) (row column : Fin 3) :
    tripleMatrix missing row column =
      pairedSingletonMatrix (triplePlayer missing row) (triplePlayer missing column) := rfl

private def tripleInverse (missing : Player) : Matrix (Fin 3) (Fin 3) ℝ :=
  if missing.val < 2 then
    !![-3 / 2, -1 / 2, -1 / 2; -1 / 2, -1 / 6, 1 / 6; -1 / 2, 1 / 6, -1 / 6]
  else
    !![-1 / 6, 1 / 6, -1 / 2; 1 / 6, -1 / 6, -1 / 2; -1 / 2, -1 / 2, -3 / 2]

private theorem tripleMatrix_inverse (missing : Player) :
    (tripleMatrix missing)⁻¹ = tripleInverse missing := by
  apply Matrix.inv_eq_left_inv
  ext row column
  fin_cases missing <;> fin_cases row <;> fin_cases column <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, tripleMatrix_apply,
      tripleInverse, triplePlayer, pairedSingletonMatrix, Matrix.one_apply]

private def isolatedIndex : Player → Fin 3 := ![0, 0, 2, 2]

/-- Every three-player principal of the literal paired singleton matrix has
determinant six, so the failure below is not a singularity failure. -/
theorem pairedSingletonMatrix_principal_triple_det
    (players : Finset Player) (hcard : players.card = 3) :
    (Matrix.of (principalMatrix pairedSingletonMatrix players)).det = 6 := by
  obtain ⟨missing, rfl⟩ := tripleSupport_complete players hcard
  rw [← Matrix.det_submatrix_equiv_self (tripleEquiv missing)]
  change (tripleMatrix missing).det = 6
  fin_cases missing <;>
    norm_num [Matrix.det_fin_three, tripleMatrix_apply, triplePlayer, pairedSingletonMatrix]

/-- The member whose partner was removed has inverse diagonal minus three
halves in every three-player principal. -/
theorem pairedSingletonMatrix_principal_triple_negative_diagonal
    (players : Finset Player) (hcard : players.card = 3) :
    ∃ who : players,
      (Matrix.of (principalMatrix pairedSingletonMatrix players))⁻¹ who who =
        -(3 / 2 : ℝ) := by
  obtain ⟨missing, rfl⟩ := tripleSupport_complete players hcard
  let index := isolatedIndex missing
  refine ⟨tripleEquiv missing index, ?_⟩
  have hinverse := Matrix.inv_submatrix_equiv
    (Matrix.of (principalMatrix pairedSingletonMatrix (tripleSupport missing)))
      (tripleEquiv missing) (tripleEquiv missing)
  have hentry := congrFun (congrFun hinverse index) index
  change (tripleMatrix missing)⁻¹ index index =
    (Matrix.of (principalMatrix pairedSingletonMatrix (tripleSupport missing)))⁻¹
      (tripleEquiv missing index) (tripleEquiv missing index) at hentry
  rw [← hentry, tripleMatrix_inverse]
  fin_cases missing <;> norm_num [tripleInverse, index, isolatedIndex]

/-- No principal triple of this matrix has an entrywise nonnegative inverse.
This is an exclusion from the passive-row sufficient test only. -/
theorem pairedSingletonMatrix_principal_triple_not_nonnegative_inverse
    (players : Finset Player) (hcard : players.card = 3) :
    ¬ ∀ row column : players,
      0 ≤ (Matrix.of (principalMatrix pairedSingletonMatrix players))⁻¹ row column := by
  intro hnonnegative
  obtain ⟨who, hnegative⟩ := pairedSingletonMatrix_principal_triple_negative_diagonal
    players hcard
  have h := hnonnegative who who
  rw [hnegative] at h
  norm_num at h

end GameTheory.FourPlayerPairedSingleton

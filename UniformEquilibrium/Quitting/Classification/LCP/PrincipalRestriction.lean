/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.MatrixClasses

/-!
# Reindexing and principal restriction for projective LCP matrices

Projective LCP solutions and the projective-Q property are invariant under
finite reindexing. Projective Q-bar is inherited by every principal matrix.
The flattening declarations below make the nested-subtype identification
explicit and reusable.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open Finset
open Math.LinearProgramming

variable {ι κ : Type} [Fintype ι] [DecidableEq ι]

section ProjectiveReindex

variable [Fintype κ]

/-- Transport a projective LCP solution along an equivalence of coordinate
types. -/
def ProjectiveLCPSolution.reindex (e : ι ≃ κ) {M : ι → ι → ℝ}
    {q : κ → ℝ}
    (solution : ProjectiveLCPSolution M (fun i => q (e i))) :
    ProjectiveLCPSolution (reindexMatrix e M) q where
  cemetery := solution.cemetery
  singleton := fun i => solution.singleton (e.symm i)
  cemetery_nonneg := solution.cemetery_nonneg
  singleton_nonneg := fun i => solution.singleton_nonneg (e.symm i)
  total := by
    rw [Equiv.sum_comp e.symm]
    exact solution.total
  residual_nonneg := by
    intro i
    have h := solution.residual_nonneg (e.symm i)
    change 0 ≤ solution.cemetery * q i +
      ∑ j : κ, solution.singleton (e.symm j) *
        M (e.symm i) (e.symm j)
    rw [Equiv.sum_comp e.symm
      (fun j => solution.singleton j * M (e.symm i) j)]
    simpa using h
  complementary := by
    intro i
    have h := solution.complementary (e.symm i)
    change solution.singleton (e.symm i) *
      (solution.cemetery * q i +
        ∑ j : κ, solution.singleton (e.symm j) *
          M (e.symm i) (e.symm j)) = 0
    rw [Equiv.sum_comp e.symm
      (fun j => solution.singleton j * M (e.symm i) j)]
    simpa using h

omit [DecidableEq ι] in
/-- Projective Q is invariant under a finite reindexing. -/
theorem isProjectiveQMatrix_reindexMatrix_iff (e : ι ≃ κ)
    (M : ι → ι → ℝ) :
    IsProjectiveQMatrix (reindexMatrix e M) ↔ IsProjectiveQMatrix M := by
  constructor
  · intro hQ q
    obtain ⟨solution⟩ := hQ (fun i => q (e.symm i))
    have transported := solution.reindex e.symm
    have hmatrix : reindexMatrix e.symm (reindexMatrix e M) = M := by
      funext i j
      simp [reindexMatrix]
    rw [hmatrix] at transported
    simpa using ⟨transported⟩
  · intro hQ q
    obtain ⟨solution⟩ := hQ (fun i => q (e i))
    exact ⟨solution.reindex e⟩

end ProjectiveReindex

section ProjectiveQBarReindex

variable [Fintype κ] [DecidableEq κ]

/-- A finite coordinate set transported through an equivalence is canonically
equivalent to the original coordinate set. -/
def reindexFinsetEquiv (e : ι ≃ κ) (players : Finset κ) :
    players.map e.symm.toEmbedding ≃ players where
  toFun i := ⟨e i.1, by
    obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp i.2
    have heq : e i.1 = j := by
      rw [← hji]
      exact e.apply_symm_apply j
    simpa [heq] using hj⟩
  invFun j := ⟨e.symm j.1,
    Finset.mem_map.mpr ⟨j.1, j.2, rfl⟩⟩
  left_inv i := Subtype.ext (e.symm_apply_apply i.1)
  right_inv j := Subtype.ext (e.apply_symm_apply j.1)

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
@[simp] theorem reindexFinsetEquiv_apply_val
    (e : ι ≃ κ) (players : Finset κ)
    (i : players.map e.symm.toEmbedding) :
    (reindexFinsetEquiv e players i).1 = e i.1 := rfl

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
@[simp] theorem reindexFinsetEquiv_symm_apply_val
    (e : ι ≃ κ) (players : Finset κ) (i : players) :
    ((reindexFinsetEquiv e players).symm i).1 = e.symm i.1 := rfl

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- Reindexing commutes with taking a principal matrix, up to the canonical
equivalence of its coordinate subtypes. -/
theorem reindexMatrix_reindexFinsetEquiv_principalMatrix
    (e : ι ≃ κ) (M : ι → ι → ℝ) (players : Finset κ) :
    reindexMatrix (reindexFinsetEquiv e players)
      (principalMatrix M (players.map e.symm.toEmbedding)) =
        principalMatrix (reindexMatrix e M) players := by
  funext i j
  simp [reindexMatrix, principalMatrix]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- Projective Q-bar is preserved by a finite reindexing. -/
theorem isProjectiveQBarMatrix_reindexMatrix_of
    (e : ι ≃ κ) (M : ι → ι → ℝ)
    (hQ : IsProjectiveQBarMatrix M) :
    IsProjectiveQBarMatrix (reindexMatrix e M) := by
  intro players hplayers
  have horiginal : (players.map e.symm.toEmbedding).Nonempty := by
    simpa using hplayers
  have hprincipal := hQ (players.map e.symm.toEmbedding) horiginal
  rw [← reindexMatrix_reindexFinsetEquiv_principalMatrix]
  exact (isProjectiveQMatrix_reindexMatrix_iff
    (reindexFinsetEquiv e players)
    (principalMatrix M (players.map e.symm.toEmbedding))).2 hprincipal

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- Projective Q-bar is invariant under a finite reindexing. -/
theorem isProjectiveQBarMatrix_reindexMatrix_iff
    (e : ι ≃ κ) (M : ι → ι → ℝ) :
    IsProjectiveQBarMatrix (reindexMatrix e M) ↔
      IsProjectiveQBarMatrix M := by
  constructor
  · intro hQ
    have hback := isProjectiveQBarMatrix_reindexMatrix_of
      e.symm (reindexMatrix e M) hQ
    have hmatrix : reindexMatrix e.symm (reindexMatrix e M) = M := by
      funext i j
      simp [reindexMatrix]
    rwa [hmatrix] at hback
  · exact isProjectiveQBarMatrix_reindexMatrix_of e M

end ProjectiveQBarReindex

/-- Flatten a finite set of coordinates of a principal matrix back to the
ambient coordinate type. -/
def flattenPrincipalPlayers (outer : Finset ι) (inner : Finset outer) :
    Finset ι :=
  inner.map ⟨Subtype.val, Subtype.val_injective⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem mem_flattenPrincipalPlayers
    (outer : Finset ι) (inner : Finset outer) (who : ι) :
    who ∈ flattenPrincipalPlayers outer inner ↔
      ∃ hwho : who ∈ outer, (⟨who, hwho⟩ : outer) ∈ inner := by
  simp [flattenPrincipalPlayers]

/-- The coordinates of a nested principal matrix are canonically equivalent
to their flattened ambient coordinates. -/
def nestedPrincipalEquiv (outer : Finset ι) (inner : Finset outer) :
    inner ≃ flattenPrincipalPlayers outer inner where
  toFun i := ⟨i.1.1, (mem_flattenPrincipalPlayers outer inner i.1.1).2
    ⟨i.1.2, i.2⟩⟩
  invFun j :=
    let h := (mem_flattenPrincipalPlayers outer inner j.1).1 j.2
    ⟨⟨j.1, h.choose⟩, h.choose_spec⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem nestedPrincipalEquiv_apply_val
    (outer : Finset ι) (inner : Finset outer) (i : inner) :
    ((nestedPrincipalEquiv outer inner i :
      flattenPrincipalPlayers outer inner) : ι) = i.1.1 := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem nestedPrincipalEquiv_symm_apply_val
    (outer : Finset ι) (inner : Finset outer)
    (i : flattenPrincipalPlayers outer inner) :
    ((nestedPrincipalEquiv outer inner).symm i).1.1 = i.1 := rfl

omit [Fintype ι] [DecidableEq ι] in
/-- Flattening nested principal coordinates turns the nested principal matrix
into the literal ambient principal matrix. -/
theorem reindexMatrix_nestedPrincipalEquiv_principalMatrix
    (M : ι → ι → ℝ) (outer : Finset ι) (inner : Finset outer) :
    reindexMatrix (nestedPrincipalEquiv outer inner)
      (principalMatrix (principalMatrix M outer) inner) =
        principalMatrix M (flattenPrincipalPlayers outer inner) := by
  funext i j
  simp [reindexMatrix, principalMatrix]

omit [Fintype ι] [DecidableEq ι] in
/-- Projective Q-bar on the ambient matrix implies projective Q-bar on any
principal matrix. -/
theorem isProjectiveQBarMatrix_principalMatrix
    (M : ι → ι → ℝ) (outer : Finset ι)
    (hQ : IsProjectiveQBarMatrix M) :
    IsProjectiveQBarMatrix (principalMatrix M outer) := by
  classical
  intro inner hinner
  have hambient : (flattenPrincipalPlayers outer inner).Nonempty := by
    simpa [flattenPrincipalPlayers] using hinner
  have hambientQ := hQ (flattenPrincipalPlayers outer inner) hambient
  rw [← reindexMatrix_nestedPrincipalEquiv_principalMatrix] at hambientQ
  exact (isProjectiveQMatrix_reindexMatrix_iff
    (nestedPrincipalEquiv outer inner)
    (principalMatrix (principalMatrix M outer) inner)).1 hambientQ

end QuittingLCPClassification
end GameTheory

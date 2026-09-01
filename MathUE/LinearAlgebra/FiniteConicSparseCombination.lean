/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.NormalizedFarkasBasis

/-!
# Sparse nonnegative representations in a finite-dimensional cone

A nonnegative representation of one fixed finite-dimensional vector can be
replaced by another representation of the same vector whose positive support
has cardinality at most the ambient coordinate dimension.  This is the conic,
rather than affine, Caratheodory bound.
-/

noncomputable section

namespace Math
namespace LinearAlgebra

variable {Coordinate Generator : Type*}
variable [Fintype Coordinate] [Fintype Generator]

omit [Fintype Coordinate] in
/-- A finite nonnegative representation of a fixed vector can be chosen with
linearly independent positive-support columns. -/
theorem exists_nonnegative_finiteCombination_eq_with_linearIndependent_support
    (vector : Generator → Coordinate → ℝ)
    (target : Coordinate → ℝ)
    (coefficient : Generator → ℝ)
    (hnonnegative : ∀ generator, 0 ≤ coefficient generator)
    (hreconstruct : ∀ coordinate,
      ∑ generator, coefficient generator * vector generator coordinate =
        target coordinate) :
    ∃ sparse : Generator → ℝ,
      (∀ generator, 0 ≤ sparse generator) ∧
      (∀ coordinate,
        ∑ generator, sparse generator * vector generator coordinate =
          target coordinate) ∧
      LinearIndependent ℝ
        (fun generator : {generator // sparse generator ≠ 0} ↦
          vector generator.1) := by
  classical
  let matrix : Matrix Coordinate Generator ℝ :=
    fun coordinate generator ↦ vector generator coordinate
  have hfeasible : coefficient ∈ standardFeasibleSet matrix target := by
    refine ⟨hnonnegative, funext fun coordinate ↦ ?_⟩
    simpa only [matrix, Matrix.mulVec, dotProduct, mul_comm] using
      hreconstruct coordinate
  have hoptimal : IsStandardOptimal matrix target (fun _ ↦ 0) coefficient := by
    refine ⟨hfeasible, ?_⟩
    intro candidate hcandidate
    simp
  obtain ⟨sparse, hsparseExtreme, -, -⟩ :=
    exists_extreme_standardOptimal_of_standardOptimal
      matrix target (fun _ ↦ 0) hoptimal
  have hsparseFeasible := extremePoints_subset hsparseExtreme
  refine ⟨sparse, hsparseFeasible.1, ?_, ?_⟩
  · intro coordinate
    have hcoordinate := congrFun hsparseFeasible.2 coordinate
    simpa only [matrix, Matrix.mulVec, dotProduct, mul_comm] using hcoordinate
  · change LinearIndependent ℝ
      (fun generator : {generator // sparse generator ≠ 0} ↦
        matrix.col generator.1)
    exact linearIndependent_supportColumns_of_extreme_standardFeasible
      matrix target hsparseExtreme

/-- Conic Caratheodory for a finite indexed family: the same vector has a
nonnegative representation on at most the ambient number of coordinates. -/
theorem exists_nonnegative_finiteCombination_eq_support_card_le
    (vector : Generator → Coordinate → ℝ)
    (target : Coordinate → ℝ)
    (coefficient : Generator → ℝ)
    (hnonnegative : ∀ generator, 0 ≤ coefficient generator)
    (hreconstruct : ∀ coordinate,
      ∑ generator, coefficient generator * vector generator coordinate =
        target coordinate) :
    ∃ sparse : Generator → ℝ,
      (∀ generator, 0 ≤ sparse generator) ∧
      (∀ coordinate,
        ∑ generator, sparse generator * vector generator coordinate =
          target coordinate) ∧
      Fintype.card {generator // sparse generator ≠ 0} ≤
        Fintype.card Coordinate := by
  obtain ⟨sparse, hnonnegativeSparse, hreconstructSparse, hlinear⟩ :=
    exists_nonnegative_finiteCombination_eq_with_linearIndependent_support
      vector target coefficient hnonnegative hreconstruct
  refine ⟨sparse, hnonnegativeSparse, hreconstructSparse, ?_⟩
  have hcard := hlinear.fintype_card_le_finrank
  simpa only [Module.finrank_fintype_fun_eq_card] using hcard

end LinearAlgebra
end Math

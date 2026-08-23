/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.OccupationFlowAlternative

/-!
# Strict separation of a finite convex hull from zero

If zero is not a convex combination of finitely many columns, an augmented
conic separation gives a Euclidean-normalized covector with one common
strictly positive margin on every column.
-/

open Finset BigOperators

namespace Math
namespace LinearAlgebra

noncomputable section

/-- Strict finite convex separation, with an explicit Euclidean
normalization shared by the covector and its positive margin. -/
theorem exists_euclideanUnit_strictConvexSeparator_fintype
    {D J : Type*} [Fintype D] [Fintype J]
    (column : J → D → ℝ)
    (hnot : ¬ ∃ weight : J → ℝ,
      (∀ j, 0 ≤ weight j) ∧
      (∑ j, weight j) = 1 ∧
      ∀ i, (∑ j, weight j * column j i) = 0) :
    ∃ covector : D → ℝ, ∃ margin : ℝ,
      0 < margin ∧
      (∑ i, covector i ^ 2) + margin ^ 2 = 1 ∧
      ∀ j, margin ≤ ∑ i, covector i * column j i := by
  let augmented : Option D → J → ℝ := fun coordinate j =>
    match coordinate with
    | none => 1
    | some i => column j i
  let target : Option D → ℝ := fun coordinate =>
    match coordinate with
    | none => 1
    | some _ => 0
  have hnotConic : ¬ ∃ weight : J → ℝ, (∀ j, 0 ≤ weight j) ∧
      ∀ coordinate, (∑ j, weight j * augmented coordinate j) =
        target coordinate := by
    rintro ⟨weight, hweight, hbalance⟩
    apply hnot
    refine ⟨weight, hweight, ?_, ?_⟩
    · simpa [augmented, target] using hbalance none
    · intro i
      simpa [augmented, target] using hbalance (some i)
  obtain ⟨extended, hunit, hcolumns, htarget⟩ :=
    exists_euclideanUnit_conicSeparator_fintype augmented target hnotConic
  let covector : D → ℝ := fun i => extended (some i)
  let margin : ℝ := -extended none
  refine ⟨covector, margin, ?_, ?_, ?_⟩
  · dsimp only [margin]
    have : extended none < 0 := by
      simpa [target] using htarget
    linarith
  · have hsplit : (∑ coordinate : Option D, extended coordinate ^ 2) =
        (∑ i : D, extended (some i) ^ 2) + extended none ^ 2 := by
      rw [Fintype.sum_option]
      ring
    rw [hsplit] at hunit
    simpa [covector, margin] using hunit
  · intro j
    have hcolumn := hcolumns j
    have hsplit : (∑ coordinate : Option D,
        extended coordinate * augmented coordinate j) =
          (∑ i : D, extended (some i) * column j i) + extended none := by
      rw [Fintype.sum_option]
      simp [augmented]
      ring
    rw [hsplit] at hcolumn
    dsimp only [covector, margin]
    linarith

end

end LinearAlgebra
end Math

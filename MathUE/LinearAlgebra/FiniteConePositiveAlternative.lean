/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.DirectedTransport.FiniteInequality.Basic
import MathUE.LinearAlgebra.FiniteConicSparseCombination

/-!
# Strict covectors or sparse nonnegative cone improvements

For a finite family of vectors, exactly one of two result-facing objects
exists: a strictly positive covector that is nonpositive on every vector, or
a nonnegative combination with a nonzero nonnegative value.  The latter can
be chosen on at most the ambient number of coordinates.
-/

noncomputable section

namespace Math
namespace LinearAlgebra

open scoped BigOperators

variable {Coordinate Generator : Type*}
variable [Fintype Coordinate] [Fintype Generator]

/-- A strictly positive covector which is nonpositive on every generator. -/
structure StrictPositiveNonpositiveCovector
    (vector : Generator → Coordinate → ℝ) where
  weight : Coordinate → ℝ
  positive : ∀ coordinate, 0 < weight coordinate
  generator_nonpositive : ∀ generator,
    dotProduct (vector generator) weight ≤ 0

/-- A nonnegative generator combination with a nonzero coordinatewise
nonnegative value and conic Caratheodory support bound. -/
structure SparseNonnegativeConeImprovement
    (vector : Generator → Coordinate → ℝ) where
  coefficient : Generator → ℝ
  coefficient_nonnegative : ∀ generator, 0 ≤ coefficient generator
  value_nonnegative : ∀ coordinate,
    0 ≤ ∑ generator,
      coefficient generator * vector generator coordinate
  value_positive : ∃ coordinate,
    0 < ∑ generator,
      coefficient generator * vector generator coordinate
  support_card_le :
    Fintype.card {generator // coefficient generator ≠ 0} ≤
      Fintype.card Coordinate

/-- A probability-normalized sparse cone improvement. -/
structure SparseProbabilityConeImprovement
    (vector : Generator → Coordinate → ℝ) where
  weight : Generator → ℝ
  weight_nonnegative : ∀ generator, 0 ≤ weight generator
  weight_sum_eq_one : ∑ generator, weight generator = 1
  value_nonnegative : ∀ coordinate,
    0 ≤ ∑ generator, weight generator * vector generator coordinate
  value_positive : ∃ coordinate,
    0 < ∑ generator, weight generator * vector generator coordinate
  support_card_le :
    Fintype.card {generator // weight generator ≠ 0} ≤
      Fintype.card Coordinate

namespace SparseNonnegativeConeImprovement

/-- Normalize the nonzero generator mass without changing support or signs. -/
def normalized
    {vector : Generator → Coordinate → ℝ}
    (improvement : SparseNonnegativeConeImprovement vector) :
    SparseProbabilityConeImprovement vector := by
  classical
  let total := ∑ generator, improvement.coefficient generator
  have hsome : ∃ generator, 0 < improvement.coefficient generator := by
    obtain ⟨coordinate, hcoordinate⟩ := improvement.value_positive
    by_contra hnone
    push Not at hnone
    have hzero : ∀ generator, improvement.coefficient generator = 0 := by
      intro generator
      exact le_antisymm (hnone generator)
        (improvement.coefficient_nonnegative generator)
    simp only [hzero, zero_mul, Finset.sum_const_zero] at hcoordinate
    exact (lt_irrefl 0) hcoordinate
  have htotalPositive : 0 < total := by
    obtain ⟨generator, hgenerator⟩ := hsome
    exact Finset.sum_pos' (fun current _ ↦
      improvement.coefficient_nonnegative current)
      ⟨generator, Finset.mem_univ generator, hgenerator⟩
  let weight : Generator → ℝ := fun generator ↦
    improvement.coefficient generator / total
  refine {
    weight := weight
    weight_nonnegative := fun generator ↦
      div_nonneg (improvement.coefficient_nonnegative generator)
        htotalPositive.le
    weight_sum_eq_one := by
      dsimp only [weight]
      rw [← Finset.sum_div, div_self htotalPositive.ne']
    value_nonnegative := ?_
    value_positive := ?_
    support_card_le := ?_ }
  · intro coordinate
    dsimp only [weight]
    simp only [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    exact div_nonneg (improvement.value_nonnegative coordinate)
      htotalPositive.le
  · obtain ⟨coordinate, hcoordinate⟩ := improvement.value_positive
    refine ⟨coordinate, ?_⟩
    dsimp only [weight]
    simp only [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    exact div_pos hcoordinate htotalPositive
  · let supportEquiv :
        {generator // weight generator ≠ 0} ≃
          {generator // improvement.coefficient generator ≠ 0} :=
      Equiv.subtypeEquivRight fun generator ↦ by
        dsimp only [weight]
        rw [div_ne_zero_iff]
        exact and_iff_left htotalPositive.ne'
    rw [Fintype.card_congr supportEquiv]
    exact improvement.support_card_le

end SparseNonnegativeConeImprovement

/-- The two cone objects cannot coexist. -/
theorem StrictPositiveNonpositiveCovector.not_sparseNonnegativeConeImprovement
    {vector : Generator → Coordinate → ℝ}
    (separator : StrictPositiveNonpositiveCovector vector) :
    ¬Nonempty (SparseNonnegativeConeImprovement vector) := by
  rintro ⟨improvement⟩
  obtain ⟨coordinate, hcoordinate⟩ := improvement.value_positive
  have hweightedPositive : 0 <
      ∑ current, separator.weight current *
        (∑ generator, improvement.coefficient generator *
          vector generator current) := by
    apply Finset.sum_pos'
    · intro current _
      exact mul_nonneg (separator.positive current).le
        (improvement.value_nonnegative current)
    · exact ⟨coordinate, Finset.mem_univ coordinate,
        mul_pos (separator.positive coordinate) hcoordinate⟩
  have hweightedNonpositive :
      (∑ current, separator.weight current *
        (∑ generator, improvement.coefficient generator *
          vector generator current)) ≤ 0 := by
    calc
      _ = ∑ generator, improvement.coefficient generator *
          dotProduct (vector generator) separator.weight := by
        simp only [dotProduct, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro generator _
        apply Finset.sum_congr rfl
        intro current _
        ring
      _ ≤ 0 := by
        exact Finset.sum_nonpos fun generator _ ↦
          mul_nonpos_of_nonneg_of_nonpos
            (improvement.coefficient_nonnegative generator)
            (separator.generator_nonpositive generator)
  exact (not_lt_of_ge hweightedNonpositive) hweightedPositive

/-- Exact sparse finite-cone alternative. -/
theorem xor_strictPositiveNonpositiveCovector_or_sparseNonnegativeConeImprovement
    (vector : Generator → Coordinate → ℝ) :
    Xor (Nonempty (StrictPositiveNonpositiveCovector vector))
      (Nonempty (SparseNonnegativeConeImprovement vector)) := by
  classical
  let rowVector : Sum Coordinate Generator → Coordinate → ℝ
    | .inl selected, current => if current = selected then 1 else 0
    | .inr generator, current => -vector generator current
  let rowFloor : Sum Coordinate Generator → ℝ
    | .inl _ => 1
    | .inr _ => 0
  rcases Math.exists_potential_or_nonnegative_incompatibility
      rowVector rowFloor with hseparator | hcombination
  · left
    obtain ⟨weight, hweight⟩ := hseparator
    refine ⟨⟨⟨weight, ?_, ?_⟩⟩, ?_⟩
    · intro coordinate
      have hcoordinate := hweight (Sum.inl coordinate)
      simp only [rowFloor, rowVector, dotProduct] at hcoordinate
      simpa using lt_of_lt_of_le zero_lt_one hcoordinate
    · intro generator
      have hgenerator := hweight (Sum.inr generator)
      simp only [rowFloor, rowVector, dotProduct] at hgenerator
      have : 0 ≤ -dotProduct (vector generator) weight := by
        simpa [dotProduct, Finset.sum_neg_distrib] using hgenerator
      linarith
    · rintro ⟨improvement⟩
      exact
        StrictPositiveNonpositiveCovector.not_sparseNonnegativeConeImprovement
          ⟨weight, fun coordinate ↦ by
            have hcoordinate := hweight (Sum.inl coordinate)
            simp only [rowFloor, rowVector, dotProduct] at hcoordinate
            simpa using lt_of_lt_of_le zero_lt_one hcoordinate,
          fun generator ↦ by
            have hgenerator := hweight (Sum.inr generator)
            simp only [rowFloor, rowVector, dotProduct] at hgenerator
            have : 0 ≤ -dotProduct (vector generator) weight := by
              simpa [dotProduct, Finset.sum_neg_distrib] using hgenerator
            linarith⟩ ⟨improvement⟩
  · right
    obtain ⟨coefficient, hnonnegative, hbalance, hpositive⟩ :=
      hcombination
    let initial : Generator → ℝ := fun generator ↦
      coefficient (Sum.inr generator)
    let value : Coordinate → ℝ := fun coordinate ↦
      coefficient (Sum.inl coordinate)
    have hinitialNonnegative : ∀ generator, 0 ≤ initial generator :=
      fun generator ↦ hnonnegative (Sum.inr generator)
    have hvalueNonnegative : ∀ coordinate, 0 ≤ value coordinate :=
      fun coordinate ↦ hnonnegative (Sum.inl coordinate)
    have hreconstruct : ∀ coordinate,
        ∑ generator, initial generator * vector generator coordinate =
          value coordinate := by
      intro coordinate
      have hcoordinate := hbalance coordinate
      simp only [Fintype.sum_sum_type, rowVector] at hcoordinate
      dsimp only [initial, value]
      have hleft :
          (∑ selected, coefficient (Sum.inl selected) *
            (if coordinate = selected then 1 else 0)) =
            coefficient (Sum.inl coordinate) := by
        classical
        simp
      rw [hleft] at hcoordinate
      simp only [mul_neg, Finset.sum_neg_distrib] at hcoordinate
      linarith
    have hvaluePositive : ∃ coordinate, 0 < value coordinate := by
      have hpositive' : 0 < ∑ coordinate, value coordinate := by
        simpa only [rowFloor, Fintype.sum_sum_type, mul_one, mul_zero,
          Finset.sum_const_zero, add_zero, value] using hpositive
      by_contra hnone
      push Not at hnone
      have hnonpositive : ∑ coordinate, value coordinate ≤ 0 :=
        Finset.sum_nonpos fun coordinate _ ↦ hnone coordinate
      exact (not_lt_of_ge hnonpositive) hpositive'
    obtain ⟨sparse, hsparseNonnegative, hsparseValue, hsparseCard⟩ :=
      exists_nonnegative_finiteCombination_eq_support_card_le
        vector value initial hinitialNonnegative hreconstruct
    have hsparseImprovement : SparseNonnegativeConeImprovement vector := {
      coefficient := sparse
      coefficient_nonnegative := hsparseNonnegative
      value_nonnegative := fun coordinate ↦ by
        rw [hsparseValue coordinate]
        exact hvalueNonnegative coordinate
      value_positive := by
        obtain ⟨coordinate, hcoordinate⟩ := hvaluePositive
        exact ⟨coordinate, by rw [hsparseValue coordinate]; exact hcoordinate⟩
      support_card_le := hsparseCard }
    refine ⟨⟨hsparseImprovement⟩, ?_⟩
    rintro ⟨separator⟩
    exact separator.not_sparseNonnegativeConeImprovement
      ⟨hsparseImprovement⟩

end LinearAlgebra
end Math

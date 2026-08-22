/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cubical reset integrability

Any scalar observable indexed by finite coordinate sets is a potential on a
Boolean reset cube. This file records its exact path and curvature telescopes.

For an ordered reset word, the discrepancy between the actual path increment
and the sum of all reset increments measured at the common source is exactly
a sum of two-reset square curvatures at successive background prefixes.
Thus a positive high-cardinality superadditivity gap cannot be intrinsically
high-order: one two-direction square at a (possibly large) background prefix
must carry positive curvature.

This is pure cubical algebra. An application must separately give the square
directions their intended meaning and control the background prefix.
-/

noncomputable section

namespace Math.Finset
namespace CubicalResetIntegrability

variable {Coordinate : Type*} [DecidableEq Coordinate]

/-- The endpoint reset set obtained by executing a word from `source`. -/
def finalSet (source : Finset Coordinate) : List Coordinate → Finset Coordinate
  | [] => source
  | coordinate :: rest => finalSet (insert coordinate source) rest

/-- One directed coordinate increment of a scalar cube observable. -/
def edge (value : Finset Coordinate → ℝ)
    (source : Finset Coordinate) (coordinate : Coordinate) : ℝ :=
  value (insert coordinate source) - value source

/-- The mixed discrete derivative on one square face. -/
def square (value : Finset Coordinate → ℝ)
    (source : Finset Coordinate) (first second : Coordinate) : ℝ :=
  edge value (insert first source) second - edge value source second

/-- Accumulated change of one fixed coordinate edge while a word of other
coordinates is inserted. -/
def edgeCurvatureSum (value : Finset Coordinate → ℝ) :
    Finset Coordinate → List Coordinate → Coordinate → ℝ
  | _source, [], _coordinate => 0
  | source, first :: rest, coordinate =>
      square value source first coordinate +
        edgeCurvatureSum value (insert first source) rest coordinate

/-- A square with large absolute curvature encountered while transporting one
fixed coordinate edge across a reset word. -/
def HasAbsSquareAboveOnEdge (value : Finset Coordinate → ℝ)
    (threshold : ℝ) : Finset Coordinate → List Coordinate → Coordinate → Prop
  | _source, [], _coordinate => False
  | source, first :: rest, coordinate =>
      threshold < |square value source first coordinate| ∨
        HasAbsSquareAboveOnEdge value threshold
          (insert first source) rest coordinate

/-- Sum of the literal consecutive edge increments along a reset word. -/
def pathEdgeSum (value : Finset Coordinate → ℝ) :
    Finset Coordinate → List Coordinate → ℝ
  | _source, [] => 0
  | source, coordinate :: rest =>
      edge value source coordinate +
        pathEdgeSum value (insert coordinate source) rest

/-- Sum of the same coordinate increments, all frozen at the initial source. -/
def frozenEdgeSum (value : Finset Coordinate → ℝ)
    (source : Finset Coordinate) (word : List Coordinate) : ℝ :=
  (word.map (edge value source)).sum

/-- The triangular sum of square curvatures generated when the reset word is
compared with its common-source star. -/
def squareCurvatureSum (value : Finset Coordinate → ℝ) :
    Finset Coordinate → List Coordinate → ℝ
  | _source, [] => 0
  | source, coordinate :: rest =>
      squareCurvatureSum value (insert coordinate source) rest +
        (rest.map (square value source coordinate)).sum

/-- A positive two-reset square appearing in the triangular decomposition of
one ordered reset word. -/
def HasPositiveSquareAlong (value : Finset Coordinate → ℝ) :
    Finset Coordinate → List Coordinate → Prop
  | _source, [] => False
  | source, coordinate :: rest =>
      HasPositiveSquareAlong value (insert coordinate source) rest ∨
        ∃ other ∈ rest, 0 < square value source coordinate other

/-- Literal consecutive reset increments telescope to the endpoint
difference. -/
theorem pathEdgeSum_eq_endpoint_sub
    (value : Finset Coordinate → ℝ)
    (source : Finset Coordinate) (word : List Coordinate) :
    pathEdgeSum value source word = value (finalSet source word) - value source := by
  induction word generalizing source with
  | nil => simp [pathEdgeSum, finalSet]
  | cons coordinate rest ih =>
      rw [pathEdgeSum, finalSet, ih]
      unfold edge
      ring

/-- Exact fixed-edge curvature telescope. -/
theorem edge_finalSet_sub_edge_eq_edgeCurvatureSum
    (value : Finset Coordinate → ℝ)
    (source : Finset Coordinate) (word : List Coordinate)
    (coordinate : Coordinate) :
    edge value (finalSet source word) coordinate -
        edge value source coordinate =
      edgeCurvatureSum value source word coordinate := by
  induction word generalizing source with
  | nil => simp [finalSet, edgeCurvatureSum]
  | cons first rest ih =>
      rw [finalSet, edgeCurvatureSum]
      rw [← ih (insert first source)]
      unfold square
      ring

/-- Quantitative fixed-edge transport: either the edge changes by at most one
threshold per inserted coordinate, or one crossed square has larger absolute
curvature. -/
theorem abs_edge_finalSet_sub_edge_le_or_hasAbsSquareAboveOnEdge
    (value : Finset Coordinate → ℝ)
    (source : Finset Coordinate) (word : List Coordinate)
    (coordinate : Coordinate) (threshold : ℝ) :
    |edge value (finalSet source word) coordinate -
        edge value source coordinate| ≤
          (word.length : ℝ) * threshold ∨
      HasAbsSquareAboveOnEdge value threshold source word coordinate := by
  rw [edge_finalSet_sub_edge_eq_edgeCurvatureSum]
  induction word generalizing source with
  | nil => simp [edgeCurvatureSum]
  | cons first rest ih =>
      rw [edgeCurvatureSum]
      rcases ih (insert first source) with hrest | hlarge
      · by_cases hfirst : |square value source first coordinate| ≤ threshold
        · left
          calc
            |square value source first coordinate +
                edgeCurvatureSum value (insert first source) rest coordinate| ≤
                |square value source first coordinate| +
                  |edgeCurvatureSum value (insert first source) rest coordinate| :=
              abs_add_le _ _
            _ ≤ threshold + (rest.length : ℝ) * threshold :=
              add_le_add hfirst hrest
            _ = ((first :: rest).length : ℝ) * threshold := by
              simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
              ring
        · right
          exact Or.inl (lt_of_not_ge hfirst)
      · right
        exact Or.inr hlarge

/-- Moving the base of every frozen edge across one coordinate produces the
sum of the corresponding square curvatures. -/
theorem frozenEdgeSum_insert_sub
    (value : Finset Coordinate → ℝ)
    (source : Finset Coordinate) (coordinate : Coordinate)
    (word : List Coordinate) :
    frozenEdgeSum value (insert coordinate source) word -
        frozenEdgeSum value source word =
      (word.map (square value source coordinate)).sum := by
  induction word with
  | nil => simp [frozenEdgeSum]
  | cons other rest ih =>
      change
        (edge value (insert coordinate source) other +
              frozenEdgeSum value (insert coordinate source) rest) -
            (edge value source other + frozenEdgeSum value source rest) =
          square value source coordinate other +
            (rest.map (square value source coordinate)).sum
      rw [show square value source coordinate other =
          edge value (insert coordinate source) other -
            edge value source other from rfl, ← ih]
      ring

/-- **Exact cubical curvature identity.**  The failure of the common-source
star to equal one actual reset path is precisely the triangular sum of
two-reset square curvatures at successive reached prefixes. -/
theorem path_sub_frozen_eq_squareCurvatureSum
    (value : Finset Coordinate → ℝ)
    (source : Finset Coordinate) (word : List Coordinate) :
    pathEdgeSum value source word - frozenEdgeSum value source word =
      squareCurvatureSum value source word := by
  induction word generalizing source with
  | nil => simp [pathEdgeSum, frozenEdgeSum, squareCurvatureSum]
  | cons coordinate rest ih =>
      change
        (edge value source coordinate +
              pathEdgeSum value (insert coordinate source) rest) -
            (edge value source coordinate + frozenEdgeSum value source rest) =
          squareCurvatureSum value (insert coordinate source) rest +
            (rest.map (square value source coordinate)).sum
      calc
        (edge value source coordinate +
                pathEdgeSum value (insert coordinate source) rest) -
              (edge value source coordinate + frozenEdgeSum value source rest) =
            (pathEdgeSum value (insert coordinate source) rest -
                frozenEdgeSum value (insert coordinate source) rest) +
              (frozenEdgeSum value (insert coordinate source) rest -
                frozenEdgeSum value source rest) := by ring
        _ = squareCurvatureSum value (insert coordinate source) rest +
              (rest.map (square value source coordinate)).sum := by
          rw [ih (insert coordinate source),
            frozenEdgeSum_insert_sub value source coordinate rest]

/-- Endpoint form of the same identity. -/
theorem endpoint_sub_source_sub_frozen_eq_squareCurvatureSum
    (value : Finset Coordinate → ℝ)
    (source : Finset Coordinate) (word : List Coordinate) :
    value (finalSet source word) - value source -
        frozenEdgeSum value source word =
      squareCurvatureSum value source word := by
  rw [← pathEdgeSum_eq_endpoint_sub]
  exact path_sub_frozen_eq_squareCurvatureSum value source word

/-- If every square contribution in the triangular decomposition is
nonpositive, the simultaneous endpoint increment is no larger than the sum
of common-source increments.  Its contrapositive localizes every positive
superadditivity gap to a positive square contribution. -/
theorem endpoint_sub_source_le_frozen_of_squareCurvatureSum_nonpos
    (value : Finset Coordinate → ℝ)
    (source : Finset Coordinate) (word : List Coordinate)
    (hcurvature : squareCurvatureSum value source word ≤ 0) :
    value (finalSet source word) - value source ≤
      frozenEdgeSum value source word := by
  have hidentity :=
    endpoint_sub_source_sub_frozen_eq_squareCurvatureSum value source word
  linarith

private theorem exists_mem_pos_of_list_sum_pos (values : List ℝ)
    (hsum : 0 < values.sum) :
    ∃ value ∈ values, 0 < value := by
  induction values with
  | nil => simp at hsum
  | cons value values ih =>
      by_cases hvalue : 0 < value
      · exact ⟨value, by simp, hvalue⟩
      · have htail : 0 < values.sum := by
          simp only [List.sum_cons] at hsum
          linarith
        obtain ⟨positive, hpositiveMem, hpositive⟩ := ih htail
        exact ⟨positive, by simp [hpositiveMem], hpositive⟩

/-- **Positive-gap localization.**  Every positive common-source versus path
gap contains a positive two-reset square at one literal reached prefix.  The
background prefix can be large; the two nonlinear reset directions cannot. -/
theorem hasPositiveSquareAlong_of_squareCurvatureSum_pos
    (value : Finset Coordinate → ℝ)
    (source : Finset Coordinate) (word : List Coordinate)
    (hpositive : 0 < squareCurvatureSum value source word) :
    HasPositiveSquareAlong value source word := by
  induction word generalizing source with
  | nil => simp [squareCurvatureSum] at hpositive
  | cons coordinate rest ih =>
      simp only [squareCurvatureSum] at hpositive
      by_cases htail :
          0 < squareCurvatureSum value (insert coordinate source) rest
      · exact Or.inl (ih (insert coordinate source) htail)
      · have hsquares :
            0 < (rest.map (square value source coordinate)).sum := by
          linarith
        obtain ⟨positive, hpositiveMem, hpositiveValue⟩ :=
          exists_mem_pos_of_list_sum_pos
            (rest.map (square value source coordinate)) hsquares
        obtain ⟨other, hotherMem, rfl⟩ := List.mem_map.mp hpositiveMem
        exact Or.inr ⟨other, hotherMem, hpositiveValue⟩

/-- Endpoint formulation of positive square localization. -/
theorem hasPositiveSquareAlong_of_frozen_lt_endpoint_sub_source
    (value : Finset Coordinate → ℝ)
    (source : Finset Coordinate) (word : List Coordinate)
    (hpositive : frozenEdgeSum value source word <
      value (finalSet source word) - value source) :
    HasPositiveSquareAlong value source word := by
  apply hasPositiveSquareAlong_of_squareCurvatureSum_pos value source word
  rw [← endpoint_sub_source_sub_frozen_eq_squareCurvatureSum]
  linarith

/-! ## Quantitative signed localization -/

/-- Number of square contributions in the triangular decomposition of a
reset word. Repeated coordinates are counted as distinct positions. -/
def squareCount : List Coordinate → ℕ
  | [] => 0
  | _coordinate :: rest => squareCount rest + rest.length

/-- A two-reset square in the triangular decomposition whose curvature is
strictly larger than the displayed threshold. -/
def HasSquareAboveAlong (value : Finset Coordinate → ℝ) (threshold : ℝ) :
    Finset Coordinate → List Coordinate → Prop
  | _source, [] => False
  | source, coordinate :: rest =>
      HasSquareAboveAlong value threshold (insert coordinate source) rest ∨
        ∃ other ∈ rest, threshold < square value source coordinate other

private theorem exists_mem_gt_of_length_mul_lt_sum
    (values : List ℝ) (threshold : ℝ)
    (hlarge : (values.length : ℝ) * threshold < values.sum) :
    ∃ value ∈ values, threshold < value := by
  induction values with
  | nil => simp at hlarge
  | cons value values ih =>
      by_cases hvalue : threshold < value
      · exact ⟨value, by simp, hvalue⟩
      · have hvalueLe : value ≤ threshold := le_of_not_gt hvalue
        have htail : (values.length : ℝ) * threshold < values.sum := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one,
            List.sum_cons] at hlarge
          linarith
        obtain ⟨large, hlargeMem, hlargeValue⟩ := ih htail
        exact ⟨large, by simp [hlargeMem], hlargeValue⟩

/-- If the aggregate triangular curvature exceeds `squareCount * threshold`,
one literal square contribution exceeds `threshold`. -/
theorem hasSquareAboveAlong_of_mul_lt_squareCurvatureSum
    (value : Finset Coordinate → ℝ)
    (source : Finset Coordinate) (word : List Coordinate)
    (threshold : ℝ)
    (hlarge : (squareCount word : ℝ) * threshold <
      squareCurvatureSum value source word) :
    HasSquareAboveAlong value threshold source word := by
  induction word generalizing source with
  | nil => simp [squareCount, squareCurvatureSum] at hlarge
  | cons coordinate rest ih =>
      simp only [squareCount, squareCurvatureSum, Nat.cast_add] at hlarge
      by_cases htail : (squareCount rest : ℝ) * threshold <
          squareCurvatureSum value (insert coordinate source) rest
      · exact Or.inl (ih (insert coordinate source) htail)
      · have htailLe :
            squareCurvatureSum value (insert coordinate source) rest ≤
              (squareCount rest : ℝ) * threshold := le_of_not_gt htail
        have hsquares : (rest.length : ℝ) * threshold <
            (rest.map (square value source coordinate)).sum := by
          linarith
        obtain ⟨large, hlargeMem, hlargeValue⟩ :=
          exists_mem_gt_of_length_mul_lt_sum
            (rest.map (square value source coordinate)) threshold (by
              simpa using hsquares)
        obtain ⟨other, hotherMem, rfl⟩ := List.mem_map.mp hlargeMem
        exact Or.inr ⟨other, hotherMem, hlargeValue⟩

private theorem sum_map_neg_of
    {α : Type*} (first second : α → ℝ) (values : List α)
    (heq : ∀ value, first value = -second value) :
    (values.map first).sum = -(values.map second).sum := by
  induction values with
  | nil => simp
  | cons value values ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [heq value, ih]
      ring

/-- Negating an observable negates every triangular curvature sum. -/
theorem squareCurvatureSum_neg
    (value : Finset Coordinate → ℝ)
    (source : Finset Coordinate) (word : List Coordinate) :
    squareCurvatureSum (fun reset ↦ -value reset) source word =
      -squareCurvatureSum value source word := by
  induction word generalizing source with
  | nil => simp [squareCurvatureSum]
  | cons coordinate rest ih =>
      simp only [squareCurvatureSum, ih]
      have hsquare : ∀ other,
          square (fun reset ↦ -value reset) source coordinate other =
            -square value source coordinate other := by
        intro other
        simp [square, edge]
        ring
      have hsquares := sum_map_neg_of
        (square (fun reset ↦ -value reset) source coordinate)
        (square value source coordinate) rest hsquare
      rw [hsquares]
      ring

/-- **Quantitative signed curvature dichotomy.** Either the complete
common-source/path discrepancy is at most `squareCount * threshold`, or one
literal two-reset square exceeds `threshold` in one of the two orientations.
The second orientation is represented by negating the observable. -/
theorem abs_squareCurvatureSum_le_or_signedSquareAbove
    (value : Finset Coordinate → ℝ)
    (source : Finset Coordinate) (word : List Coordinate)
    (threshold : ℝ) (hthreshold : 0 ≤ threshold) :
    |squareCurvatureSum value source word| ≤
          (squareCount word : ℝ) * threshold ∨
      HasSquareAboveAlong value threshold source word ∨
        HasSquareAboveAlong (fun reset ↦ -value reset) threshold source word := by
  let bound : ℝ := (squareCount word : ℝ) * threshold
  have hbound : 0 ≤ bound := mul_nonneg (Nat.cast_nonneg _) hthreshold
  by_cases hnear : |squareCurvatureSum value source word| ≤ bound
  · exact Or.inl hnear
  · have hfar : bound < |squareCurvatureSum value source word| :=
      lt_of_not_ge hnear
    by_cases hcurvature : 0 ≤ squareCurvatureSum value source word
    · right
      left
      apply hasSquareAboveAlong_of_mul_lt_squareCurvatureSum
      simpa only [bound, abs_of_nonneg hcurvature] using hfar
    · right
      right
      apply hasSquareAboveAlong_of_mul_lt_squareCurvatureSum
      rw [squareCurvatureSum_neg]
      have hnegative : squareCurvatureSum value source word < 0 :=
        lt_of_not_ge hcurvature
      simpa only [bound, abs_of_neg hnegative] using hfar

/-- Endpoint form of the quantitative signed curvature dichotomy. -/
theorem nearFrozenReturn_or_signedSquareAbove
    (value : Finset Coordinate → ℝ)
    (source : Finset Coordinate) (word : List Coordinate)
    (threshold : ℝ) (hthreshold : 0 ≤ threshold) :
    |value (finalSet source word) - value source -
        frozenEdgeSum value source word| ≤
          (squareCount word : ℝ) * threshold ∨
      HasSquareAboveAlong value threshold source word ∨
        HasSquareAboveAlong (fun reset ↦ -value reset) threshold source word := by
  rw [endpoint_sub_source_sub_frozen_eq_squareCurvatureSum]
  exact abs_squareCurvatureSum_le_or_signedSquareAbove
    value source word threshold hthreshold

end CubicalResetIntegrability
end Math.Finset

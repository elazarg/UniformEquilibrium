/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib

/-!
# Cubical reset integrability

Fixed coordinate replacements commute.  Therefore any scalar observable of
the resulting profiles is a potential on a Boolean reset cube.  This file
records the exact telescopes needed by the quitting-game reset program.

For an ordered reset word, the discrepancy between the actual path increment
and the sum of all reset increments measured at the common source is exactly
a sum of two-reset square curvatures at successive background prefixes.
Thus a positive high-cardinality superadditivity gap cannot be intrinsically
high-order: one two-direction square at a (possibly large) background prefix
must carry positive curvature.

This is pure cubical algebra.  A quitting-game consumer must still show that
the two square directions have strategic sign and compress the background
prefix to a fixed-table host without losing deviation geometry.
-/

noncomputable section

namespace Experiments
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

end CubicalResetIntegrability
end Experiments

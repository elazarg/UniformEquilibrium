/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Finset.CubicalResetIntegrability

/-!
# Fresh-square extraction from cubical localization

The recursive `HasSquareAboveAlong` predicate retains a literal square but does
not itself expose its coordinates.  For a duplicate-free reset word disjoint
from its starting face, this file extracts the square together with the
freshness and distinctness facts needed by game-semantic consumers.
-/

noncomputable section

namespace Math.Finset
namespace CubicalResetIntegrability

variable {Coordinate : Type*} [DecidableEq Coordinate]

/-- A square localized along a duplicate-free word has two fresh, distinct
coordinates at one reached background face. -/
theorem exists_fresh_square_of_hasSquareAboveAlong
    (value : Finset Coordinate → ℝ) (threshold : ℝ)
    (source : Finset Coordinate) (word : List Coordinate)
    (hnodup : word.Nodup) (hdisjoint : Disjoint word.toFinset source)
    (hlarge : HasSquareAboveAlong value threshold source word) :
    ∃ background first second,
      first ∉ background ∧ second ∉ background ∧ first ≠ second ∧
        threshold < square value background first second := by
  induction word generalizing source with
  | nil =>
      simp [HasSquareAboveAlong] at hlarge
  | cons coordinate rest ih =>
      have hnodupParts := List.nodup_cons.mp hnodup
      have hcoordinateNotSource : coordinate ∉ source := by
        intro hsource
        exact Finset.disjoint_left.mp hdisjoint (by simp) hsource
      have hrestDisjoint : Disjoint rest.toFinset (insert coordinate source) := by
        rw [Finset.disjoint_left]
        intro other hotherRest hotherInsert
        simp only [List.toFinset_cons, Finset.disjoint_insert_left] at hdisjoint
        rcases Finset.mem_insert.mp hotherInsert with rfl | hotherSource
        · exact hnodupParts.1 (by simpa using hotherRest)
        · exact Finset.disjoint_left.mp hdisjoint.2 hotherRest hotherSource
      simp only [HasSquareAboveAlong] at hlarge
      rcases hlarge with hrest | ⟨other, hotherRest, hpositive⟩
      · exact ih (insert coordinate source) hnodupParts.2 hrestDisjoint hrest
      · have hotherNotSource : other ∉ source := by
          intro hotherSource
          exact Finset.disjoint_left.mp hdisjoint
            (by simp [hotherRest]) hotherSource
        have hne : coordinate ≠ other := by
          intro heq
          subst other
          exact hnodupParts.1 hotherRest
        exact ⟨source, coordinate, other, hcoordinateNotSource,
          hotherNotSource, hne, hpositive⟩

end CubicalResetIntegrability
end Math.Finset

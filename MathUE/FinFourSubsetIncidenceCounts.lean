import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Powerset

/-! # Exact incidence counts among subsets of Fin4 -/

namespace Math

open scoped BigOperators

def finFourNonemptySubsets : Finset (Finset (Fin 4)) :=
  (Finset.univ : Finset (Fin 4)).powerset.erase ∅

/-- There are fifteen nonempty subsets of a four-element type. -/
theorem finFour_nonemptySubset_count : finFourNonemptySubsets.card = 15 := by
  decide

/-- The total number of incidences between a nonempty Fin4 subset and one
of its elements is 32. -/
theorem finFour_nonemptySubset_totalCardinality :
    (∑ subset ∈ finFourNonemptySubsets, subset.card) = 32 := by
  decide

/-- The total number of pairs of nonempty Fin4 subsets with the first
contained in the second is 65. -/
theorem finFour_nonemptySubset_totalNonemptySubsets :
    (∑ subset ∈ finFourNonemptySubsets, (2 ^ subset.card - 1)) = 65 := by
  decide

/-- Of those contained-subset pairs, 33 have a nonsingleton first subset. -/
theorem finFour_nonemptySubset_totalNonsingletonSubsets :
    (∑ subset ∈ finFourNonemptySubsets,
      ((2 ^ subset.card - 1) - subset.card)) = 33 := by
  decide

end Math

/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max

/-!
# A member small enough to be dominated by a sum

A nonempty finite index set always carries a member whose multiple by the
cardinality is at most the whole sum: take a member of least value
(`Math.Finset.exists_card_nsmul_le_sum`).

Running the same choice over a finite family of index sets of one common size
gives a single member whose multiple by that common size is at most *every*
one of the sums (`Math.Finset.exists_nsmul_le_forall_sum`): pick a set of
least sum, then a least member inside it.  Equal size is what makes the two
choices compose; without it the conclusion fails already for two singletons.
-/

namespace Math.Finset

/-- **A least member is dominated by the averaged sum.**  Some member of a
nonempty finite index set has its multiple by the cardinality at most the
sum. -/
theorem exists_card_nsmul_le_sum {Index Value : Type*} [AddCommMonoid Value]
    [LinearOrder Value] [AddLeftMono Value] {indices : Finset Index}
    (hindices : indices.Nonempty) (weight : Index → Value) :
    ∃ index ∈ indices,
      indices.card • weight index ≤ ∑ other ∈ indices, weight other := by
  obtain ⟨index, hindex, hmin⟩ := indices.exists_min_image weight hindices
  exact ⟨index, hindex,
    Finset.card_nsmul_le_sum indices weight (weight index) hmin⟩

/-- **One member under every equal-sized sum.**  Given a nonempty finite
family of nonempty index sets of one common size `size`, some index has its
`size`-fold multiple at most every one of the family's sums. -/
theorem exists_nsmul_le_forall_sum {Index Part Value : Type*}
    [AddCommMonoid Value] [LinearOrder Value] [AddLeftMono Value] [Fintype Part]
    [Nonempty Part] {size : ℕ} {parts : Part → Finset Index}
    (hparts : ∀ part, (parts part).Nonempty)
    (hsize : ∀ part, (parts part).card = size) (weight : Index → Value) :
    ∃ index : Index,
      ∀ part, size • weight index ≤ ∑ other ∈ parts part, weight other := by
  obtain ⟨least, -, hleast⟩ := Finset.exists_min_image Finset.univ
    (fun part ↦ ∑ other ∈ parts part, weight other) Finset.univ_nonempty
  obtain ⟨index, -, hindex⟩ := exists_card_nsmul_le_sum (hparts least) weight
  refine ⟨index, fun part ↦ ?_⟩
  rw [← hsize least]
  exact hindex.trans (hleast part (Finset.mem_univ part))

end Math.Finset

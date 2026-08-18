/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Order.Basic

/-!
# The extremum of a finite family clamped at a base value

`Math.Finset.insertMax base indices weight` is the greatest of the base value
`base` and the values of `weight` on `indices`, and `Math.Finset.insertMin` is
its order dual.  Both are total on a `LinearOrder`, including at
`indices = ∅`, where they return `base`; this is what makes them usable as a
clamped cap or a clamped floor without a nonemptiness side condition.

Each carries the three facts that characterize it:

* the base value is on the correct side of the extremum;
* every value of `weight` on `indices` is on the correct side; and
* the extremum is the tightest such bound.

The characterization is stated as a one-directional bound in each direction
rather than as a `Nat.find`-style specification, because the two directions
are used separately.
-/

namespace Math.Finset

variable {Index : Type*} {Value : Type*} [LinearOrder Value]

/-- The greatest of `base` and the values of `weight` on `indices`. -/
def insertMax (base : Value) (indices : Finset Index) (weight : Index → Value) :
    Value :=
  (insert base (indices.image weight)).max' (Finset.insert_nonempty _ _)

/-- The least of `base` and the values of `weight` on `indices`. -/
def insertMin (base : Value) (indices : Finset Index) (weight : Index → Value) :
    Value :=
  (insert base (indices.image weight)).min' (Finset.insert_nonempty _ _)

theorem base_le_insertMax (base : Value) (indices : Finset Index)
    (weight : Index → Value) : base ≤ insertMax base indices weight :=
  Finset.le_max' _ _ (Finset.mem_insert_self _ _)

theorem insertMin_le_base (base : Value) (indices : Finset Index)
    (weight : Index → Value) : insertMin base indices weight ≤ base :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem le_insertMax (base : Value) {indices : Finset Index}
    (weight : Index → Value) {index : Index} (hindex : index ∈ indices) :
    weight index ≤ insertMax base indices weight :=
  Finset.le_max' _ _
    (Finset.mem_insert_of_mem (Finset.mem_image_of_mem weight hindex))

theorem insertMin_le (base : Value) {indices : Finset Index}
    (weight : Index → Value) {index : Index} (hindex : index ∈ indices) :
    insertMin base indices weight ≤ weight index :=
  Finset.min'_le _ _
    (Finset.mem_insert_of_mem (Finset.mem_image_of_mem weight hindex))

/-- `insertMax` is the least common upper bound of the base value and of the
values of `weight` on `indices`. -/
theorem insertMax_le {base bound : Value} {indices : Finset Index}
    {weight : Index → Value} (hbase : base ≤ bound)
    (hweight : ∀ index ∈ indices, weight index ≤ bound) :
    insertMax base indices weight ≤ bound := by
  refine Finset.max'_le _ _ _ fun entry hentry => ?_
  rcases Finset.mem_insert.mp hentry with rfl | hmem
  · exact hbase
  · obtain ⟨index, hindex, rfl⟩ := Finset.mem_image.mp hmem
    exact hweight index hindex

/-- `insertMin` is the greatest common lower bound of the base value and of
the values of `weight` on `indices`. -/
theorem le_insertMin {base bound : Value} {indices : Finset Index}
    {weight : Index → Value} (hbase : bound ≤ base)
    (hweight : ∀ index ∈ indices, bound ≤ weight index) :
    bound ≤ insertMin base indices weight := by
  refine Finset.le_min' _ _ _ fun entry hentry => ?_
  rcases Finset.mem_insert.mp hentry with rfl | hmem
  · exact hbase
  · obtain ⟨index, hindex, rfl⟩ := Finset.mem_image.mp hmem
    exact hweight index hindex

end Math.Finset

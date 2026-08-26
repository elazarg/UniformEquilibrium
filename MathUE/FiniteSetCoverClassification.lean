/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Finite set-cover classification

For a finite family of finite cells, the intersection of the nonempty cells
is empty exactly when every point is excluded by some nonempty cell.  When
the cells are indexed by their owners and every nonempty owner cell excludes
its owner, a point in the common intersection has an empty own cell and lies
in every other nonempty cell.
-/

namespace Math

variable {κ α : Type*} [Fintype κ] [Fintype α] [DecidableEq α]

/-- The intersection of the nonempty members of a finite family, with the
empty-family intersection equal to the whole finite universe. -/
def finiteNonemptyFamilyCore (cell : κ → Finset α) : Finset α :=
  Finset.univ.filter fun point =>
    ∀ index, cell index ≠ ∅ → point ∈ cell index

@[simp]
theorem mem_finiteNonemptyFamilyCore_iff
    (cell : κ → Finset α) (point : α) :
    point ∈ finiteNonemptyFamilyCore cell ↔
      ∀ index, cell index ≠ ∅ → point ∈ cell index := by
  simp [finiteNonemptyFamilyCore]

/-- The nonempty cells cover by complements exactly when their common core
is empty. -/
theorem finiteNonemptyFamilyCore_eq_empty_iff
    (cell : κ → Finset α) :
    finiteNonemptyFamilyCore cell = ∅ ↔
      ∀ point, ∃ index, cell index ≠ ∅ ∧ point ∉ cell index := by
  classical
  constructor
  · intro hcore point
    have hpoint : point ∉ finiteNonemptyFamilyCore cell := by
      simp [hcore]
    rw [mem_finiteNonemptyFamilyCore_iff] at hpoint
    push Not at hpoint
    obtain ⟨index, hnonempty, hexcluded⟩ := hpoint
    exact ⟨index, Finset.nonempty_iff_ne_empty.mp hnonempty, hexcluded⟩
  · intro hcover
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨point, hpoint⟩
    obtain ⟨index, hnonempty, hexcluded⟩ := hcover point
    exact hexcluded ((mem_finiteNonemptyFamilyCore_iff cell point).mp
      hpoint index hnonempty)

/-- A member of the common core belongs to every nonempty cell. -/
theorem mem_cell_of_mem_finiteNonemptyFamilyCore
    {cell : κ → Finset α} {point : α}
    (hpoint : point ∈ finiteNonemptyFamilyCore cell)
    {index : κ} (hcell : cell index ≠ ∅) :
    point ∈ cell index :=
  (mem_finiteNonemptyFamilyCore_iff cell point).mp hpoint index hcell

section OwnerCells

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If every nonempty owner cell excludes its owner, a common participant
has an empty own cell. -/
theorem own_cell_eq_empty_of_mem_finiteNonemptyFamilyCore
    {cell : ι → Finset ι}
    (hface : ∀ owner, cell owner ≠ ∅ → owner ∉ cell owner)
    {owner : ι} (howner : owner ∈ finiteNonemptyFamilyCore cell) :
    cell owner = ∅ := by
  by_contra hnonempty
  exact hface owner hnonempty
    (mem_cell_of_mem_finiteNonemptyFamilyCore howner hnonempty)

/-- Exact owner-cell alternative: either every owner is excluded by a
nonempty selected cell, or a common participant has an empty own cell and
belongs to every selected nonempty cell. -/
theorem finite_owner_cell_cover_or_common_participant
    (cell : ι → Finset ι)
    (hface : ∀ owner, cell owner ≠ ∅ → owner ∉ cell owner) :
    (∀ owner, ∃ index, cell index ≠ ∅ ∧ owner ∉ cell index) ∨
      ∃ owner, cell owner = ∅ ∧
        ∀ index, cell index ≠ ∅ → owner ∈ cell index := by
  classical
  by_cases hcore : finiteNonemptyFamilyCore cell = ∅
  · exact Or.inl ((finiteNonemptyFamilyCore_eq_empty_iff cell).mp hcore)
  · obtain ⟨owner, howner⟩ := Finset.nonempty_iff_ne_empty.mpr hcore
    refine Or.inr ⟨owner,
      own_cell_eq_empty_of_mem_finiteNonemptyFamilyCore hface howner, ?_⟩
    exact (mem_finiteNonemptyFamilyCore_iff cell owner).mp howner

end OwnerCells

end Math

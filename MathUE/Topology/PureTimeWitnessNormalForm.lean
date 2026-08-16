/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Option.Basic
import Mathlib.Order.Filter.AtTopBot.Finite

/-!
# A common subsequence normal form for optional natural-number witnesses

Along a sequence, an optional natural-number witness can switch between
finite values and `none`. After extraction it has only three possible forms:

* one fixed finite value;
* constant `none`;
* finite values tending to infinity.

The extraction can be done simultaneously for any finite family of witness
sequences.
-/

noncomputable section

namespace Math
namespace PureTimeWitnessNormalForm

open Filter Finset

/-- The three subsequential modes of an optional natural-number witness. -/
def HasNormalForm (q : ℕ → Option ℕ) : Prop :=
  (∃ t : ℕ, ∀ n, q n = some t) ∨
    (∀ n, q n = none) ∨
      ∃ t : ℕ → ℕ, Tendsto t atTop atTop ∧ ∀ n, q n = some (t n)

/-- A normal form remains normal after any reindexing that tends to infinity. -/
theorem HasNormalForm.comp_of_tendsto_atTop {q : ℕ → Option ℕ}
    (hq : HasNormalForm q) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    HasNormalForm (q ∘ φ) := by
  rcases hq with ⟨t, ht⟩ | hnone | ⟨t, ht, hqt⟩
  · exact Or.inl ⟨t, fun n ↦ ht (φ n)⟩
  · exact Or.inr (Or.inl fun n ↦ hnone (φ n))
  · exact Or.inr (Or.inr ⟨t ∘ φ, ht.comp hφ, fun n ↦ hqt (φ n)⟩)

/-- Every optional natural-number sequence has a strict subsequence in one
of the three normal modes. -/
theorem exists_strictMono_hasNormalForm (q : ℕ → Option ℕ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ HasNormalForm (q ∘ φ) := by
  by_cases hnone : ∃ᶠ n in atTop, q n = none
  · rcases extraction_of_frequently_atTop hnone with ⟨φ, hφ, hqφ⟩
    exact ⟨φ, hφ, Or.inr (Or.inl hqφ)⟩
  by_cases hfixed : ∃ t : ℕ, ∃ᶠ n in atTop, q n = some t
  · rcases hfixed with ⟨t, ht⟩
    rcases extraction_of_frequently_atTop ht with ⟨φ, hφ, hqφ⟩
    exact ⟨φ, hφ, Or.inl ⟨t, hqφ⟩⟩
  · have hsomeEventually : ∀ᶠ n in atTop, q n ≠ none := not_frequently.mp hnone
    rcases extraction_of_eventually_atTop hsomeEventually with ⟨φ, hφ, hqφ_ne⟩
    let hsome : ∀ n, (q (φ n)).isSome := fun n ↦
      Option.ne_none_iff_isSome.mp (hqφ_ne n)
    let t : ℕ → ℕ := fun n ↦ (q (φ n)).get (hsome n)
    have hqφ : ∀ n, q (φ n) = some (t n) := by
      intro n
      exact (Option.some_get (hsome n)).symm
    have ht : Tendsto t atTop atTop := by
      refine tendsto_atTop.2 fun bound ↦ ?_
      have havoid : ∀ᶠ n in atTop, ∀ r ∈ range bound, q n ≠ some r := by
        rw [eventually_all_finset]
        intro r hr
        exact not_frequently.mp (fun hrFrequently ↦ hfixed ⟨r, hrFrequently⟩)
      have havoidφ : ∀ᶠ n in atTop, ∀ r ∈ range bound, q (φ n) ≠ some r :=
        hφ.tendsto_atTop.eventually havoid
      filter_upwards [havoidφ] with n hn
      by_contra hlt
      have htlt : t n < bound := Nat.lt_of_not_ge hlt
      exact hn (t n) (mem_range.mpr htlt) (hqφ n)
    exact ⟨φ, hφ, Or.inr (Or.inr ⟨t, ht, hqφ⟩)⟩

/-- Simultaneous extraction for a finite set of witness sequences. -/
theorem exists_common_strictMono_hasNormalForm_finset
    {Index : Type*}
    (s : Finset Index) (q : Index → ℕ → Option ℕ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ index ∈ s, HasNormalForm (q index ∘ φ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨id, strictMono_id, by simp⟩
  | @insert index s hindex ih =>
      rcases ih with ⟨φ, hφ, hqφ⟩
      rcases exists_strictMono_hasNormalForm (q index ∘ φ) with ⟨ψ, hψ, hindexψ⟩
      refine ⟨φ ∘ ψ, hφ.comp hψ, ?_⟩
      intro other hother
      rw [mem_insert] at hother
      rcases hother with rfl | hother
      · simpa [Function.comp_def] using hindexψ
      · have hotherφ := hqφ other hother
        simpa [Function.comp_def] using
          hotherφ.comp_of_tendsto_atTop hψ.tendsto_atTop

/-- A finite family of optional natural-number witnesses has one common
strict subsequence on which every witness is fixed, constantly `none`, or
tends to infinity. -/
theorem exists_common_strictMono_hasNormalForm
    {Index : Type*} [Finite Index]
    (q : Index → ℕ → Option ℕ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ index, HasNormalForm (q index ∘ φ) := by
  classical
  letI := Fintype.ofFinite Index
  rcases exists_common_strictMono_hasNormalForm_finset (univ : Finset Index) q with
    ⟨φ, hφ, hqφ⟩
  exact ⟨φ, hφ, fun index ↦ hqφ index (mem_univ index)⟩

end PureTimeWitnessNormalForm
end Math

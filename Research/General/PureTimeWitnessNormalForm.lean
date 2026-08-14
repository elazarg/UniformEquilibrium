/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Order.Filter.AtTopBot.Finite
import Mathlib.Data.Option.Basic

/-!
# A common subsequence normal form for pure-time witnesses

An approximate pure-time deviation is represented by `some t`; `none`
represents Never.  Along one sequence, a selected witness can switch both
between finite times and between finite time and Never.  After extraction it
has only three possible forms:

* one fixed finite time;
* literal Never;
* a finite time tending to infinity.

The extraction can be done simultaneously for any finite family of witnesses.
Thus finitely many active movers do not create arbitrary temporal switching:
all surviving switching is escape of a finite quit time to infinity.

This is a compactness normal form, not a quitting-game contradiction.  It
normalizes already selected witnesses.  It does not say that another
near-best pure-time witness cannot become active after a reset, and it does
not turn an escaping witness into a state-matched suffix.
-/

noncomputable section

namespace Experiments
namespace PureTimeWitnessNormalForm

open Filter Finset

/-- The three subsequential modes of a pure-time/Never witness. -/
def HasNormalForm (q : ℕ → Option ℕ) : Prop :=
  (∃ t : ℕ, ∀ n, q n = some t) ∨
    (∀ n, q n = none) ∨
      ∃ t : ℕ → ℕ, Tendsto t atTop atTop ∧ ∀ n, q n = some (t n)

/-- A normal form remains normal after passing to a strict subsequence. -/
theorem HasNormalForm.comp_strictMono {q : ℕ → Option ℕ}
    (hq : HasNormalForm q) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    HasNormalForm (q ∘ φ) := by
  rcases hq with ⟨t, ht⟩ | hnever | ⟨t, ht, hqt⟩
  · exact Or.inl ⟨t, fun n ↦ ht (φ n)⟩
  · exact Or.inr (Or.inl fun n ↦ hnever (φ n))
  · exact Or.inr (Or.inr ⟨t ∘ φ, ht.comp hφ.tendsto_atTop, fun n ↦ hqt (φ n)⟩)

/-- Every pure-time/Never witness sequence has a strict subsequence in one of
the three normal modes. -/
theorem exists_strictMono_hasNormalForm (q : ℕ → Option ℕ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ HasNormalForm (q ∘ φ) := by
  by_cases hnever : ∃ᶠ n in atTop, q n = none
  · rcases extraction_of_frequently_atTop hnever with ⟨φ, hφ, hqφ⟩
    exact ⟨φ, hφ, Or.inr (Or.inl hqφ)⟩
  by_cases hfixed : ∃ t : ℕ, ∃ᶠ n in atTop, q n = some t
  · rcases hfixed with ⟨t, ht⟩
    rcases extraction_of_frequently_atTop ht with ⟨φ, hφ, hqφ⟩
    exact ⟨φ, hφ, Or.inl ⟨t, hqφ⟩⟩
  · have hsomeEventually : ∀ᶠ n in atTop, q n ≠ none := not_frequently.mp hnever
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
    {Mover : Type*}
    (s : Finset Mover) (q : Mover → ℕ → Option ℕ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ mover ∈ s, HasNormalForm (q mover ∘ φ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨id, strictMono_id, by simp⟩
  | @insert mover s hmover ih =>
      rcases ih with ⟨φ, hφ, hqφ⟩
      rcases exists_strictMono_hasNormalForm (q mover ∘ φ) with ⟨ψ, hψ, hmoverψ⟩
      refine ⟨φ ∘ ψ, hφ.comp hψ, ?_⟩
      intro other hother
      rw [mem_insert] at hother
      rcases hother with rfl | hother
      · simpa [Function.comp_def] using hmoverψ
      · have hotherφ := hqφ other hother
        simpa [Function.comp_def] using hotherφ.comp_strictMono hψ

/-- A finite family of selected pure-time witnesses has one common strict
subsequence on which every mover is fixed finite, literal Never, or escapes to
infinity. -/
theorem exists_common_strictMono_hasNormalForm
    {Mover : Type*} [Finite Mover]
    (q : Mover → ℕ → Option ℕ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ mover, HasNormalForm (q mover ∘ φ) := by
  classical
  letI := Fintype.ofFinite Mover
  rcases exists_common_strictMono_hasNormalForm_finset (univ : Finset Mover) q with
    ⟨φ, hφ, hqφ⟩
  exact ⟨φ, hφ, fun mover ↦ hqφ mover (mem_univ mover)⟩

end PureTimeWitnessNormalForm
end Experiments

/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.ProbabilityMassFunction.DiscreteTightness

/-!
# Finite heads and late finite tails of stopping laws

This module owns the canonical finite stopping prefix containing `Never` and
the complementary mass on finite dates beyond a displayed horizon.
-/

noncomputable section

namespace Math.Probability

/-- Finite stopping outcomes through `horizon`, together with `Never`. -/
def stoppingLawFinitePrefix (horizon : Nat) : Finset (Option Nat) :=
  {none} ∪ (Finset.range (horizon + 1)).image some

@[simp] theorem none_mem_stoppingLawFinitePrefix (horizon : Nat) :
    none ∈ stoppingLawFinitePrefix horizon := by
  simp [stoppingLawFinitePrefix]

@[simp] theorem some_mem_stoppingLawFinitePrefix (horizon time : Nat) :
    some time ∈ stoppingLawFinitePrefix horizon <-> time <= horizon := by
  simp [stoppingLawFinitePrefix]

/-- Total stopping mass at the finite dates through `horizon`. -/
def stoppingLawFiniteHeadMass (law : PMF (Option Nat))
    (horizon : Nat) : Real :=
  ∑ time ∈ Finset.range (horizon + 1), (law (some time)).toReal

/-- Probability of stopping at a finite date strictly after `horizon`.
The retained prefix includes `Never`, so no `Never` mass is counted. -/
def stoppingLawLateFiniteMass (law : PMF (Option Nat))
    (horizon : Nat) : Real :=
  pmfFiniteComplementMass law (stoppingLawFinitePrefix horizon)

/-- The late-finite mass is literally the mass on the complement of the
finite prefix.  Since that prefix contains `none`, this sum has no `Never`
atom. -/
theorem stoppingLawLateFiniteMass_eq_tsum_compl
    (law : PMF (Option Nat)) (horizon : Nat) :
    stoppingLawLateFiniteMass law horizon =
      ∑' choice :
        ↑((↑(stoppingLawFinitePrefix horizon) : Set (Option Nat))ᶜ),
        (law choice).toReal := by
  have hsplit := (pmf_toReal_summable law).sum_add_tsum_compl
    (s := stoppingLawFinitePrefix horizon)
  rw [pmf_toReal_tsum_one law] at hsplit
  unfold stoppingLawLateFiniteMass pmfFiniteComplementMass
  linarith

theorem stoppingLawFinitePrefix_compl_is_late_finite
    {horizon : Nat}
    (choice : {choice // choice ∉ stoppingLawFinitePrefix horizon}) :
    ∃ time : Nat, horizon < time ∧ choice.1 = some time := by
  cases hchoice : choice.1 with
  | none =>
      exact False.elim (choice.property (hchoice ▸ none_mem_stoppingLawFinitePrefix horizon))
  | some time =>
      refine ⟨time, ?_, rfl⟩
      have hnot : ¬ time <= horizon := by
        intro hle
        exact choice.property (hchoice ▸ (some_mem_stoppingLawFinitePrefix horizon time).2 hle)
      omega

/-- Late finite mass is total mass minus the `Never` atom and the canonical
finite head. -/
theorem stoppingLawLateFiniteMass_eq_one_sub_none_sub_finiteHead
    (law : PMF (Option Nat)) (horizon : Nat) :
    stoppingLawLateFiniteMass law horizon =
      1 - (law none).toReal - stoppingLawFiniteHeadMass law horizon := by
  simp [stoppingLawLateFiniteMass, stoppingLawFinitePrefix,
    stoppingLawFiniteHeadMass, pmfFiniteComplementMass, Finset.sum_image]
  ring

/-- Every finite atom beyond a cutoff is bounded by the canonical late-finite
stopping-law mass. -/
theorem stoppingLaw_atom_le_lateFiniteMass
    (law : PMF (Option ℕ)) (horizon time : ℕ) (htime : horizon < time) :
    (law (some time)).toReal ≤ stoppingLawLateFiniteMass law horizon := by
  have hnot : some time ∉ stoppingLawFinitePrefix horizon := by
    simpa using (not_le.mpr htime)
  have hsum := (pmf_toReal_summable law).sum_le_tsum
    (insert (some time) (stoppingLawFinitePrefix horizon))
    (fun _ _ => ENNReal.toReal_nonneg)
  rw [pmf_toReal_tsum_one law] at hsum
  simp only [Finset.sum_insert hnot] at hsum
  unfold stoppingLawLateFiniteMass pmfFiniteComplementMass
  linarith

end Math.Probability

/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.NormalCore

/-!
# Finite support reduction for the four-player Q audit

This file isolates two reusable reductions that do not depend on determinant
enumeration.  A standard LCP is a finite disjunction over complementary
supports, and the corrected normal core is full exactly when every row has a
distinct nonpositive witness.  In the zero-diagonal Q/no-homogeneous branch,
each row also has a positive entry and each column a negative entry.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The polyhedral LCP cell attached to a proposed positive-weight support.
Weights outside `support` vanish and residuals on `support` vanish. -/
def HasStandardLCPSupportSolution
    (M : ι → ι → ℝ) (q : ι → ℝ) (support : Finset ι) : Prop :=
  ∃ weight : ι → ℝ,
    (∀ i, 0 ≤ weight i) ∧
    (∀ i, 0 ≤ q i + ∑ j, weight j * M i j) ∧
    (∀ i ∈ support, q i + ∑ j, weight j * M i j = 0) ∧
    (∀ i ∉ support, weight i = 0)

omit [DecidableEq ι] in
/-- Exact finite-support decomposition of one standard LCP. -/
theorem hasStandardLCPSolution_iff_exists_support
    (M : ι → ι → ℝ) (q : ι → ℝ) :
    HasStandardLCPSolution M q ↔
      ∃ support : Finset ι, HasStandardLCPSupportSolution M q support := by
  classical
  constructor
  · rintro ⟨solution⟩
    let support := Finset.univ.filter fun i => solution.weight i ≠ 0
    refine ⟨support, solution.weight, solution.weight_nonneg,
      solution.residual_nonneg, ?_, ?_⟩
    · intro i hi
      have hweight : solution.weight i ≠ 0 := by
        simpa [support] using hi
      exact (mul_eq_zero.mp (solution.complementary i)).resolve_left hweight
    · intro i hi
      by_contra hweight
      exact hi (by simp [support, hweight])
  · rintro ⟨support, weight, hweight, hresidual, hon, hoff⟩
    refine ⟨{
      weight := weight
      weight_nonneg := hweight
      residual_nonneg := hresidual
      complementary := ?_ }⟩
    intro i
    by_cases hi : i ∈ support
    · rw [hon i hi, mul_zero]
    · rw [hoff i hi, zero_mul]

omit [DecidableEq ι] in
/-- Textbook Q is therefore a universal finite disjunction of explicit
polyhedral support systems. -/
theorem isStandardQMatrix_iff_forall_exists_support
    (M : ι → ι → ℝ) :
    IsStandardQMatrix M ↔
      ∀ q : ι → ℝ, ∃ support : Finset ι,
        HasStandardLCPSupportSolution M q support := by
  classical
  simp only [IsStandardQMatrix, hasStandardLCPSolution_iff_exists_support]

/-- The corrected core is full exactly when its first deletion step removes
nothing. -/
theorem normalCore_eq_univ_iff_forall_exists_distinct_nonpos
    (M : ι → ι → ℝ) :
    normalCore M = Finset.univ ↔
      ∀ i, ∃ j, j ≠ i ∧ M i j ≤ 0 := by
  constructor
  · intro hcore i
    have hi : i ∈ normalCore M := by rw [hcore]; simp
    obtain ⟨j, _hjcore, hji, hnonpos⟩ :=
      exists_core_blocker_of_mem_normalCore M hi
    exact ⟨j, hji, hnonpos⟩
  · intro hwitness
    have hall : ∀ n i, i ∈ normalLayer M n := by
      intro n
      induction n with
      | zero => intro i; simp
      | succ n ih =>
          intro i
          rw [mem_normalLayer_succ]
          obtain ⟨j, hji, hnonpos⟩ := hwitness i
          exact ⟨ih i, j, ih j, hji, hnonpos⟩
    apply Finset.eq_univ_of_forall
    intro i
    rw [mem_normalCore]
    exact fun n => hall n i

/-- Immediate sign restrictions in the zero-diagonal, full-core,
standard-Q/no-homogeneous branch. -/
theorem fullCore_standardQ_noHomogeneous_sign_reductions
    (M : ι → ι → ℝ)
    (hdiag : ∀ i, M i i = 0)
    (hcore : normalCore M = Finset.univ)
    (hQ : IsStandardQMatrix M)
    (hhom : ¬HasHomogeneousSimplexSolution M) :
    (∀ i, ∃ j, j ≠ i ∧ M i j ≤ 0) ∧
      (∀ i, ∃ j, 0 < M i j) ∧
      (∀ j, ∃ i, M i j < 0) := by
  exact ⟨
    (normalCore_eq_univ_iff_forall_exists_distinct_nonpos M).1 hcore,
    exists_positive_entry_in_row_of_standardQ M hQ,
    exists_negative_entry_in_column_of_noHomogeneous M hdiag hhom⟩

end QuittingLCPClassification
end GameTheory

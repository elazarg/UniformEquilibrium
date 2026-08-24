/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.LinearAlgebra.Matrix.Stochastic

/-!
# Eliminating one state from a finite Markov reward account

This file records the exact Schur-complement calculation needed for a state-count induction on
finite homogeneous Markov chains.  Eliminating a state does not give that state's excursions an
independent variation budget.  Instead, every collapsed excursion splits into the direct
variation of the reduced transition and a nonnegative triangle excess.  The latter is the
coupled quantity that a sharp cardinality proof still has to control.
-/

namespace Math.Probability

noncomputable section

variable {State : Type*}

/-- The mass sent from `source` to `target` after eliminating `pivot`. -/
def schurWeight (matrix : State → State → ℝ) (pivot source target : State) : ℝ :=
  matrix source target +
    matrix source pivot * matrix pivot target / (1 - matrix pivot pivot)

/-- The extra absolute variation incurred by routing from `source` to `target` through `pivot`
rather than replacing the two edges by one direct edge. -/
def triangleExcursionExcess (value : State → ℝ) (source pivot target : State) : ℝ :=
  |value pivot - value source| + |value target - value pivot| -
    |value target - value source|

/-- Absolute-variation reward carried by the Schur-complement transition.  Its excursion term
keeps both legs through `pivot`; it is not a state-owned renewal surrogate. -/
def schurVariationReward
    (matrix : State → State → ℝ) (value : State → ℝ)
    (pivot source target : State) : ℝ :=
  matrix source target * |value target - value source| +
    matrix source pivot * matrix pivot target / (1 - matrix pivot pivot) *
      (|value pivot - value source| + |value target - value pivot|)

theorem triangleExcursionExcess_nonneg
    (value : State → ℝ) (source pivot target : State) :
    0 ≤ triangleExcursionExcess value source pivot target := by
  dsimp only [triangleExcursionExcess]
  have htriangle : |value target - value source| ≤
      |value pivot - value source| + |value target - value pivot| := by
    calc
      |value target - value source| =
          |(value pivot - value source) + (value target - value pivot)| := by ring_nf
      _ ≤ |value pivot - value source| + |value target - value pivot| :=
        abs_add_le _ _
  linarith

/-- Pointwise reward decomposition: reduced-chain variation plus the triangle excess of the
collapsed excursion. -/
theorem schurVariationReward_eq_reduced_add_excess
    (matrix : State → State → ℝ) (value : State → ℝ)
    (pivot source target : State) :
    schurVariationReward matrix value pivot source target =
      schurWeight matrix pivot source target * |value target - value source| +
        matrix source pivot * matrix pivot target / (1 - matrix pivot pivot) *
          triangleExcursionExcess value source pivot target := by
  simp only [schurVariationReward, schurWeight, triangleExcursionExcess]
  ring

/-- Eliminating a nonabsorbing state preserves nonnegativity of transition weights. -/
theorem schurWeight_nonneg
    (matrix : State → State → ℝ) (pivot source target : State)
    (matrix_nonneg : ∀ i j, 0 ≤ matrix i j)
    (pivot_exit_pos : 0 < 1 - matrix pivot pivot) :
    0 ≤ schurWeight matrix pivot source target := by
  dsimp only [schurWeight]
  exact add_nonneg (matrix_nonneg source target)
    (div_nonneg (mul_nonneg (matrix_nonneg source pivot) (matrix_nonneg pivot target))
      pivot_exit_pos.le)

variable [Fintype State] [DecidableEq State]

/-- The Schur complement is row stochastic on the states distinct from the eliminated pivot. -/
theorem sum_schurWeight_erase_eq_one
    (matrix : State → State → ℝ) (pivot source : State)
    (row_sum : ∀ i, ∑ j, matrix i j = 1)
    (pivot_exit_pos : 0 < 1 - matrix pivot pivot) :
    ∑ target ∈ Finset.univ.erase pivot,
        schurWeight matrix pivot source target = 1 := by
  have hsource :
      (∑ target ∈ Finset.univ.erase pivot, matrix source target) +
          matrix source pivot = 1 := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ pivot)]
    exact row_sum source
  have hpivot :
      (∑ target ∈ Finset.univ.erase pivot, matrix pivot target) +
          matrix pivot pivot = 1 := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ pivot)]
    exact row_sum pivot
  have hfactor :
      (∑ target ∈ Finset.univ.erase pivot,
        matrix source pivot * matrix pivot target / (1 - matrix pivot pivot)) =
          matrix source pivot / (1 - matrix pivot pivot) *
            ∑ target ∈ Finset.univ.erase pivot, matrix pivot target := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro target _
    ring
  simp_rw [schurWeight, Finset.sum_add_distrib]
  rw [hfactor]
  have hpivot_exit :
      ∑ target ∈ Finset.univ.erase pivot, matrix pivot target =
        1 - matrix pivot pivot := by
    linarith
  rw [hpivot_exit]
  field_simp [ne_of_gt pivot_exit_pos]
  linarith

/-- Summed form of the coupled reward decomposition on the reduced row. -/
theorem sum_schurVariationReward_erase_eq_reduced_add_excess
    (matrix : State → State → ℝ) (value : State → ℝ)
    (pivot source : State) :
    (∑ target ∈ Finset.univ.erase pivot,
        schurVariationReward matrix value pivot source target) =
      (∑ target ∈ Finset.univ.erase pivot,
        schurWeight matrix pivot source target *
          |value target - value source|) +
      ∑ target ∈ Finset.univ.erase pivot,
        matrix source pivot * matrix pivot target /
            (1 - matrix pivot pivot) *
          triangleExcursionExcess value source pivot target := by
  simp_rw [schurVariationReward_eq_reduced_add_excess, Finset.sum_add_distrib]

/-- The reduced absolute-variation reward is no larger than the reward of the excursions it
replaces.  The exact gap is the nonnegative triangle-excess sum displayed above. -/
theorem sum_schurWeight_abs_le_sum_schurVariationReward
    (matrix : State → State → ℝ) (value : State → ℝ)
    (pivot source : State)
    (matrix_nonneg : ∀ i j, 0 ≤ matrix i j)
    (pivot_exit_pos : 0 < 1 - matrix pivot pivot) :
    (∑ target ∈ Finset.univ.erase pivot,
        schurWeight matrix pivot source target *
          |value target - value source|) ≤
      ∑ target ∈ Finset.univ.erase pivot,
        schurVariationReward matrix value pivot source target := by
  rw [sum_schurVariationReward_erase_eq_reduced_add_excess]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun target _ =>
    mul_nonneg
      (div_nonneg
        (mul_nonneg (matrix_nonneg source pivot) (matrix_nonneg pivot target))
        pivot_exit_pos.le)
      (triangleExcursionExcess_nonneg value source pivot target))

/-- Backward harmonicity is preserved by eliminating one state. -/
theorem harmonic_sum_schurWeight_erase
    (matrix : State → State → ℝ) (value : State → ℝ)
    (pivot source : State)
    (harmonic : ∀ i, value i = ∑ j, matrix i j * value j)
    (pivot_exit_pos : 0 < 1 - matrix pivot pivot) :
    value source =
      ∑ target ∈ Finset.univ.erase pivot,
        schurWeight matrix pivot source target * value target := by
  have hsource : value source =
      (∑ target ∈ Finset.univ.erase pivot,
        matrix source target * value target) +
          matrix source pivot * value pivot := by
    rw [harmonic source, Finset.sum_erase_add _ _ (Finset.mem_univ pivot)]
  have hpivot : value pivot =
      (∑ target ∈ Finset.univ.erase pivot,
        matrix pivot target * value target) +
          matrix pivot pivot * value pivot := by
    calc
      value pivot = ∑ target, matrix pivot target * value target := harmonic pivot
      _ = (∑ target ∈ Finset.univ.erase pivot,
          matrix pivot target * value target) +
            matrix pivot pivot * value pivot :=
        (Finset.sum_erase_add _ _ (Finset.mem_univ pivot)).symm
  simp_rw [schurWeight, add_mul, Finset.sum_add_distrib]
  rw [show (∑ target ∈ Finset.univ.erase pivot,
      matrix source pivot * matrix pivot target /
        (1 - matrix pivot pivot) * value target) =
      matrix source pivot / (1 - matrix pivot pivot) *
        ∑ target ∈ Finset.univ.erase pivot,
          matrix pivot target * value target by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro target _
    ring]
  have hpivot_rearranged :
      (1 - matrix pivot pivot) * value pivot =
        ∑ target ∈ Finset.univ.erase pivot,
          matrix pivot target * value target := by
    linarith
  rw [← hpivot_rearranged]
  field_simp [ne_of_gt pivot_exit_pos]
  linarith

end

end Math.Probability

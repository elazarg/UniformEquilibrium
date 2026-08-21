/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.ChargedOccupationAlternative

/-!
# Integer chattering approximation of a charged circulation

A normalized positive charged circulation is a real nonnegative occupation
vector `mass` with zero aggregate displacement and aggregate charge one.
For an integer scale `N`, replace `N * mass i` by its natural floor.  The
resulting rational occupation coefficients

```text
floor(N * mass i) / N
```

have aggregate displacement `O(1/N)` and aggregate charge `1 + O(1/N)`.

The standard dynamical interpretation is a chattering word: use microscopic
step `1/N^2`, take `floor(N * mass i)` copies of move `i` in one microcycle,
and repeat the microcycle `N` times. Its total linearized coefficient is
exactly `floor(N * mass i) / N`.

This module proves the linear rounding and uniform prefix estimates. Applying
them to a nonlinear system additionally requires a domain-specific composition
estimate and an interpretation of the abstract charge.
-/

noncomputable section

namespace Math
namespace Probability

open Finset BigOperators

variable {State Move : Type*} [Fintype Move]

/-- Rational occupation coefficient obtained by flooring at scale `N`. -/
def chatteringCoefficient
    (mass : Move → ℝ) (N : ℕ) (move : Move) : ℝ :=
  (⌊(N : ℝ) * mass move⌋₊ : ℝ) / N

/-- The chattering word uses this many copies of a move in each of its `N`
microcycles. -/
def chatteringCount
    (mass : Move → ℝ) (N : ℕ) (move : Move) : ℕ :=
  ⌊(N : ℝ) * mass move⌋₊

omit [Fintype Move] in
@[simp]
theorem chatteringCoefficient_eq_count_div
    (mass : Move → ℝ) (N : ℕ) (move : Move) :
    chatteringCoefficient mass N move =
      (chatteringCount mass N move : ℝ) / N := rfl

omit [Fintype Move] in
/-- Flooring never increases a nonnegative occupation coefficient. -/
theorem chatteringCoefficient_le
    (mass : Move → ℝ) (N : ℕ) (hN : 0 < N)
    (move : Move) (hmass : 0 ≤ mass move) :
    chatteringCoefficient mass N move ≤ mass move := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hfloor : (⌊(N : ℝ) * mass move⌋₊ : ℝ) ≤
      (N : ℝ) * mass move :=
    Nat.floor_le (mul_nonneg hNreal.le hmass)
  exact (div_le_iff₀ hNreal).2 (by simpa [mul_comm] using hfloor)

omit [Fintype Move] in
/-- The coefficient lost to flooring is strictly below `1/N`. -/
theorem mass_sub_chatteringCoefficient_lt
    (mass : Move → ℝ) (N : ℕ) (hN : 0 < N)
    (move : Move) :
    mass move - chatteringCoefficient mass N move < 1 / N := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hfloor := Nat.lt_floor_add_one ((N : ℝ) * mass move)
  rw [chatteringCoefficient]
  apply (sub_lt_iff_lt_add).2
  calc
    mass move = ((N : ℝ) * mass move) / N := by
      field_simp
    _ < ((⌊(N : ℝ) * mass move⌋₊ : ℕ) + 1 : ℝ) / N :=
      (div_lt_div_iff_of_pos_right hNreal).2 hfloor
    _ = 1 / N + (⌊(N : ℝ) * mass move⌋₊ : ℝ) / N := by
      ring

omit [Fintype Move] in
/-- Absolute coefficient error is at most `1/N`. -/
theorem abs_chatteringCoefficient_sub_mass_le
    (mass : Move → ℝ) (N : ℕ) (hN : 0 < N)
    (move : Move) (hmass : 0 ≤ mass move) :
    |chatteringCoefficient mass N move - mass move| ≤ 1 / N := by
  have hle := chatteringCoefficient_le mass N hN move hmass
  have hlt := mass_sub_chatteringCoefficient_lt mass N hN move
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  linarith

/-- Coordinatewise aggregate displacement error of the rounded occupation. -/
theorem abs_sum_chatteringCoefficient_mul_column_le
    (column : Move → State → ℝ) (mass : Move → ℝ)
    (N : ℕ) (hN : 0 < N)
    (hmass : ∀ move, 0 ≤ mass move)
    (state : State)
    (hbalance : ∑ move, mass move * column move state = 0) :
    |∑ move, chatteringCoefficient mass N move * column move state| ≤
      (∑ move, |column move state|) / N := by
  have heq : (∑ move,
      chatteringCoefficient mass N move * column move state) =
      ∑ move,
        (chatteringCoefficient mass N move - mass move) *
          column move state := by
    calc
      (∑ move, chatteringCoefficient mass N move * column move state) =
          (∑ move,
            (chatteringCoefficient mass N move - mass move) *
              column move state) +
            ∑ move, mass move * column move state := by
        simp_rw [sub_mul, Finset.sum_sub_distrib]
        ring
      _ = _ := by rw [hbalance, add_zero]
  rw [heq]
  calc
    |∑ move,
        (chatteringCoefficient mass N move - mass move) *
          column move state| ≤
        ∑ move,
          |(chatteringCoefficient mass N move - mass move) *
            column move state| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ move, (1 / N) * |column move state| := by
      apply Finset.sum_le_sum
      intro move _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right
        (abs_chatteringCoefficient_sub_mass_le mass N hN move (hmass move))
        (abs_nonneg _)
    _ = (∑ move, |column move state|) / N := by
      rw [← Finset.mul_sum]
      ring

/-- Aggregate charge error of the rounded occupation. -/
theorem abs_sum_chatteringCoefficient_mul_charge_sub_one_le
    (charge mass : Move → ℝ)
    (N : ℕ) (hN : 0 < N)
    (hmass : ∀ move, 0 ≤ mass move)
    (hcharge : ∑ move, mass move * charge move = 1) :
    |(∑ move, chatteringCoefficient mass N move * charge move) - 1| ≤
      (∑ move, |charge move|) / N := by
  have heq : (∑ move,
      chatteringCoefficient mass N move * charge move) - 1 =
      ∑ move,
        (chatteringCoefficient mass N move - mass move) * charge move := by
    calc
      (∑ move, chatteringCoefficient mass N move * charge move) - 1 =
          (∑ move, chatteringCoefficient mass N move * charge move) -
            ∑ move, mass move * charge move := by rw [hcharge]
      _ = _ := by
        simp_rw [sub_mul, Finset.sum_sub_distrib]
  rw [heq]
  calc
    |∑ move,
        (chatteringCoefficient mass N move - mass move) * charge move| ≤
        ∑ move,
          |(chatteringCoefficient mass N move - mass move) * charge move| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ move, (1 / N) * |charge move| := by
      apply Finset.sum_le_sum
      intro move _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right
        (abs_chatteringCoefficient_sub_mass_le mass N hN move (hmass move))
        (abs_nonneg _)
    _ = (∑ move, |charge move|) / N := by
      rw [← Finset.mul_sum]
      ring

/-- A uniformly source-matched perturbation of the charged columns preserves
the aggregate `O(1/N)` charge estimate. -/
theorem abs_sum_chatteringCoefficient_mul_perturbed_charge_sub_one_le
    (charge actualCharge mass : Move → ℝ)
    (N : ℕ) (hN : 0 < N)
    (hmass : ∀ move, 0 ≤ mass move)
    (hcharge : ∑ move, mass move * charge move = 1)
    (hclose : ∀ move, |actualCharge move - charge move| ≤ 1 / N) :
    |(∑ move, chatteringCoefficient mass N move * actualCharge move) - 1| ≤
      ((∑ move, |charge move|) + ∑ move, mass move) / N := by
  have hcoefficientNonneg : ∀ move,
      0 ≤ chatteringCoefficient mass N move := by
    intro move
    unfold chatteringCoefficient
    positivity
  have hcoefficientLe : ∀ move,
      chatteringCoefficient mass N move ≤ mass move := by
    intro move
    exact chatteringCoefficient_le mass N hN move (hmass move)
  have hfrozen := abs_sum_chatteringCoefficient_mul_charge_sub_one_le
    charge mass N hN hmass hcharge
  have hperturb :
      |∑ move, chatteringCoefficient mass N move *
          (actualCharge move - charge move)| ≤
        (∑ move, mass move) / N := by
    calc
      |∑ move, chatteringCoefficient mass N move *
          (actualCharge move - charge move)| ≤
          ∑ move, |chatteringCoefficient mass N move *
            (actualCharge move - charge move)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ move, mass move * (1 / N) := by
        apply Finset.sum_le_sum
        intro move _
        rw [abs_mul, abs_of_nonneg (hcoefficientNonneg move)]
        exact mul_le_mul (hcoefficientLe move) (hclose move)
          (abs_nonneg _) (hmass move)
      _ = (∑ move, mass move) / N := by
        rw [← Finset.sum_mul]
        ring
  have hdecompose :
      (∑ move, chatteringCoefficient mass N move * actualCharge move) - 1 =
        ((∑ move, chatteringCoefficient mass N move * charge move) - 1) +
          ∑ move, chatteringCoefficient mass N move *
            (actualCharge move - charge move) := by
    calc
      (∑ move, chatteringCoefficient mass N move * actualCharge move) - 1 =
          (∑ move, (chatteringCoefficient mass N move * charge move +
            chatteringCoefficient mass N move *
              (actualCharge move - charge move))) - 1 := by
        apply congrArg (fun value : ℝ ↦ value - 1)
        apply Finset.sum_congr rfl
        intro move _
        ring
      _ = ((∑ move, chatteringCoefficient mass N move * charge move) - 1) +
          ∑ move, chatteringCoefficient mass N move *
            (actualCharge move - charge move) := by
        rw [Finset.sum_add_distrib]
        ring
  rw [hdecompose]
  calc
    |((∑ move, chatteringCoefficient mass N move * charge move) - 1) +
        ∑ move, chatteringCoefficient mass N move *
          (actualCharge move - charge move)| ≤
        |(∑ move, chatteringCoefficient mass N move * charge move) - 1| +
          |∑ move, chatteringCoefficient mass N move *
            (actualCharge move - charge move)| := abs_add_le _ _
    _ ≤ (∑ move, |charge move|) / N +
        (∑ move, mass move) / N := add_le_add hfrozen hperturb
    _ = ((∑ move, |charge move|) + ∑ move, mass move) / N := by ring

/-- **Integer chattering approximation.**  Every normalized positive charged
circulation has an explicit natural-number word whose aggregate displacement
is `O(1/N)` and whose charge is within `O(1/N)` of one. -/
theorem HasNormalizedPositiveChargedCirculation.exists_chatteringCounts
    (column : Move → State → ℝ) (charge : Move → ℝ)
    (C : HasNormalizedPositiveChargedCirculation column charge)
    (N : ℕ) (hN : 0 < N) :
    ∃ count : Move → ℕ,
      (∀ state,
        |∑ move, ((count move : ℝ) / N) * column move state| ≤
          (∑ move, |column move state|) / N) ∧
      |(∑ move, ((count move : ℝ) / N) * charge move) - 1| ≤
        (∑ move, |charge move|) / N := by
  obtain ⟨mass, hmass, hbalance, hcharge⟩ := C
  refine ⟨chatteringCount mass N, ?_, ?_⟩
  · intro state
    simpa only [← chatteringCoefficient_eq_count_div] using
      abs_sum_chatteringCoefficient_mul_column_le
        column mass N hN hmass state (hbalance state)
  · simpa only [← chatteringCoefficient_eq_count_div] using
      abs_sum_chatteringCoefficient_mul_charge_sub_one_le
        charge mass N hN hmass hcharge

/-- In particular the chattering charge has an explicit lower bound tending
to one. -/
theorem HasNormalizedPositiveChargedCirculation.exists_chatteringCounts_charge_lower
    (column : Move → State → ℝ) (charge : Move → ℝ)
    (C : HasNormalizedPositiveChargedCirculation column charge)
    (N : ℕ) (hN : 0 < N) :
    ∃ count : Move → ℕ,
      (∀ state,
        |∑ move, ((count move : ℝ) / N) * column move state| ≤
          (∑ move, |column move state|) / N) ∧
      1 - (∑ move, |charge move|) / N ≤
        ∑ move, ((count move : ℝ) / N) * charge move := by
  obtain ⟨count, hcolumn, hcharge⟩ := C.exists_chatteringCounts
    column charge N hN
  refine ⟨count, hcolumn, ?_⟩
  have hnegative := neg_le_of_abs_le hcharge
  linarith

/-! ## The chattering word remains local in the linearized geometry -/

/-- Aggregate coefficient after `completed` whole microcycles and an
arbitrary partial microcycle.  Each microscopic move has scale `1/N^2`. -/
def chatteringPrefixCoefficient
    (mass : Move → ℝ) (N completed : ℕ) (partialCount : Move → ℕ)
    (move : Move) : ℝ :=
  ((completed : ℝ) * chatteringCount mass N move + partialCount move) / N ^ 2

/-- Exact separation into completed-cycle and current-partial-cycle terms. -/
theorem sum_chatteringPrefixCoefficient_mul
    (column : Move → State → ℝ) (mass : Move → ℝ)
    (N completed : ℕ) (partialCount : Move → ℕ) (state : State) :
    (∑ move, chatteringPrefixCoefficient mass N completed partialCount move *
        column move state) =
      ((completed : ℝ) / N) *
          (∑ move, chatteringCoefficient mass N move * column move state) +
        ∑ move, ((partialCount move : ℝ) / N ^ 2) * column move state := by
  unfold chatteringPrefixCoefficient chatteringCoefficient chatteringCount
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro move _
  field_simp

/-- **Uniform prefix locality.** Use `N` identical microcycles, each with
`floor(N * mass i)` copies of move `i` at scale `1/N^2`. After any number at
most `N` of completed microcycles and any partial next cycle, a balanced
nonnegative mass stays within `O(1/N)` of the base in the selected coordinate.
No ordering of the moves inside a microcycle is required. -/
theorem abs_sum_chatteringPrefixCoefficient_mul_column_le
    (column : Move → State → ℝ) (mass : Move → ℝ)
    (N completed : ℕ) (hN : 0 < N) (hcompleted : completed ≤ N)
    (partialCount : Move → ℕ)
    (hpartial : ∀ move, partialCount move ≤ chatteringCount mass N move)
    (hmass : ∀ move, 0 ≤ mass move) (state : State)
    (hbalance : ∑ move, mass move * column move state = 0) :
    |∑ move,
        chatteringPrefixCoefficient mass N completed partialCount move *
          column move state| ≤
      ((∑ move, |column move state|) +
        ∑ move, mass move * |column move state|) / N := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hcompleted0 : 0 ≤ (completed : ℝ) / N := by positivity
  have hcompleted1 : (completed : ℝ) / N ≤ 1 := by
    exact (div_le_one hNreal).2 (by exact_mod_cast hcompleted)
  have hrounded :=
    abs_sum_chatteringCoefficient_mul_column_le
      column mass N hN hmass state hbalance
  have hcolumnSum0 : 0 ≤ ∑ move, |column move state| :=
    Finset.sum_nonneg fun move _ => abs_nonneg (column move state)
  have hcompletedBound :
      |((completed : ℝ) / N) *
          (∑ move, chatteringCoefficient mass N move *
            column move state)| ≤
        (∑ move, |column move state|) / N := by
    rw [abs_mul, abs_of_nonneg hcompleted0]
    exact (mul_le_mul hcompleted1 hrounded (abs_nonneg _)
      (by positivity)).trans (by simp)
  have hpartialCoefficient : ∀ move,
      (partialCount move : ℝ) / (N : ℝ) ^ 2 ≤ mass move / N := by
    intro move
    have hpCount : (partialCount move : ℝ) ≤
        chatteringCount mass N move := by exact_mod_cast hpartial move
    have hcountMass : (chatteringCount mass N move : ℝ) ≤
        (N : ℝ) * mass move := by
      exact Nat.floor_le (mul_nonneg hNreal.le (hmass move))
    apply (div_le_iff₀ (sq_pos_of_pos hNreal)).2
    have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNreal
    calc
      (partialCount move : ℝ) ≤ (N : ℝ) * mass move := hpCount.trans hcountMass
      _ = (mass move / N) * (N : ℝ) ^ 2 := by
        field_simp
  have hpartialBound :
      |∑ move, ((partialCount move : ℝ) / N ^ 2) * column move state| ≤
        (∑ move, mass move * |column move state|) / N := by
    calc
      |∑ move, ((partialCount move : ℝ) / N ^ 2) * column move state| ≤
          ∑ move, |((partialCount move : ℝ) / N ^ 2) * column move state| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ move, (mass move / N) * |column move state| := by
        apply Finset.sum_le_sum
        intro move _
        rw [abs_mul, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_right
          (hpartialCoefficient move) (abs_nonneg _)
      _ = (∑ move, mass move * |column move state|) / N := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro move _
        ring
  rw [sum_chatteringPrefixCoefficient_mul]
  calc
    |((completed : ℝ) / N) *
          (∑ move, chatteringCoefficient mass N move * column move state) +
        ∑ move, ((partialCount move : ℝ) / N ^ 2) * column move state| ≤
        |((completed : ℝ) / N) *
          (∑ move, chatteringCoefficient mass N move * column move state)| +
          |∑ move, ((partialCount move : ℝ) / N ^ 2) *
            column move state| := abs_add_le _ _
    _ ≤ (∑ move, |column move state|) / N +
        (∑ move, mass move * |column move state|) / N :=
      add_le_add hcompletedBound hpartialBound
    _ = ((∑ move, |column move state|) +
        ∑ move, mass move * |column move state|) / N := by ring

omit [Fintype Move] in
/-- A prefix coefficient is nonnegative. -/
theorem chatteringPrefixCoefficient_nonneg
    (mass : Move → ℝ) (N completed : ℕ) (partialCount : Move → ℕ)
    (move : Move) :
    0 ≤ chatteringPrefixCoefficient mass N completed partialCount move := by
  unfold chatteringPrefixCoefficient
  positivity

omit [Fintype Move] in
/-- During the prescribed `N` microcycles, every prefix coefficient is at
most twice its limiting occupation mass. -/
theorem chatteringPrefixCoefficient_le_two_mul
    (mass : Move → ℝ) (N completed : ℕ) (partialCount : Move → ℕ)
    (hN : 0 < N) (hcompleted : completed ≤ N)
    (hpartial : ∀ move, partialCount move ≤ chatteringCount mass N move)
    (hmass : ∀ move, 0 ≤ mass move) (move : Move) :
    chatteringPrefixCoefficient mass N completed partialCount move ≤
      2 * mass move := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hcompletedReal : (completed : ℝ) ≤ N := by
    exact_mod_cast hcompleted
  have hpartialReal : (partialCount move : ℝ) ≤
      chatteringCount mass N move := by
    exact_mod_cast hpartial move
  have hcountMass : (chatteringCount mass N move : ℝ) ≤
      (N : ℝ) * mass move := by
    exact Nat.floor_le (mul_nonneg hNreal.le (hmass move))
  unfold chatteringPrefixCoefficient
  apply (div_le_iff₀ (sq_pos_of_pos hNreal)).2
  calc
    (completed : ℝ) * chatteringCount mass N move + partialCount move ≤
        (N : ℝ) * ((N : ℝ) * mass move) + (N : ℝ) * mass move := by
      exact add_le_add
        (mul_le_mul hcompletedReal hcountMass (Nat.cast_nonneg _) hNreal.le)
        (hpartialReal.trans hcountMass)
    _ ≤ (2 * mass move) * (N : ℝ) ^ 2 := by
      nlinarith [hmass move]

/-- **Source perturbations preserve uniform prefix locality.** If every
actual column is within `1/N` of one balanced frozen column, then the whole
rounded chattering prefix remains `O(1/N)` from the common source. -/
theorem abs_sum_chatteringPrefixCoefficient_mul_perturbed_column_le
    (column actual : Move → State → ℝ) (mass : Move → ℝ)
    (N completed : ℕ) (hN : 0 < N) (hcompleted : completed ≤ N)
    (partialCount : Move → ℕ)
    (hpartial : ∀ move, partialCount move ≤ chatteringCount mass N move)
    (hmass : ∀ move, 0 ≤ mass move) (state : State)
    (hbalance : ∑ move, mass move * column move state = 0)
    (hclose : ∀ move, |actual move state - column move state| ≤ 1 / N) :
    |∑ move,
        chatteringPrefixCoefficient mass N completed partialCount move *
          actual move state| ≤
      ((∑ move, |column move state|) +
          ∑ move, mass move * |column move state| +
        2 * ∑ move, mass move) / N := by
  have hfrozen := abs_sum_chatteringPrefixCoefficient_mul_column_le
    column mass N completed hN hcompleted partialCount hpartial hmass state
      hbalance
  have hperturb :
      |∑ move,
          chatteringPrefixCoefficient mass N completed partialCount move *
            (actual move state - column move state)| ≤
        (2 * ∑ move, mass move) / N := by
    calc
      |∑ move,
          chatteringPrefixCoefficient mass N completed partialCount move *
            (actual move state - column move state)| ≤
          ∑ move,
            |chatteringPrefixCoefficient mass N completed partialCount move *
              (actual move state - column move state)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ move, (2 * mass move) * (1 / N) := by
        apply Finset.sum_le_sum
        intro move _
        rw [abs_mul, abs_of_nonneg
          (chatteringPrefixCoefficient_nonneg mass N completed partialCount move)]
        exact mul_le_mul
          (chatteringPrefixCoefficient_le_two_mul mass N completed partialCount
            hN hcompleted hpartial hmass move)
          (hclose move) (abs_nonneg _) (mul_nonneg (by positivity) (hmass move))
      _ = (2 * ∑ move, mass move) / N := by
        calc
          ∑ move, (2 * mass move) * (1 / N) =
              ∑ move, mass move * (2 / N) := by
            apply Finset.sum_congr rfl
            intro move _
            ring
          _ = (∑ move, mass move) * (2 / N) := by
            rw [Finset.sum_mul]
          _ = (2 * ∑ move, mass move) / N := by ring
  have hdecompose :
      (∑ move,
          chatteringPrefixCoefficient mass N completed partialCount move *
            actual move state) =
        (∑ move,
          chatteringPrefixCoefficient mass N completed partialCount move *
            column move state) +
        ∑ move,
          chatteringPrefixCoefficient mass N completed partialCount move *
            (actual move state - column move state) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro move _
    ring
  rw [hdecompose]
  calc
    |(∑ move,
        chatteringPrefixCoefficient mass N completed partialCount move *
          column move state) +
      ∑ move,
        chatteringPrefixCoefficient mass N completed partialCount move *
          (actual move state - column move state)| ≤
        |∑ move,
          chatteringPrefixCoefficient mass N completed partialCount move *
            column move state| +
        |∑ move,
          chatteringPrefixCoefficient mass N completed partialCount move *
            (actual move state - column move state)| := abs_add_le _ _
    _ ≤ ((∑ move, |column move state|) +
          ∑ move, mass move * |column move state|) / N +
        (2 * ∑ move, mass move) / N := add_le_add hfrozen hperturb
    _ = ((∑ move, |column move state|) +
          ∑ move, mass move * |column move state| +
        2 * ∑ move, mass move) / N := by ring

end Probability
end Math

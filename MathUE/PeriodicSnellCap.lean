/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

/-!
# The selected periodic Snell cap

Fix per-stage stopping data `quitValue`, `reward`, and `mass : ℕ → ℝ`, all
periodic with period `P`, with nonnegative masses at most one and one-period
survival product strictly below one.  Starting at any phase, a deterministic
stopping plan either quits after finitely many stages or never quits.  This
module defines:

* `pureTimeValue steps phase` — continue `steps` stages from `phase`, then
  quit;
* `neverValue phase` — the survival-weighted one-period reward accumulation
  divided by one minus the one-period survival product; and
* `selectedCap phase` — the better of the first period's pure quit times and
  never quitting.

It proves that the never value balances its affine continuation equation,
that every deterministic quit time is dominated by the selected cap, and that
the selected cap satisfies the cyclic Snell equation

`selectedCap phase = max (quitValue phase)
  (reward phase + mass phase * selectedCap (phase + 1))`.

This is the abstract periodic sibling of the stationary selected cap used by
the quitting stationary machinery.  The game-facing periodic unilateral cap —
identifying `quitValue`, `reward`, and `mass` with the fixed-opponents data of
a periodic behavioral profile and dominating arbitrary behavioral deviations —
is future work and is not provided here.
-/

namespace Math.PeriodicSnell

open Finset

/-- `range (P + 1)` is nonempty. -/
theorem range_succ_nonempty (P : ℕ) : (range (P + 1)).Nonempty :=
  ⟨0, mem_range.mpr (Nat.succ_pos P)⟩

/-! ## Pure-time values, survival products, accumulations -/

/-- Value of continuing `steps` stages from `phase` and then quitting. -/
def pureTimeValue (quitValue reward mass : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, phase => quitValue phase
  | steps + 1, phase =>
      reward phase + mass phase * pureTimeValue quitValue reward mass steps (phase + 1)

/-- Product of `count` survival masses starting at `phase`. -/
def survival (mass : ℕ → ℝ) (phase count : ℕ) : ℝ :=
  ∏ i ∈ range count, mass (phase + i)

/-- Survival-weighted reward accumulation over `count` stages from `phase`. -/
def accumulated (reward mass : ℕ → ℝ) (phase count : ℕ) : ℝ :=
  ∑ i ∈ range count, survival mass phase i * reward (phase + i)

variable {quitValue reward mass : ℕ → ℝ} {P : ℕ}

@[simp] theorem pureTimeValue_zero (phase : ℕ) :
    pureTimeValue quitValue reward mass 0 phase = quitValue phase := rfl

theorem pureTimeValue_succ (steps phase : ℕ) :
    pureTimeValue quitValue reward mass (steps + 1) phase =
      reward phase + mass phase *
        pureTimeValue quitValue reward mass steps (phase + 1) := rfl

@[simp] theorem survival_zero (phase : ℕ) : survival mass phase 0 = 1 := by
  simp [survival]

@[simp] theorem accumulated_zero (phase : ℕ) :
    accumulated reward mass phase 0 = 0 := by
  simp [accumulated]

theorem survival_succ' (phase count : ℕ) :
    survival mass phase (count + 1) = mass phase * survival mass (phase + 1) count := by
  unfold survival
  rw [prod_range_succ']
  simp only [Nat.add_zero]
  rw [mul_comm]
  congr 1
  apply prod_congr rfl
  intro i _
  congr 1
  omega

theorem survival_succ (phase count : ℕ) :
    survival mass phase (count + 1) =
      survival mass phase count * mass (phase + count) := by
  simp [survival, prod_range_succ]

theorem accumulated_succ' (phase count : ℕ) :
    accumulated reward mass phase (count + 1) =
      reward phase + mass phase * accumulated reward mass (phase + 1) count := by
  unfold accumulated
  rw [sum_range_succ']
  simp only [survival_zero, one_mul, Nat.add_zero, mul_sum]
  rw [add_comm]
  congr 1
  apply sum_congr rfl
  intro i _
  have harg : phase + (i + 1) = phase + 1 + i := by omega
  rw [survival_succ', harg, mul_assoc]

theorem accumulated_succ (phase count : ℕ) :
    accumulated reward mass phase (count + 1) =
      accumulated reward mass phase count +
        survival mass phase count * reward (phase + count) := by
  simp [accumulated, sum_range_succ]

theorem survival_nonneg (hmass : ∀ k, 0 ≤ mass k) (phase count : ℕ) :
    0 ≤ survival mass phase count :=
  prod_nonneg fun i _ => hmass (phase + i)

theorem survival_le_one (hmass0 : ∀ k, 0 ≤ mass k) (hmass1 : ∀ k, mass k ≤ 1)
    (phase count : ℕ) :
    survival mass phase count ≤ 1 :=
  prod_le_one (fun i _ => hmass0 (phase + i)) (fun i _ => hmass1 (phase + i))

/-- Splitting a pure quit time into a prefix and a remainder. -/
theorem pureTimeValue_add (count steps phase : ℕ) :
    pureTimeValue quitValue reward mass (count + steps) phase =
      accumulated reward mass phase count +
        survival mass phase count *
          pureTimeValue quitValue reward mass steps (phase + count) := by
  induction count generalizing phase with
  | zero => simp
  | succ count ih =>
      have hshift : count + 1 + steps = (count + steps) + 1 := by omega
      rw [hshift, pureTimeValue_succ, ih (phase + 1), accumulated_succ', survival_succ']
      have harg : phase + 1 + count = phase + (count + 1) := by omega
      rw [harg]
      ring

/-! ## Periodicity transport -/

theorem survival_phase_periodic (hmass : ∀ k, mass (k + P) = mass k)
    (phase count : ℕ) :
    survival mass (phase + P) count = survival mass phase count := by
  unfold survival
  apply prod_congr rfl
  intro i _
  have harg : phase + P + i = phase + i + P := by omega
  rw [harg, hmass]

theorem accumulated_phase_periodic (hreward : ∀ k, reward (k + P) = reward k)
    (hmass : ∀ k, mass (k + P) = mass k) (phase count : ℕ) :
    accumulated reward mass (phase + P) count =
      accumulated reward mass phase count := by
  unfold accumulated
  apply sum_congr rfl
  intro i _
  rw [survival_phase_periodic hmass]
  have harg : phase + P + i = phase + i + P := by omega
  rw [harg, hreward]

theorem pureTimeValue_phase_periodic (hquit : ∀ k, quitValue (k + P) = quitValue k)
    (hreward : ∀ k, reward (k + P) = reward k) (hmass : ∀ k, mass (k + P) = mass k)
    (steps phase : ℕ) :
    pureTimeValue quitValue reward mass steps (phase + P) =
      pureTimeValue quitValue reward mass steps phase := by
  induction steps generalizing phase with
  | zero => simpa using hquit phase
  | succ steps ih =>
      rw [pureTimeValue_succ, pureTimeValue_succ, hreward, hmass]
      have harg : phase + P + 1 = phase + 1 + P := by omega
      rw [harg, ih]

/-- The one-period survival product is the same at every phase. -/
theorem survival_full_period_shift (hmass : ∀ k, mass (k + P) = mass k) (phase : ℕ) :
    survival mass (phase + 1) P = survival mass phase P := by
  rcases Nat.eq_zero_or_pos P with hP | hP
  · simp [hP]
  · obtain ⟨Q, hQ⟩ : ∃ Q, P = Q + 1 := ⟨P - 1, by omega⟩
    subst hQ
    rw [survival_succ, survival_succ' (mass := mass) phase Q]
    have harg : phase + 1 + Q = phase + (Q + 1) := by omega
    rw [harg, hmass phase]
    ring

/-! ## The never value -/

/-- The value of never quitting: the one-period survival-weighted reward
accumulation, divided by one minus the one-period survival product. -/
noncomputable def neverValue (reward mass : ℕ → ℝ) (P phase : ℕ) : ℝ :=
  accumulated reward mass phase P / (1 - survival mass phase P)

/-- **Never-value balance.**  Under periodic data with a contracting
one-period survival product, the never value solves its affine continuation
equation at every phase. -/
theorem neverValue_balance (hreward : ∀ k, reward (k + P) = reward k)
    (hmass : ∀ k, mass (k + P) = mass k)
    (hcontract : ∀ phase, survival mass phase P < 1) (phase : ℕ) :
    neverValue reward mass P phase =
      reward phase + mass phase * neverValue reward mass P (phase + 1) := by
  rcases Nat.eq_zero_or_pos P with hP | hP
  · exfalso
    have hone := hcontract 0
    rw [hP] at hone
    simp at hone
  obtain ⟨Q, hQ⟩ : ∃ Q, P = Q + 1 := ⟨P - 1, by omega⟩
  have hS : survival mass (phase + 1) P = survival mass phase P :=
    survival_full_period_shift hmass phase
  have hSne : 1 - survival mass phase P ≠ 0 :=
    ne_of_gt (sub_pos.mpr (hcontract phase))
  have hfrontS : survival mass phase P =
      mass phase * survival mass (phase + 1) Q := by
    rw [hQ]; exact survival_succ' phase Q
  have hfrontA : accumulated reward mass phase P =
      reward phase + mass phase * accumulated reward mass (phase + 1) Q := by
    rw [hQ]; exact accumulated_succ' phase Q
  have hbackA : accumulated reward mass (phase + 1) P =
      accumulated reward mass (phase + 1) Q +
        survival mass (phase + 1) Q * reward phase := by
    rw [hQ, accumulated_succ]
    congr 1
    have harg : phase + 1 + Q = phase + P := by omega
    rw [harg, hreward]
  have hSne2 : 1 - mass phase * survival mass (phase + 1) Q ≠ 0 := by
    rw [← hfrontS]; exact hSne
  unfold neverValue
  rw [hS, hfrontA, hbackA, hfrontS]
  field_simp
  ring

/-- One-period unrolling: the never value is a fixed point of the one-period
affine accumulation. -/
theorem neverValue_period_unroll
    (hcontract : ∀ phase, survival mass phase P < 1) (phase : ℕ) :
    neverValue reward mass P phase =
      accumulated reward mass phase P +
        survival mass phase P * neverValue reward mass P phase := by
  have hSne : 1 - survival mass phase P ≠ 0 :=
    ne_of_gt (sub_pos.mpr (hcontract phase))
  unfold neverValue
  field_simp
  ring

/-! ## The selected periodic cap -/

/-- The selected periodic cap: the better of the first period's pure quit
times and the never value. -/
noncomputable def selectedCap (quitValue reward mass : ℕ → ℝ) (P phase : ℕ) : ℝ :=
  max
    ((range (P + 1)).sup' (range_succ_nonempty P)
      fun steps => pureTimeValue quitValue reward mass steps phase)
    (neverValue reward mass P phase)

theorem pureTimeValue_le_selectedCap_of_le (steps phase : ℕ) (hsteps : steps ≤ P) :
    pureTimeValue quitValue reward mass steps phase ≤
      selectedCap quitValue reward mass P phase :=
  le_trans
    (le_sup' (fun steps => pureTimeValue quitValue reward mass steps phase)
      (mem_range.mpr (by omega)))
    (le_max_left _ _)

theorem neverValue_le_selectedCap (phase : ℕ) :
    neverValue reward mass P phase ≤ selectedCap quitValue reward mass P phase :=
  le_max_right _ _

/-- **Deterministic domination.**  Every pure quit time is dominated by the
selected periodic cap. -/
theorem pureTimeValue_le_selectedCap (hquit : ∀ k, quitValue (k + P) = quitValue k)
    (hreward : ∀ k, reward (k + P) = reward k) (hmass : ∀ k, mass (k + P) = mass k)
    (hmass0 : ∀ k, 0 ≤ mass k) (hmass1 : ∀ k, mass k ≤ 1)
    (hcontract : ∀ phase, survival mass phase P < 1)
    (steps phase : ℕ) :
    pureTimeValue quitValue reward mass steps phase ≤
      selectedCap quitValue reward mass P phase := by
  induction steps using Nat.strong_induction_on with
  | _ steps ih =>
      by_cases hsmall : steps ≤ P
      · exact pureTimeValue_le_selectedCap_of_le steps phase hsmall
      · have hP : 0 < P := by
          by_contra hzero
          have hzero' : P = 0 := by omega
          have hone := hcontract 0
          rw [hzero'] at hone
          simp at hone
        obtain ⟨tail, htail⟩ : ∃ tail, steps = P + tail := ⟨steps - P, by omega⟩
        subst htail
        have htailLt : tail < P + tail := by omega
        rw [pureTimeValue_add, pureTimeValue_phase_periodic hquit hreward hmass]
        have hihTail := ih tail htailLt
        have hunroll := neverValue_period_unroll
          (reward := reward) hcontract phase
        have hnever := neverValue_le_selectedCap
          (quitValue := quitValue) (reward := reward) (mass := mass)
          (P := P) (phase := phase)
        have hsurv0 := survival_nonneg hmass0 phase P
        have hsurv1 := survival_le_one hmass0 hmass1 phase P
        nlinarith [mul_nonneg hsurv0 (sub_nonneg.mpr hihTail),
          mul_nonneg (sub_nonneg.mpr hsurv1) (sub_nonneg.mpr hnever)]

/-- The selected cap is attained by a pure time in the first period or by
never quitting. -/
theorem selectedCap_attained (phase : ℕ) :
    (∃ steps, steps ≤ P ∧ selectedCap quitValue reward mass P phase =
        pureTimeValue quitValue reward mass steps phase) ∨
      selectedCap quitValue reward mass P phase =
        neverValue reward mass P phase := by
  obtain ⟨steps, hmem, hsup⟩ := exists_mem_eq_sup' (range_succ_nonempty P)
    (fun steps => pureTimeValue quitValue reward mass steps phase)
  rcases le_total (neverValue reward mass P phase)
      ((range (P + 1)).sup' (range_succ_nonempty P)
        fun steps => pureTimeValue quitValue reward mass steps phase) with hle | hle
  · left
    refine ⟨steps, ?_, ?_⟩
    · have := mem_range.mp hmem
      omega
    · rw [selectedCap, max_eq_left hle, hsup]
  · right
    rw [selectedCap, max_eq_right hle]

/-- **The cyclic Snell equation.**  Under periodic contracting data, the
selected periodic cap satisfies its one-step Bellman identity. -/
theorem selectedCap_bellman (hquit : ∀ k, quitValue (k + P) = quitValue k)
    (hreward : ∀ k, reward (k + P) = reward k) (hmass : ∀ k, mass (k + P) = mass k)
    (hmass0 : ∀ k, 0 ≤ mass k) (hmass1 : ∀ k, mass k ≤ 1)
    (hcontract : ∀ phase, survival mass phase P < 1) (phase : ℕ) :
    selectedCap quitValue reward mass P phase =
      max (quitValue phase)
        (reward phase + mass phase *
          selectedCap quitValue reward mass P (phase + 1)) := by
  apply le_antisymm
  · rcases selectedCap_attained (quitValue := quitValue) (reward := reward)
        (mass := mass) (P := P) (phase := phase) with
      ⟨steps, hsteps, hval⟩ | hval
    · rw [hval]
      cases steps with
      | zero => simp
      | succ steps =>
          rw [pureTimeValue_succ]
          refine le_max_of_le_right ?_
          have hbound := pureTimeValue_le_selectedCap hquit hreward hmass hmass0
            hmass1 hcontract steps (phase + 1)
          have hscaled := mul_le_mul_of_nonneg_left hbound (hmass0 phase)
          linarith
    · rw [hval, neverValue_balance hreward hmass hcontract phase]
      refine le_max_of_le_right ?_
      have hbound := neverValue_le_selectedCap (quitValue := quitValue)
        (reward := reward) (mass := mass) (P := P) (phase := phase + 1)
      have hscaled := mul_le_mul_of_nonneg_left hbound (hmass0 phase)
      linarith
  · apply max_le
    · simpa using
        pureTimeValue_le_selectedCap_of_le (quitValue := quitValue)
          (reward := reward) (mass := mass) 0 phase (Nat.zero_le P)
    · rcases selectedCap_attained (quitValue := quitValue) (reward := reward)
          (mass := mass) (P := P) (phase := phase + 1) with
        ⟨steps, hsteps, hval⟩ | hval
      · rw [hval, ← pureTimeValue_succ]
        exact pureTimeValue_le_selectedCap hquit hreward hmass hmass0 hmass1
          hcontract (steps + 1) phase
      · rw [hval, ← neverValue_balance hreward hmass hcontract phase]
        exact neverValue_le_selectedCap (quitValue := quitValue)
          (reward := reward) (mass := mass) (P := P) (phase := phase)

/-- The selected cap is periodic in the phase. -/
theorem selectedCap_phase_periodic (hquit : ∀ k, quitValue (k + P) = quitValue k)
    (hreward : ∀ k, reward (k + P) = reward k) (hmass : ∀ k, mass (k + P) = mass k)
    (phase : ℕ) :
    selectedCap quitValue reward mass P (phase + P) =
      selectedCap quitValue reward mass P phase := by
  unfold selectedCap neverValue
  rw [survival_phase_periodic hmass, accumulated_phase_periodic hreward hmass]
  congr 1
  apply sup'_congr _ rfl
  intro steps _
  exact pureTimeValue_phase_periodic hquit hreward hmass steps phase

end Math.PeriodicSnell

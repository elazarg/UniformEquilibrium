/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
# Quantitative subsequences with a fixed finite label

Two elementary sequence facts used by finite-label localization arguments.
An asymptotic lower bound on a finite sum can be frozen to one label along a
strict subsequence.  A fixed positive lower bound along such a subsequence
prevents convergence to zero.
-/

namespace Math

open Filter
open scoped Topology

/-- A nonnegative real sequence that does not tend to zero has a fixed
positive lower bound frequently along `atTop`. -/
theorem exists_pos_frequently_ge_of_nonneg_of_not_tendsto_zero
    (value : ℕ → ℝ) (hnonneg : ∀ n, 0 ≤ value n)
    (hnot : ¬Tendsto value atTop (nhds 0)) :
    ∃ lower, 0 < lower ∧ ∃ᶠ n in atTop, lower ≤ value n := by
  by_contra hnone
  push Not at hnone
  apply hnot
  rw [tendsto_order]
  constructor
  · intro lower hlower
    exact Eventually.of_forall fun n => hlower.trans_le (hnonneg n)
  · intro upper hupper
    exact hnone upper hupper

/-- If a finite sum is bounded below by a positive floor up to an error
converging to zero, one fixed label carries at least half the average along a
strict subsequence.  Nonemptiness of `labels` is a consequence, not a premise.
-/
theorem exists_fixed_mem_subsequence_of_sum_lower_and_error_tendsto_zero
    {alpha : Type*} [DecidableEq alpha]
    (labels : Finset alpha) (value : Nat -> alpha -> Real)
    (error : Nat -> Real) (floor : Real)
    (hfloor : 0 < floor)
    (herror : Tendsto error atTop (nhds 0))
    (hlower : ∀ n,
      floor - error n <= Finset.sum labels (value n)) :
    ∃ label, label ∈ labels ∧ ∃ subseq : Nat -> Nat,
      StrictMono subseq ∧ ∀ n,
        floor / (2 * (labels.card : Real)) <= value (subseq n) label := by
  have hsmall : ∀ᶠ n in atTop, error n < floor / 2 :=
    herror.eventually (Iio_mem_nhds (half_pos hfloor))
  have hpositiveSum : ∀ᶠ n in atTop,
      floor / 2 < Finset.sum labels (value n) := by
    filter_upwards [hsmall] with n hn
    linarith [hlower n]
  have hlabels : labels.Nonempty := by
    obtain ⟨n, hn⟩ := hpositiveSum.exists
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty, Finset.sum_empty] at hn
    linarith
  have hcard : 0 < (labels.card : Real) := by
    exact_mod_cast Finset.card_pos.mpr hlabels
  have hwitness : ∀ᶠ n in atTop, ∃ label ∈ labels,
      floor / (2 * (labels.card : Real)) <= value n label := by
    filter_upwards [hpositiveSum] with n hn
    have haverageSum :
        Finset.sum labels
            (fun _ => floor / (2 * (labels.card : Real))) <=
          Finset.sum labels (value n) := by
      have heq : Finset.sum labels
          (fun _ => floor / (2 * (labels.card : Real))) = floor / 2 := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        field_simp
      linarith
    exact Finset.exists_le_of_sum_le hlabels haverageSum
  have hfrequent : ∃ᶠ n in atTop, ∃ label ∈ labels,
      floor / (2 * (labels.card : Real)) <= value n label :=
    hwitness.frequently
  rw [labels.frequently_exists] at hfrequent
  obtain ⟨label, hlabel, hlabelFrequent⟩ := hfrequent
  obtain ⟨subseq, hsubseq, hvalue⟩ :=
    extraction_of_frequently_atTop hlabelFrequent
  exact ⟨label, hlabel, subseq, hsubseq, hvalue⟩

/-- A fixed positive lower bound along a strict subsequence prevents a real
sequence from converging to zero. -/
theorem not_tendsto_zero_of_positive_lower_bound_on_strict_subsequence
    (value : Nat -> Real) (subseq : Nat -> Nat) (lower : Real)
    (hsubseq : StrictMono subseq) (hlower : 0 < lower)
    (hbound : ∀ n, lower <= value (subseq n)) :
    ¬ Tendsto value atTop (nhds 0) := by
  intro htendsto
  have hcomp : Tendsto (fun n => value (subseq n)) atTop (nhds 0) :=
    htendsto.comp hsubseq.tendsto_atTop
  have hsmall : ∀ᶠ n in atTop, value (subseq n) < lower :=
    hcomp.eventually (Iio_mem_nhds hlower)
  obtain ⟨n, hn⟩ := hsmall.exists
  exact (not_lt_of_ge (hbound n)) hn

/-- Every sequence in a finite type is constant along one strict
subsequence. -/
theorem exists_fixed_label_on_strictMono_subsequence
    {Label : Type} [Fintype Label] (label : ℕ → Label) :
    ∃ fixed : Label, ∃ subsequence : ℕ → ℕ,
      StrictMono subsequence ∧
        ∀ rank, label (subsequence rank) = fixed := by
  classical
  have hfrequent : ∃ fixed : Label, ∃ᶠ rank in atTop,
      label rank = fixed := by
    by_contra hnone
    push Not at hnone
    have hall : ∀ᶠ rank in atTop, ∀ fixed : Label,
        label rank ≠ fixed := by
      rw [eventually_all]
      exact hnone
    obtain ⟨rank, hrank⟩ := hall.exists
    exact hrank (label rank) rfl
  obtain ⟨fixed, hfixed⟩ := hfrequent
  obtain ⟨subsequence, hmono, hlabel⟩ :=
    extraction_of_frequently_atTop hfixed
  exact ⟨fixed, subsequence, hmono, hlabel⟩

end Math

/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.AbelCesaro
import MathUE.SurvivalProduct

/-!
# Generic diagonal discounted backward recursions

This file contains the game-independent accounting behind a diagonal
backward recursion.  It deliberately does not construct any game roots or
identify any one-step defects: those are inputs to these lemmas.
-/

noncomputable section

open scoped BigOperators

namespace Math

/-! ## Finite Abel shadowing -/

/-- The largest absolute prefix sum among the first `length` terms of `g`.

The extra zero-length prefix makes the definition total and convenient for
Abel summation. -/
def prefixAbsMax (g : ℕ → ℝ) (start length : ℕ) : ℝ :=
  (Finset.range (length + 1)).sup'
    ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ length)⟩
    (fun count ↦ |∑ offset ∈ Finset.range count, g (start + offset)|)

theorem abs_prefixSum_le_prefixAbsMax
    (g : ℕ → ℝ) (start length count : ℕ) (hcount : count ≤ length) :
    |∑ offset ∈ Finset.range count, g (start + offset)| ≤
      prefixAbsMax g start length := by
  unfold prefixAbsMax
  apply Finset.le_sup' (f := fun count ↦
    |∑ offset ∈ Finset.range count, g (start + offset)|)
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le hcount)

theorem prefixSum_le_prefixAbsMax
    (g : ℕ → ℝ) (start length count : ℕ) (hcount : count ≤ length) :
    ∑ offset ∈ Finset.range count, g (start + offset) ≤
      prefixAbsMax g start length :=
  (le_abs_self _).trans (abs_prefixSum_le_prefixAbsMax g start length count hcount)

theorem neg_prefixSum_le_prefixAbsMax
    (g : ℕ → ℝ) (start length count : ℕ) (hcount : count ≤ length) :
    -∑ offset ∈ Finset.range count, g (start + offset) ≤
      prefixAbsMax g start length := by
  calc
    -∑ offset ∈ Finset.range count, g (start + offset) ≤
        |-∑ offset ∈ Finset.range count, g (start + offset)| := le_abs_self _
    _ = |∑ offset ∈ Finset.range count, g (start + offset)| := by rw [abs_neg]
    _ ≤ prefixAbsMax g start length :=
      abs_prefixSum_le_prefixAbsMax g start length count hcount

private theorem weighted_sum_abs_le_prefixAbsMax
    (g discount : ℕ → ℝ) (start length : ℕ)
    (hdiscount0 : ∀ time, 0 ≤ discount time)
    (hdiscount1 : ∀ time, discount time ≤ 1) :
    |∑ offset ∈ Finset.range length,
        survivalProduct discount start offset * g (start + offset)| ≤
      prefixAbsMax g start length := by
  let weight : ℕ → ℝ := fun offset ↦ survivalProduct discount start offset
  let summand : ℕ → ℝ := fun offset ↦ g (start + offset)
  have hweight0 : ∀ offset, 0 ≤ weight offset := by
    intro offset
    exact survivalProduct_nonneg discount hdiscount0 start offset
  have hweight1 : ∀ offset, weight (offset + 1) ≤ weight offset := by
    intro offset
    dsimp only [weight]
    rw [survivalProduct_succ]
    exact (mul_le_mul_of_nonneg_left
      (hdiscount1 (start + offset)) (survivalProduct_nonneg discount
        hdiscount0 start offset)).trans_eq
      (by simp)
  have hpositive :
      ∑ offset ∈ Finset.range length, weight offset * summand offset ≤
        prefixAbsMax g start length := by
    have h := MathUE.sum_mul_le_initialWeight_mul_of_partialSum_le
      (weight := weight) (summand := summand) (ε := prefixAbsMax g start length)
      length hweight1 (hweight0 length)
        (fun index hindex ↦ prefixSum_le_prefixAbsMax g start length index hindex)
    simpa [weight, survivalProduct] using h
  have hnegative :
      ∑ offset ∈ Finset.range length, weight offset * (-summand offset) ≤
        prefixAbsMax g start length := by
    have h := MathUE.sum_mul_le_initialWeight_mul_of_partialSum_le
      (weight := weight) (summand := fun index ↦ -summand index)
      (ε := prefixAbsMax g start length) length hweight1 (hweight0 length)
        (fun index hindex ↦ by
          dsimp only [summand]
          simpa only [Finset.sum_neg_distrib] using
            (neg_prefixSum_le_prefixAbsMax g start length index hindex))
    simpa [weight, survivalProduct] using h
  rw [abs_le]
  constructor
  · have hnegative' :
        -∑ offset ∈ Finset.range length, weight offset * summand offset ≤
          prefixAbsMax g start length := by
      have hrewrite :
          (∑ offset ∈ Finset.range length, weight offset * (-summand offset)) =
            -∑ offset ∈ Finset.range length, weight offset * summand offset := by
        calc
          (∑ offset ∈ Finset.range length,
              weight offset * (-summand offset)) =
              ∑ offset ∈ Finset.range length,
                -(weight offset * summand offset) := by
            apply Finset.sum_congr rfl
            intro offset hoffset
            ring
          _ = -∑ offset ∈ Finset.range length,
              weight offset * summand offset := Finset.sum_neg_distrib _
      rw [← hrewrite]
      exact hnegative
    have hnegative'' :
        -prefixAbsMax g start length ≤
          ∑ offset ∈ Finset.range length, weight offset * summand offset := by
      linarith [hnegative']
    simpa [weight, summand] using hnegative''
  · exact hpositive

theorem abs_discrepancy_le_prefix_max_add_terminal
    (g discount e : ℕ → ℝ) (start length : ℕ)
    (hrec : ∀ offset, offset < length →
      e (start + offset) =
        g (start + offset) + discount (start + offset) * e (start + offset + 1))
    (hdiscount0 : ∀ time, 0 ≤ discount time)
    (hdiscount1 : ∀ time, discount time ≤ 1) :
    |e start| ≤
      prefixAbsMax g start length +
        survivalProduct discount start length * |e (start + length)| := by
  have hunroll :
      e start =
        (∑ offset ∈ Finset.range length,
          survivalProduct discount start offset * g (start + offset)) +
          survivalProduct discount start length * e (start + length) := by
    induction length generalizing start with
    | zero => simp [survivalProduct]
    | succ length ih =>
        have hrec0 := hrec 0 (by omega)
        have htail := ih (start + 1) (fun offset hoffset ↦ by
          have h := hrec (offset + 1) (by omega)
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h)
        have hshift :
            (∑ offset ∈ Finset.range length,
              survivalProduct discount start (offset + 1) *
                g (start + (offset + 1))) =
              discount start *
                (∑ offset ∈ Finset.range length,
                  survivalProduct discount (start + 1) offset *
                    g (start + 1 + offset)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro offset hoffset
          rw [survivalProduct_succ_left]
          have hindex : start + (offset + 1) = start + 1 + offset := by omega
          rw [hindex]
          ring
        have hsum :
            (∑ offset ∈ Finset.range (length + 1),
              survivalProduct discount start offset * g (start + offset)) +
                survivalProduct discount start (length + 1) *
                  e (start + (length + 1)) =
              g start + discount start *
                ((∑ offset ∈ Finset.range length,
                  survivalProduct discount (start + 1) offset *
                    g (start + 1 + offset)) +
                  survivalProduct discount (start + 1) length *
                    e (start + 1 + length)) := by
          rw [Finset.sum_range_succ', survivalProduct_zero, hshift,
            survivalProduct_succ_left]
          ring_nf
        rw [show e start =
            g start + discount start * e (start + 1) by simpa using hrec0,
          htail, ← hsum]
  calc
    |e start| =
        |(∑ offset ∈ Finset.range length,
            survivalProduct discount start offset * g (start + offset)) +
          survivalProduct discount start length * e (start + length)| :=
      congrArg abs hunroll
    _ ≤ |∑ offset ∈ Finset.range length,
          survivalProduct discount start offset * g (start + offset)| +
        survivalProduct discount start length * |e (start + length)| := by
      calc
        _ ≤ |∑ offset ∈ Finset.range length,
              survivalProduct discount start offset * g (start + offset)| +
            |survivalProduct discount start length * e (start + length)| :=
          abs_add_le _ _
        _ = |∑ offset ∈ Finset.range length,
              survivalProduct discount start offset * g (start + offset)| +
            survivalProduct discount start length * |e (start + length)| := by
          rw [abs_mul, abs_of_nonneg
            (survivalProduct_nonneg discount hdiscount0 start length)]
    _ ≤ prefixAbsMax g start length +
        survivalProduct discount start length * |e (start + length)| := by
      exact add_le_add_left
        (weighted_sum_abs_le_prefixAbsMax g discount start length
          hdiscount0 hdiscount1) _

/-- A homogeneous exact difference is bounded by its tail survival product.

This is the reusable uniqueness/shadowing estimate for any coordinate whose
one-step secant coefficient is nonnegative and at most the stated discount. -/
theorem abs_exact_difference_le_survival_product_mul_terminal
    (difference discount : ℕ → ℝ) (start length : ℕ)
    (hstep : ∀ offset,
      |difference (start + offset)| ≤
        discount (start + offset) * |difference (start + offset + 1)|)
    (hdiscount0 : ∀ time, 0 ≤ discount time) :
    |difference start| ≤
      survivalProduct discount start length *
        |difference (start + length)| := by
  induction length generalizing start with
  | zero => simp [survivalProduct]
  | succ length ih =>
      calc
        |difference start| ≤
            discount start * |difference (start + 1)| := by
          simpa using hstep 0
        _ ≤ discount start *
            (survivalProduct discount (start + 1) length *
              |difference (start + 1 + length)|) := by
          apply mul_le_mul_of_nonneg_left _ (hdiscount0 start)
          exact ih (start + 1) (fun offset ↦ by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              hstep (offset + 1))
        _ = survivalProduct discount start (length + 1) *
            |difference (start + (length + 1))| := by
          rw [survivalProduct_succ_left]
          simp only [Nat.add_comm, Nat.add_left_comm]
          ring

/-! ## Summable block accounting -/

def blockTailBound (prefixVariation seamVariation : ℕ → ℝ) (block : ℕ) : ℝ :=
  2 * prefixVariation block +
    ∑' later, (if block < later then prefixVariation later else 0) +
    ∑' later, (if block ≤ later then seamVariation later else 0)

theorem finite_blockTailBound_le
    (prefixVariation seamVariation : ℕ → ℝ)
    (hprefix0 : ∀ block, 0 ≤ prefixVariation block)
    (hseam0 : ∀ block, 0 ≤ seamVariation block)
    (hprefix : Summable prefixVariation)
    (hseam : Summable seamVariation)
    (block horizon : ℕ) :
    2 * prefixVariation block +
        (∑ later ∈ Finset.Ioc block horizon, prefixVariation later) +
        (∑ later ∈ Finset.Icc block horizon, seamVariation later) ≤
      blockTailBound prefixVariation seamVariation block := by
  unfold blockTailBound
  have hprefixFilter : Summable (fun later ↦
      if block < later then prefixVariation later else 0) := by
    have heq : (fun later ↦
        if block < later then prefixVariation later else 0) =
        (Set.Ioi block).indicator prefixVariation := by
      funext later
      by_cases hlater : block < later <;> simp [Set.indicator, hlater]
    rw [heq]
    exact hprefix.indicator (Set.Ioi block)
  have hseamFilter : Summable (fun later ↦
      if block ≤ later then seamVariation later else 0) := by
    have heq : (fun later ↦
        if block ≤ later then seamVariation later else 0) =
        (Set.Ici block).indicator seamVariation := by
      funext later
      by_cases hlater : block ≤ later <;> simp [Set.indicator, hlater]
    rw [heq]
    exact hseam.indicator (Set.Ici block)
  have hprefixFinite :
      (∑ later ∈ Finset.Ioc block horizon, prefixVariation later) ≤
        ∑' later, (if block < later then prefixVariation later else 0) := by
    have hEq :
        (∑ later ∈ Finset.Ioc block horizon, prefixVariation later) =
          ∑ later ∈ Finset.Ioc block horizon,
            (if block < later then prefixVariation later else 0) := by
      apply Finset.sum_congr rfl
      intro later hlater
      simp only [Finset.mem_Ioc] at hlater
      simp [hlater.1]
    rw [hEq]
    apply hprefixFilter.sum_le_tsum
    intro later hlater
    by_cases h : block < later <;> simp [h, hprefix0]
  have hseamFinite :
      (∑ later ∈ Finset.Icc block horizon, seamVariation later) ≤
        ∑' later, (if block ≤ later then seamVariation later else 0) := by
    have hEq :
        (∑ later ∈ Finset.Icc block horizon, seamVariation later) =
          ∑ later ∈ Finset.Icc block horizon,
            (if block ≤ later then seamVariation later else 0) := by
      apply Finset.sum_congr rfl
      intro later hlater
      simp only [Finset.mem_Icc] at hlater
      simp [hlater.1]
    rw [hEq]
    apply hseamFilter.sum_le_tsum
    intro later hlater
    by_cases h : block ≤ later <;> simp [h, hseam0]
  linarith

end Math

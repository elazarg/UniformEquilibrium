/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Analysis.PSeries

/-!
# Summability tests for calendar error budgets

These two game-independent tests connect harmonic-scale pointwise lower
bounds and normalized cumulative calendar bills to ordinary summability.
-/

noncomputable section

namespace Math
namespace CalendarSummability

open Filter

/-- A nonnegative error cannot be summable if it remains at least a positive
multiple of the reciprocal calendar time.  The formulation below derives
that comparison from a positive product lower bound and a scale negligible
relative to calendar time. -/
theorem not_summable_of_eventually_pos_le_mul_of_inv_mul_tendsto_zero
    (a e : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (he0 : ∀ n, 0 ≤ e n)
    (hlower : ∀ᶠ n in atTop, c ≤ a n * e n)
    (hscale : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * a n)
      atTop (nhds 0)) :
    ¬ Summable e := by
  intro he
  have hscaleOne : ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ * a n < 1 := by
    have hclose := hscale.eventually (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)
    filter_upwards [hclose] with n hn
    rw [Real.dist_eq, sub_zero, abs_lt] at hn
    exact hn.2
  have hcompare : ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ)⁻¹ ≤ e n := by
    filter_upwards [hlower, hscaleOne, eventually_gt_atTop 0] with n hn hsmall hnpos
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hane : a n ≤ n := by
      have hlt : a n < (n : ℝ) := by
        simpa only [mul_one] using (inv_mul_lt_iff₀ hnreal).mp hsmall
      exact hlt.le
    have hmul : a n * e n ≤ (n : ℝ) * e n :=
      mul_le_mul_of_nonneg_right hane (he0 n)
    have hdiv : c / (n : ℝ) ≤ e n :=
      (div_le_iff₀ hnreal).2 (by
        simpa only [mul_comm] using hn.trans hmul)
    simpa only [div_eq_mul_inv] using hdiv
  have hharmonic : Summable (fun n : ℕ => c * (n : ℝ)⁻¹) := by
    apply Summable.of_norm_bounded_eventually_nat he
    filter_upwards [hcompare] with n hn
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg hc.le (inv_nonneg.mpr (Nat.cast_nonneg n)))]
    exact hn
  have honeDiv : Summable (fun n : ℕ => (n : ℝ)⁻¹) := by
    have hscaled := hharmonic.mul_left c⁻¹
    simpa only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using hscaled
  exact Real.not_summable_natCast_inv honeDiv

/-- For nonnegative errors, a bounded normalized sum of cumulative prefix
errors already forces summability of the original errors.  Thus the nested
drift bill used by calendar verification is not weaker than summable drift. -/
theorem summable_of_eventually_normalized_cumulative_sum_le
    (e : ℕ → ℝ) (he0 : ∀ n, 0 ≤ e n) (C : ℝ)
    (hbound : ∀ᶠ T : ℕ in atTop,
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        ∑ k ∈ Finset.range t, e k ≤ C) :
    Summable e := by
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 hbound
  apply summable_of_sum_range_le (c := 2 * C) he0
  intro N
  let T := max T₀ (2 * N + 2)
  have hT₀T : T₀ ≤ T := le_max_left _ _
  have htwo : 2 * N + 2 ≤ T := le_max_right _ _
  have hNT : N ≤ T := by omega
  have hTpos : 0 < T := by omega
  let P : ℝ := ∑ k ∈ Finset.range N, e k
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun k hk => he0 k
  have hinner : ∀ t ∈ Finset.Ico N T, P ≤
      ∑ k ∈ Finset.range t, e k := by
    intro t ht
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (Finset.mem_Ico.mp ht).1)
    intro k hk hnot
    exact he0 k
  have hIcoSubset : Finset.Ico N T ⊆ Finset.range T := by
    intro t ht
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp ht).2
  have houter : ((T - N : ℕ) : ℝ) * P ≤
      ∑ t ∈ Finset.range T, ∑ k ∈ Finset.range t, e k := by
    calc
      ((T - N : ℕ) : ℝ) * P = ∑ _t ∈ Finset.Ico N T, P := by
        simp [Nat.card_Ico, hNT]
      _ ≤ ∑ t ∈ Finset.Ico N T, ∑ k ∈ Finset.range t, e k :=
        Finset.sum_le_sum hinner
      _ ≤ ∑ t ∈ Finset.range T, ∑ k ∈ Finset.range t, e k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hIcoSubset
        intro t ht hnot
        exact Finset.sum_nonneg fun k hk => he0 k
  have hbill := hT₀ T hT₀T
  have hweighted : (T : ℝ)⁻¹ * (((T - N : ℕ) : ℝ) * P) ≤ C :=
    (mul_le_mul_of_nonneg_left houter
      (inv_nonneg.mpr (Nat.cast_nonneg T))).trans hbill
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hTpos
  have hratio : (1 / 2 : ℝ) ≤ ((T - N : ℕ) : ℝ) / T := by
    apply (le_div_iff₀ hTreal).2
    rw [Nat.cast_sub hNT]
    have hcast : (2 : ℝ) * N ≤ T := by exact_mod_cast (by omega : 2 * N ≤ T)
    linarith
  have hhalf : (1 / 2 : ℝ) * P ≤ C := by
    calc
      (1 / 2 : ℝ) * P ≤
          (((T - N : ℕ) : ℝ) / T) * P :=
        mul_le_mul_of_nonneg_right hratio hP0
      _ = (T : ℝ)⁻¹ * (((T - N : ℕ) : ℝ) * P) := by
        rw [div_eq_mul_inv]
        ring
      _ ≤ C := hweighted
  dsimp only [P] at hhalf ⊢
  linarith


end CalendarSummability
end Math

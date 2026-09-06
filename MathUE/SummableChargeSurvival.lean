/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import MathUE.DivergentChargeRecurrence

/-!
# Positive survival under a summable strict charge

A summable sequence of hazards in `[0,1)` has finite survival products bounded
uniformly away from zero.  This is the elementary positive-product direction
complementary to the nonsummable survival-collapse results in
`MathUE.DivergentChargeRecurrence`.
-/

noncomputable section

namespace Math

open Filter

/-- Summable strict unit-interval hazards leave a uniformly positive finite
prefix survival probability. -/
theorem exists_pos_le_prod_one_sub_of_summable
    (charge : Nat -> Real)
    (hcharge0 : forall time, 0 <= charge time)
    (hcharge1 : forall time, charge time < 1)
    (hsummable : Summable charge) :
    exists lower : Real, 0 < lower ∧
      forall horizon,
        lower <= ∏ time ∈ Finset.range horizon, (1 - charge time) := by
  have htail : Tendsto (fun start : Nat =>
      ∑' offset : Nat, charge (offset + start)) atTop (nhds 0) :=
    tendsto_sum_nat_add charge
  have heventually : ∀ᶠ start : Nat in atTop,
      (∑' offset : Nat, charge (offset + start)) < (1 / 2 : Real) :=
    htail.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨start, hstart⟩ := heventually.exists
  let initialProduct := ∏ time ∈ Finset.range start, (1 - charge time)
  have hinitialProductPos : 0 < initialProduct := by
    dsimp only [initialProduct]
    exact Finset.prod_pos fun time _ => sub_pos.mpr (hcharge1 time)
  refine ⟨initialProduct / 2, by positivity, ?_⟩
  intro horizon
  by_cases hhorizon : horizon <= start
  · have hinitialProductLe : initialProduct <=
        ∏ time ∈ Finset.range horizon, (1 - charge time) := by
      let fuel := start - horizon
      have hstart : horizon + fuel = start := by
        dsimp only [fuel]
        omega
      have htailNonneg : 0 <=
          ∏ offset ∈ Finset.range fuel,
            (1 - charge (horizon + offset)) :=
        Finset.prod_nonneg fun offset _ =>
          (sub_nonneg.mpr (hcharge1 (horizon + offset)).le)
      have htailLeOne :
          (∏ offset ∈ Finset.range fuel,
            (1 - charge (horizon + offset))) <= 1 :=
        Finset.prod_le_one
          (fun offset _ => sub_nonneg.mpr
            (hcharge1 (horizon + offset)).le)
          (fun offset _ => by linarith [hcharge0 (horizon + offset)])
      have hsplit := Finset.prod_range_add
        (fun time => 1 - charge time) horizon fuel
      rw [hstart] at hsplit
      rw [show initialProduct =
        (∏ time ∈ Finset.range horizon, (1 - charge time)) *
          ∏ offset ∈ Finset.range fuel,
            (1 - charge (horizon + offset)) by
              simpa [initialProduct, Nat.add_comm] using hsplit]
      exact mul_le_of_le_one_right
        (Finset.prod_nonneg fun time _ =>
          sub_nonneg.mpr (hcharge1 time).le)
        htailLeOne
    linarith
  · have hstartLe : start <= horizon := Nat.le_of_not_ge hhorizon
    let fuel := horizon - start
    have hhorizonEq : start + fuel = horizon := by
      dsimp only [fuel]
      omega
    have hsuffix : Summable (fun offset => charge (start + offset)) := by
      have hshift : Summable (fun offset => charge (offset + start)) :=
        (summable_nat_add_iff start).2 hsummable
      simpa [Nat.add_comm] using hshift
    have hfiniteTail :
        (∑ offset ∈ Finset.range fuel, charge (start + offset)) <=
          ∑' offset : Nat, charge (start + offset) :=
      hsuffix.sum_le_tsum (Finset.range fuel) fun offset _ =>
        hcharge0 (start + offset)
    have htailRewrite :
        (∑' offset : Nat, charge (start + offset)) =
          ∑' offset : Nat, charge (offset + start) := by
      congr 1
      funext offset
      rw [Nat.add_comm]
    rw [htailRewrite] at hfiniteTail
    have htailLower : (1 / 2 : Real) <=
        ∏ offset ∈ Finset.range fuel,
          (1 - charge (start + offset)) := by
      have hunion := one_sub_sum_range_le_prod_one_sub
        charge hcharge0 (fun time => (hcharge1 time).le) start fuel
      linarith
    have hsplit := Finset.prod_range_add
      (fun time => 1 - charge time) start fuel
    rw [hhorizonEq] at hsplit
    rw [show (∏ time ∈ Finset.range horizon, (1 - charge time)) =
      initialProduct * ∏ offset ∈ Finset.range fuel,
        (1 - charge (start + offset)) by
          simpa [initialProduct, Nat.add_comm] using hsplit]
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ hinitialProductPos.le
    simpa using htailLower

/-- A summable unit-interval charge has uniformly near-one survival on every
sufficiently late finite window. -/
theorem eventually_one_sub_le_finiteSurvivalWindow_of_summable
    (charge : ℕ → ℝ) (hcharge0 : ∀ n, 0 ≤ charge n)
    (hcharge1 : ∀ n, charge n ≤ 1) (hsummable : Summable charge)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ start in atTop, ∀ fuel,
      1 - ε ≤ ∏ offset ∈ Finset.range fuel,
        (1 - charge (start + offset)) := by
  have htail : Tendsto (fun start : ℕ =>
      ∑' offset : ℕ, charge (offset + start)) atTop (nhds 0) :=
    tendsto_sum_nat_add charge
  filter_upwards [htail.eventually (Iio_mem_nhds hε)] with start hstart
  intro fuel
  have hsuffix : Summable (fun offset => charge (start + offset)) := by
    simpa [Nat.add_comm] using (summable_nat_add_iff start).2 hsummable
  have hfinite :
      (∑ offset ∈ Finset.range fuel, charge (start + offset)) ≤
        ∑' offset, charge (start + offset) :=
    hsuffix.sum_le_tsum (Finset.range fuel) fun offset _ =>
      hcharge0 (start + offset)
  have hrewrite : (∑' offset, charge (start + offset)) =
      ∑' offset, charge (offset + start) := by
    congr 1
    funext offset
    rw [Nat.add_comm]
  rw [hrewrite] at hfinite
  exact (by linarith : 1 - ε ≤
    1 - ∑ offset ∈ Finset.range fuel, charge (start + offset)) |>.trans
      (one_sub_sum_range_le_prod_one_sub
        charge hcharge0 hcharge1 start fuel)

end Math

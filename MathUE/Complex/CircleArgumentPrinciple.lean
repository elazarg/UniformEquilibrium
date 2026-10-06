/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache-2.0; see LICENSES/APACHE_2_0.txt.
Authors: Yury Kudryashov

Adapted from the circle log-derivative multiplicity formula in
https://github.com/urkud/mathlib4/tree/d43061d911b1aeae0788591da437a3b115098962
under Mathlib/Analysis/Complex/RiemannMapping.lean (PR33505).
-/
module

public import MathUE.Analysis.AnalyticCompactZeroFactorization
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.LogDeriv

/-! # The argument principle on a complex circle

For a function analytic near a closed disk and nonzero on its boundary,
the circle integral of its logarithmic derivative counts the actual analytic
orders of its zeros in the disk. The finite-zero factorization is constructed
from the function; no zero census or winding-number oracle is supplied.
-/

public section

namespace Math.ComplexAnalysis

open Complex Set Metric
open scoped Real

theorem circleIntegral_logDeriv_eq_finsum_analyticOrderNatAt
    {f : ℂ → ℂ} {center : ℂ} {radius : ℝ}
    (hanalytic : AnalyticOnNhd ℂ f (closedBall center radius))
    (hboundary : ∀ z ∈ sphere center radius, f z ≠ 0) (hradius : 0 ≤ radius) :
    (∮ z in C(center, radius), logDeriv f z) =
      (2 * π * I) * ∑ᶠ z ∈ ball center radius, analyticOrderNatAt f z := by
  obtain ⟨zeros, hzeros, g, hg, hfactor, hgnonzero⟩ :=
    Math.Analysis.exists_finset_eq_prod_smul_nonzero hanalytic
      (isCompact_closedBall center radius) (convex_closedBall center radius).isPreconnected
      (fun hzero => ((NormedSpace.sphere_nonempty (x := center)).mpr hradius).elim
        fun x hx => hboundary x hx (hzero (sphere_subset_closedBall hx)))
  have hdenominator : ∀ z ∈ sphere center radius, ∀ w ∈ zeros, z - w ≠ 0 := by
    intro z hz w hw
    rw [sub_ne_zero]
    rintro rfl
    exact hboundary z hz ((hzeros z).mp hw).2
  have hzerosInterior : (zeros : Set ℂ) ⊆ ball center radius := by
    intro w hw
    rw [Finset.mem_coe, hzeros, ← sphere_union_ball, mem_union] at hw
    exact hw.1.resolve_left fun hboundaryPoint => hboundary w hboundaryPoint hw.2
  have hlogDerivative : EqOn (logDeriv f)
      (fun z => (∑ w ∈ zeros, analyticOrderNatAt f w / (z - w)) + logDeriv g z)
      (sphere center radius) := by
    intro z hz
    conv_lhs => rw [hfactor]
    simp only [smul_eq_mul]
    rw [logDeriv_fun_mul, logDeriv_fun_prod]
    · congr 1
      refine Finset.sum_congr rfl fun w hw => ?_
      rw [logDeriv_fun_pow (by fun_prop), logDeriv, Pi.div_apply,
        deriv_sub_const, deriv_id'']
      simp [div_eq_mul_inv]
    · intro w hw
      exact pow_ne_zero _ (hdenominator z hz w hw)
    · intros
      fun_prop
    · rw [Finset.prod_ne_zero_iff]
      exact fun w hw => pow_ne_zero _ (hdenominator z hz w hw)
    · exact hgnonzero z (sphere_subset_closedBall hz)
    · fun_prop
    · exact (hg z (sphere_subset_closedBall hz)).differentiableAt
  rw [finsum_mem_eq_sum_of_subset (t := zeros),
    circleIntegral.integral_congr hradius hlogDerivative]
  · have hanalyticLog : AnalyticOnNhd ℂ (logDeriv g) (closedBall center radius) :=
      hg.deriv.div hg hgnonzero
    have hintegrable : ∀ w ∈ zeros,
        CircleIntegrable (fun z => analyticOrderNatAt f w / (z - w)) center radius := by
      intro w hw
      apply ContinuousOn.circleIntegrable hradius
      exact continuousOn_const.div (continuous_id.sub continuous_const).continuousOn
        (fun z hz => hdenominator z hz w hw)
    rw [circleIntegral.integral_add, circleIntegral.integral_fun_sum,
      DiffContOnCl.circleIntegral_eq_zero hradius, add_zero, Nat.cast_sum, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun w hw => ?_
      rw [circleIntegral_div_sub_of_differentiable_on_off_countable countable_empty]
      · exact hzerosInterior hw
      · fun_prop
      · intros
        fun_prop
    · exact hanalyticLog.differentiableOn.diffContOnCl_ball subset_rfl
    · exact hintegrable
    · exact CircleIntegrable.fun_sum _ hintegrable
    · exact (hanalyticLog.continuousOn.mono sphere_subset_closedBall).circleIntegrable hradius
  · rintro z ⟨hzball, hzorder⟩
    rw [Function.mem_support, analyticOrderNatAt, ne_eq, ENat.toNat_eq_zero, not_or,
      analyticOrderAt_eq_zero, not_or, not_not, ne_eq, not_not] at hzorder
    have hzero := hzorder.1.2
    rw [hfactor, smul_eq_zero, Finset.prod_eq_zero_iff] at hzero
    obtain ⟨w, hw, hzw⟩ := hzero.resolve_right (hgnonzero z (ball_subset_closedBall hzball))
    have hzeq : z = w := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hzw)
    simpa only [hzeq, Finset.mem_coe] using hw
  · exact hzerosInterior

end Math.ComplexAnalysis

import UniformEquilibrium.Quitting.Stationary.DiscountedAmbientDerivative
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Uniform scaling of the actual discounted displacement

The ambient derivative of the literal displacement gives uniform convergence
on every fixed bounded set of signed scaled hazards. Neither the set nor its
points are required to lie in the probability cube. This is a source-specific
calculus consequence, not an extension of the probabilistic remainder bound.
-/

noncomputable section

namespace GameTheory

open Filter Set QuittingLCPClassification
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The actual scaled displacement converges uniformly on every bounded signed
hazard set to its singleton-matrix affine limit. -/
theorem quittingDiscountedDisplacement_scaled_uniform_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {domain : Set (ι → ℝ)} (hbounded : Bornology.IsBounded domain)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ discount : ℝ, 0 < discount → discount ≤ δ →
      ∀ hazard ∈ domain,
        ‖(fun who => -quittingDiscountedDisplacement reward discount
            (discount • hazard) who / discount) -
          (fun who => (∑ player, hazard player * quittingSingletonMatrix reward who player) -
            reward ⟨{who}, Finset.singleton_nonempty who⟩ who)‖ < ε := by
  let displacement : (ℝ × (ι → ℝ)) → (ι → ℝ) :=
    fun point who => quittingDiscountedDisplacement reward point.1 point.2 who
  let linear : (ℝ × (ι → ℝ)) →L[ℝ] (ι → ℝ) :=
    ContinuousLinearMap.pi (quittingDiscountedSingletonLinearization reward)
  have hderiv : HasFDerivAt displacement linear 0 :=
    hasFDerivAt_pi.mpr (hasFDerivAt_quittingDiscountedDisplacement_zero reward)
  have hzero : displacement 0 = 0 := by
    funext who
    exact quittingDiscountedDisplacement_zero reward who
  obtain ⟨B, hB, hnorm⟩ := hbounded.exists_pos_norm_le
  have hB1 : 0 < 1 + B := by positivity
  have hsmall := hderiv.isLittleO.bound (show 0 < ε / (2 * (1 + B)) by positivity)
  simp only [hzero, sub_zero] at hsmall
  obtain ⟨radius, hradius, hlocal⟩ := Metric.eventually_nhds_iff.mp hsmall
  refine ⟨radius / (2 * (1 + B)), by positivity, ?_⟩
  intro discount hdiscount hdiscount_le hazard hhazard
  let point : ℝ × (ι → ℝ) := (discount, discount • hazard)
  have hpoint : ‖point‖ ≤ discount * (1 + B) := by
    change max ‖discount‖ ‖discount • hazard‖ ≤ discount * (1 + B)
    apply max_le
    · simpa only [Real.norm_eq_abs, abs_of_pos hdiscount] using
        (show discount ≤ discount * (1 + B) by nlinarith)
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hdiscount]
      exact (mul_le_mul_of_nonneg_left (hnorm hazard hhazard) hdiscount.le).trans
        (by nlinarith)
  have hnear : dist point 0 < radius := by
    rw [dist_zero_right]
    have := (le_div_iff₀ (show 0 < 2 * (1 + B) by positivity)).mp hdiscount_le
    nlinarith
  have herror := hlocal hnear
  have herror' : ‖displacement point - linear point‖ ≤ (ε / 2) * discount := by
    calc
      _ ≤ (ε / (2 * (1 + B))) * ‖point‖ := herror
      _ ≤ (ε / (2 * (1 + B))) * (discount * (1 + B)) :=
        mul_le_mul_of_nonneg_left hpoint (by positivity)
      _ = (ε / 2) * discount := by field_simp [ne_of_gt hB1]
  have heq :
      (fun who => -quittingDiscountedDisplacement reward discount
          (discount • hazard) who / discount) -
        (fun who => (∑ player, hazard player * quittingSingletonMatrix reward who player) -
          reward ⟨{who}, Finset.singleton_nonempty who⟩ who) =
      (-discount⁻¹) • (displacement point - linear point) := by
    funext who
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, displacement, linear,
      ContinuousLinearMap.pi_apply, point, quittingDiscountedSingletonLinearization_apply,
      mul_assoc]
    rw [← Finset.mul_sum]
    field_simp [ne_of_gt hdiscount]
    ring
  rw [heq, norm_smul, norm_neg, norm_inv, Real.norm_eq_abs, abs_of_pos hdiscount]
  calc
    discount⁻¹ * ‖displacement point - linear point‖ ≤
        discount⁻¹ * ((ε / 2) * discount) :=
      mul_le_mul_of_nonneg_left herror' (inv_nonneg.mpr hdiscount.le)
    _ = ε / 2 := by field_simp [ne_of_gt hdiscount]
    _ < ε := by linarith

/-- Filter formulation of uniform convergence on an arbitrary bounded signed
set, with the original reward table retained literally. -/
theorem tendstoUniformlyOn_quittingDiscountedDisplacement_scaled
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {domain : Set (ι → ℝ)} (hbounded : Bornology.IsBounded domain) :
    TendstoUniformlyOn
      (fun discount : ℝ => fun hazard who =>
        -quittingDiscountedDisplacement reward discount (discount • hazard) who / discount)
      (fun hazard who => (∑ player, hazard player * quittingSingletonMatrix reward who player) -
        reward ⟨{who}, Finset.singleton_nonempty who⟩ who)
      (𝓝[>] (0 : ℝ)) domain := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ :=
    quittingDiscountedDisplacement_scaled_uniform_bound reward hbounded hε
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with discount hpositive hsmall
  intro hazard hhazard
  rw [dist_eq_norm, norm_sub_rev]
  exact hbound discount hpositive hsmall.le hazard hhazard

end GameTheory

import UniformEquilibrium.Quitting.Stationary.DiscountedUniformScaling
import MathUE.LinearProgramming.LocalAffine

/-!
# Uniform minimum-map scaling of the actual clipped discounted field

The upper clip becomes inactive uniformly on every fixed bounded set of signed
scaled hazards. The lower clip remains literal and yields a minimum map. The
existing uniform displacement approximation then controls the rescaled field
of the actual clipped map, using the same reward table and singleton matrix.
No probability-cube, fixed-point, localization, or degree hypothesis is used.
-/

noncomputable section

namespace GameTheory

open Set QuittingLCPClassification Math.LinearProgramming

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Once the upper clip is inactive, the literal fixed-point field is a minimum,
including at negative ambient hazard coordinates. -/
theorem quittingDiscountedClippedMap_sub_eq_min
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (discount : ℝ) (hazard : ι → ℝ) (who : ι)
    (hupper : hazard who + quittingDiscountedDisplacement reward discount hazard who ≤ 1) :
    hazard who - quittingDiscountedClippedMap reward discount hazard who =
      min (hazard who) (-quittingDiscountedDisplacement reward discount hazard who) := by
  rw [quittingDiscountedClippedMap, min_eq_right (max_le (by norm_num) hupper)]
  by_cases hnonneg : 0 ≤ hazard who +
      quittingDiscountedDisplacement reward discount hazard who
  · rw [max_eq_right hnonneg, min_eq_right (by linarith)]
    ring
  · rw [max_eq_left (le_of_not_ge hnonneg), sub_zero, min_eq_left (by linarith)]

/-- Positive rescaling retains exactly the lower-clip minimum expression. -/
theorem quittingDiscountedClippedMap_scaled_sub_eq_min
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {discount : ℝ} (hdiscount : 0 < discount) (hazard : ι → ℝ)
    (hupper : ∀ who, (discount • hazard) who +
      quittingDiscountedDisplacement reward discount (discount • hazard) who ≤ 1) :
    (fun who => ((discount • hazard) who -
      quittingDiscountedClippedMap reward discount (discount • hazard) who) / discount) =
      fun who => min (hazard who)
        (-quittingDiscountedDisplacement reward discount (discount • hazard) who / discount) := by
  funext who
  rw [quittingDiscountedClippedMap_sub_eq_min reward discount _ who (hupper who),
    ← min_div_div_right hdiscount.le]
  simp only [Pi.smul_apply, smul_eq_mul, mul_div_cancel_left₀ _ hdiscount.ne']

private theorem scaledDisplacement_residual_uniform_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {domain : Set (ι → ℝ)} (hbounded : Bornology.IsBounded domain)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ discount : ℝ, 0 < discount → discount ≤ δ →
      ∀ hazard ∈ domain,
        ‖(fun who => -quittingDiscountedDisplacement reward discount
            (discount • hazard) who / discount) -
          lcpResidual (quittingSingletonMatrix reward)
            (fun who => -reward ⟨{who}, Finset.singleton_nonempty who⟩ who) hazard‖ < ε := by
  obtain ⟨δ, hδ, hbound⟩ :=
    quittingDiscountedDisplacement_scaled_uniform_bound reward hbounded hε
  refine ⟨δ, hδ, ?_⟩
  intro discount hdiscount hsmall hazard hhazard
  have hlimit :
      (fun who => (∑ player, hazard player * quittingSingletonMatrix reward who player) -
        reward ⟨{who}, Finset.singleton_nonempty who⟩ who) =
      lcpResidual (quittingSingletonMatrix reward)
        (fun who => -reward ⟨{who}, Finset.singleton_nonempty who⟩ who) hazard := by
    funext who
    simp only [lcpResidual]
    ring
  simpa only [hlimit] using hbound discount hdiscount hsmall hazard hhazard

/-- The actual upper-clip input is strictly below one on every fixed bounded
signed scaled-hazard set, uniformly for all sufficiently small positive discounts. -/
theorem quittingDiscountedClippedMap_scaled_upper_inactive
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {domain : Set (ι → ℝ)} (hbounded : Bornology.IsBounded domain) :
    ∃ δ > 0, ∀ discount : ℝ, 0 < discount → discount ≤ δ →
      ∀ hazard ∈ domain, ∀ who,
        (discount • hazard) who +
          quittingDiscountedDisplacement reward discount (discount • hazard) who < 1 := by
  obtain ⟨B, hB, hnorm⟩ := hbounded.exists_pos_norm_le
  let matrix := quittingSingletonMatrix reward
  let offset := fun who => -reward ⟨{who}, Finset.singleton_nonempty who⟩ who
  have hcompact := (isCompact_closedBall (0 : ι → ℝ) B).image
    (continuous_lcpResidual matrix offset)
  obtain ⟨C, hC, hCbound⟩ := hcompact.isBounded.exists_pos_norm_le
  have hlimitBound (hazard : ι → ℝ) (hhazard : hazard ∈ domain) :
      ‖lcpResidual matrix offset hazard‖ ≤ C := by
    apply hCbound
    refine ⟨hazard, ?_, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm hazard hhazard
  obtain ⟨δ, hδ, hbound⟩ :=
    scaledDisplacement_residual_uniform_bound reward hbounded (show (0 : ℝ) < 1 by norm_num)
  have hden : 0 < 2 * (B + C + 1) := by positivity
  refine ⟨min δ (1 / (2 * (B + C + 1))), lt_min hδ (by positivity), ?_⟩
  intro discount hdiscount hsmall hazard hhazard who
  let scaled := fun player => -quittingDiscountedDisplacement reward discount
    (discount • hazard) player / discount
  have herror : ‖scaled - lcpResidual matrix offset hazard‖ < 1 :=
    hbound discount hdiscount (hsmall.trans (min_le_left _ _)) hazard hhazard
  have hscaled : ‖scaled‖ < 1 + C :=
    (norm_le_norm_sub_add scaled (lcpResidual matrix offset hazard)).trans_lt
      (add_lt_add_of_lt_of_le herror (hlimitBound hazard hhazard))
  have hcoordinate : |hazard who| ≤ B := by
    exact (norm_le_pi_norm hazard who).trans (hnorm hazard hhazard)
  have hdisplacement :
      |quittingDiscountedDisplacement reward discount (discount • hazard) who| <
        (1 + C) * discount := by
    have h := (norm_le_pi_norm scaled who).trans_lt hscaled
    change |-quittingDiscountedDisplacement reward discount
      (discount • hazard) who / discount| < 1 + C at h
    rw [abs_div, abs_neg, abs_of_pos hdiscount] at h
    exact (div_lt_iff₀ hdiscount).mp h
  have hscale : discount * (2 * (B + C + 1)) ≤ 1 :=
    (le_div_iff₀ hden).mp (hsmall.trans (min_le_right _ _))
  have hcoord := mul_le_mul_of_nonneg_left
    ((le_abs_self (hazard who)).trans hcoordinate) hdiscount.le
  have hdisp := le_abs_self
    (quittingDiscountedDisplacement reward discount (discount • hazard) who)
  simp only [Pi.smul_apply, smul_eq_mul]
  nlinarith

/-- Uniform approximation of the actual rescaled clipped field by the canonical
minimum LCP map. Upper-clip inactivity is derived and returned with the estimate. -/
theorem quittingDiscountedClippedMap_scaled_uniform_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {domain : Set (ι → ℝ)} (hbounded : Bornology.IsBounded domain)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ discount : ℝ, 0 < discount → discount ≤ δ →
      ∀ hazard ∈ domain,
        (∀ who, (discount • hazard) who +
          quittingDiscountedDisplacement reward discount (discount • hazard) who < 1) ∧
        ‖(fun who => ((discount • hazard) who -
            quittingDiscountedClippedMap reward discount (discount • hazard) who) / discount) -
          lcpMinMap (quittingSingletonMatrix reward)
            (fun who => -reward ⟨{who}, Finset.singleton_nonempty who⟩ who) hazard‖ < ε := by
  obtain ⟨δclip, hδclip, hclip⟩ :=
    quittingDiscountedClippedMap_scaled_upper_inactive reward hbounded
  obtain ⟨δerror, hδerror, herror⟩ :=
    scaledDisplacement_residual_uniform_bound reward hbounded hε
  refine ⟨min δclip δerror, lt_min hδclip hδerror, ?_⟩
  intro discount hdiscount hsmall hazard hhazard
  have hupper := hclip discount hdiscount (hsmall.trans (min_le_left _ _)) hazard hhazard
  refine ⟨hupper, ?_⟩
  rw [quittingDiscountedClippedMap_scaled_sub_eq_min reward hdiscount hazard
    (fun who => (hupper who).le)]
  apply (pi_norm_lt_iff hε).mpr
  intro who
  have hcoordinate := (pi_norm_lt_iff hε).mp
    (herror discount hdiscount (hsmall.trans (min_le_right _ _)) hazard hhazard) who
  change |min (hazard who)
      (-quittingDiscountedDisplacement reward discount (discount • hazard) who / discount) -
    min (hazard who) (lcpResidual (quittingSingletonMatrix reward)
      (fun player => -reward ⟨{player}, Finset.singleton_nonempty player⟩ player) hazard who)| < ε
  have hmin := abs_min_sub_min_le_max (hazard who)
    (-quittingDiscountedDisplacement reward discount (discount • hazard) who / discount)
    (hazard who) (lcpResidual (quittingSingletonMatrix reward)
      (fun player => -reward ⟨{player}, Finset.singleton_nonempty player⟩ player) hazard who)
  simp only [sub_self, abs_zero] at hmin
  rw [max_eq_right (abs_nonneg
    (-quittingDiscountedDisplacement reward discount (discount • hazard) who / discount -
      lcpResidual (quittingSingletonMatrix reward)
        (fun player => -reward ⟨{player}, Finset.singleton_nonempty player⟩ player) hazard who))]
    at hmin
  simp only [Pi.sub_apply, Real.norm_eq_abs] at hcoordinate
  exact hmin.trans_lt hcoordinate

end GameTheory

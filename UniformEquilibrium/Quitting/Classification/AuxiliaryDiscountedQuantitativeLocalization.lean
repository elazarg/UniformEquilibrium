import UniformEquilibrium.Quitting.Classification.AuxiliaryDiscountedLocalization
import UniformEquilibrium.Quitting.Stationary.DiscountedQuadraticRemainder

/-!
# Uniform scaled localization of every actual auxiliary fixed point

Original-game absence of uniform equilibrium supplies the unscaled no-escape
threshold. The same auxiliary table's R₀ margin and its actual quadratic
remainder supply one scaled bound before discount and before every fixed point.
No root, value limit or remainder certificate is selected as an input.
-/

noncomputable section

namespace GameTheory

open QuittingLCPClassification Math.LinearProgramming

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- One radius and discount threshold control all scaled fixed-point coordinates
and their total mass, for the canonical auxiliary table of the original game. -/
theorem auxiliaryDiscounted_fixedPoint_scaled_sum_lt_of_no_uniformEquilibriumPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (hR0 : IsR0Matrix (quittingSingletonMatrix (quittingAuxiliaryReward reward))) :
    ∃ radius : ℝ, 0 < radius ∧ ∃ threshold : ℝ, 0 < threshold ∧
      ∀ discount : ℝ, 0 < discount → discount ≤ min threshold 1 →
        ∀ hazard : ι → ℝ, (∀ who, 0 ≤ hazard who) → (∀ who, hazard who ≤ 1) →
          quittingDiscountedClippedMap (quittingAuxiliaryReward reward) discount hazard = hazard →
            (∑ who, hazard who) / discount < radius ∧
              ∀ who, hazard who / discount < radius := by
  let M := quittingRewardBound (quittingAuxiliaryReward reward)
  let C := quittingSingletonLocalizationFactor (quittingAuxiliaryReward reward)
  let L := C * (4 * M)
  let small := min (1 / 2 : ℝ) (1 / (4 * (L + 1)))
  have hM : 0 ≤ M := quittingRewardBound_nonneg _
  have hC : 0 < C := quittingSingletonLocalizationFactor_pos _ hR0
  have hL : 0 ≤ L := mul_nonneg hC.le (by positivity)
  have hsmall : 0 < small := lt_min (by norm_num) (by positivity)
  have hhalf : small ≤ 1 / 2 := min_le_left _ _
  have hden : 0 < 4 * (L + 1) := by positivity
  have hsmall_bound : small * (4 * (L + 1)) ≤ 1 :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  obtain ⟨threshold, hthreshold, hlocal⟩ :=
    auxiliaryDiscounted_fixedPoint_sum_lt_of_no_uniformEquilibriumPayoff reward hno hsmall
  refine ⟨2 * C * M + 2, by positivity, min threshold small,
    lt_min hthreshold hsmall, ?_⟩
  intro discount hdiscount hdiscount_bound hazard hzero hone hfixed
  have hdiscount_threshold : discount ≤ min threshold 1 :=
    le_min (hdiscount_bound.trans (min_le_left _ _) |>.trans (min_le_left _ _))
      (hdiscount_bound.trans (min_le_right _ _))
  have hdiscount_small : discount ≤ small :=
    hdiscount_bound.trans (min_le_left _ _) |>.trans (min_le_right _ _)
  have hsum := hlocal discount hdiscount hdiscount_threshold hazard hzero hone hfixed
  have hsum0 : 0 ≤ ∑ who, hazard who := Finset.sum_nonneg fun who _ => hzero who
  have hupper : ∀ who, hazard who < 1 := by
    intro who
    have hwho := Finset.single_le_sum (fun player _ => hzero player) (Finset.mem_univ who)
    exact hwho.trans_lt (hsum.trans_le hhalf) |>.trans (by norm_num)
  have habsorb : C * (4 * M) * (discount + ∑ who, hazard who) ≤ 1 / 2 := by
    change L * (discount + ∑ who, hazard who) ≤ _
    have hproduct := mul_le_mul_of_nonneg_left
      (add_le_add hdiscount_small hsum.le) hL
    nlinarith [hsmall_bound, hsmall.le]
  have hbound := sum_hazard_le_discount_of_quittingDiscountedFixedPoint_reward_bound
    (quittingAuxiliaryReward reward) hR0 hdiscount.le
    (abs_reward_le_quittingRewardBound _) hazard hzero hupper hfixed habsorb
  change (∑ who, hazard who) ≤ (2 * C * M + 1) * discount at hbound
  have htotal : (∑ who, hazard who) / discount < 2 * C * M + 2 :=
    ((div_le_iff₀ hdiscount).mpr hbound).trans_lt (by linarith)
  refine ⟨htotal, fun who => ?_⟩
  exact (div_le_div_of_nonneg_right
    (Finset.single_le_sum (fun player _ => hzero player) (Finset.mem_univ who))
    hdiscount.le).trans_lt htotal

end GameTheory

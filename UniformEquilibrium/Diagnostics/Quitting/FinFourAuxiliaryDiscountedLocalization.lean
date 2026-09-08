import UniformEquilibrium.Quitting.Classification.LCP.PunishmentNormalR0
import UniformEquilibrium.Quitting.Classification.AuxiliaryDiscountedQuantitativeLocalization
import UniformEquilibrium.Quitting.Classification.ThreePlayer.AuxiliaryShift
import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.FullSupportProjectiveQBarResidual

/-!
# Four-player auxiliary discounted localization

The existing hard residual supplies punishment normality of the original
table. The homogeneous witness consumer then excludes every full homogeneous
singleton solution. Terminal reward shifts preserve the comparison matrix
algebraically; no strategic equivalence or auxiliary no-equilibrium claim is
made when Never continues to pay zero.
-/

noncomputable section

namespace GameTheory

open QuittingLCPClassification Math.LinearProgramming

/-- Bare Fin4 absence of original UE supplies the original punishment-normality facts. -/
theorem finFour_punishment_le_singleton_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∀ who, quittingPunishmentValue reward who ≤
      reward ⟨{who}, Finset.singleton_nonempty who⟩ who := by
  obtain ⟨residual⟩ := nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff
    reward (abs_reward_le_quittingRewardBound reward) hnot
  exact residual.all_punishmentNormal

/-- Full original-matrix R₀ is a consequence, not a supplied normal-core certificate. -/
theorem finFour_isR0Matrix_quittingSingletonMatrix_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    IsR0Matrix (quittingSingletonMatrix reward) :=
  isR0Matrix_quittingSingletonMatrix_of_normal_of_no_uniformPayoff reward
    (finFour_punishment_le_singleton_of_no_uniformPayoff reward hnot) hnot

/-- The same original contrary hypothesis supplies R₀ for the actual auxiliary source. -/
theorem finFour_isR0Matrix_auxiliarySingletonMatrix_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    IsR0Matrix (quittingSingletonMatrix (quittingAuxiliaryReward reward)) := by
  change IsR0Matrix (quittingSingletonMatrix
    (fun coalition player => reward coalition player - quittingAuxiliaryLive reward player))
  rw [quittingSingletonMatrix_sub_payoff]
  exact finFour_isR0Matrix_quittingSingletonMatrix_of_no_uniformPayoff reward hnot

/-- The actual punishment-clipped singleton anchor is nonnegative in this branch. -/
theorem finFour_auxiliary_singleton_nonneg_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) (who : Fin 4) :
    0 ≤ quittingAuxiliaryReward reward ⟨{who}, Finset.singleton_nonempty who⟩ who := by
  exact sub_nonneg.mpr ((min_le_right (0 : ℝ) (quittingPunishmentValue reward who)).trans
    (finFour_punishment_le_singleton_of_no_uniformPayoff reward hnot who))

/-- Uniform-over-all-fixed-points scaled no-escape from bare original Fin4 noUE. -/
theorem finFour_auxiliaryDiscounted_fixedPoint_scaled_sum_lt_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hno : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ radius : ℝ, 0 < radius ∧ ∃ threshold : ℝ, 0 < threshold ∧
      ∀ discount : ℝ, 0 < discount → discount ≤ min threshold 1 →
        ∀ hazard : Fin 4 → ℝ, (∀ who, 0 ≤ hazard who) → (∀ who, hazard who ≤ 1) →
          quittingDiscountedClippedMap (quittingAuxiliaryReward reward) discount hazard = hazard →
            (∑ who, hazard who) / discount < radius ∧
              ∀ who, hazard who / discount < radius :=
  auxiliaryDiscounted_fixedPoint_scaled_sum_lt_of_no_uniformEquilibriumPayoff reward hno
    (finFour_isR0Matrix_auxiliarySingletonMatrix_of_no_uniformPayoff reward hno)

end GameTheory

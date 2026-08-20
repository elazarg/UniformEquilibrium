/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Debt.Dynamic.DynamicDebtConservation
import UniformEquilibrium.Quitting.Debt.Dynamic.PunishmentFloorViolation
import UniformEquilibrium.Quitting.Debt.Marked.TimeAdvance

/-!
# Charge-time coordinates of exact dynamic-debt edges

On an edge with positive absorption, prescribed-value drift, dynamic-debt
loss, and marginal Quit hazards have fixed normalized bounds. These are the
bounded coordinates available to a charge-time compactness argument.
-/

noncomputable section

namespace GameTheory

open Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- One exact dynamic-debt edge inherits the universal one-stage value-drift
bound, with the same literal joint absorption scale. -/
theorem abs_value_sub_le_two_mul_absorptionMass_of_dynamicDebtEdge
    (current successor : QuittingDebtPoint ι)
    (hsuccessor : successor ∈ quittingDebtBox reward)
    (hedge : IsQuittingDynamicDebtEdge reward current successor)
    (who : ι) :
    |successor.1.1 who - current.1.1 who| ≤
      2 * quittingRewardBound reward *
        quittingRootAbsorptionMass
          (quittingRootOfSimplex current.1.2) := by
  rw [congrFun hedge.1.1 who]
  simpa [abs_sub_comm] using
    (abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass
      reward successor.1.1 (quittingRootOfSimplex current.1.2) who
      (quittingRewardBound reward)
      (abs_reward_le_quittingRewardBound reward)
      (abs_le.mpr ⟨hsuccessor.1.1 who, hsuccessor.1.2 who⟩))

/-- On an active edge, prescribed-value drift normalized by joint absorption
stays in the fixed reward box. -/
theorem abs_normalized_valueDrift_le_two_rewardBound_of_dynamicDebtEdge
    (current successor : QuittingDebtPoint ι)
    (hsuccessor : successor ∈ quittingDebtBox reward)
    (hedge : IsQuittingDynamicDebtEdge reward current successor)
    (hactive : 0 < quittingRootAbsorptionMass
      (quittingRootOfSimplex current.1.2))
    (who : ι) :
    |(successor.1.1 who - current.1.1 who) /
        quittingRootAbsorptionMass
          (quittingRootOfSimplex current.1.2)| ≤
      2 * quittingRewardBound reward := by
  rw [abs_div, abs_of_pos hactive]
  apply (div_le_iff₀ hactive).2
  simpa [mul_assoc] using
    (abs_value_sub_le_two_mul_absorptionMass_of_dynamicDebtEdge
      current successor hsuccessor hedge who)

/-- Exact debt loss is also Lipschitz in literal absorption time.  The debt
coordinate therefore admits the same charge-time compactification as payoff. -/
theorem dynamicDebtCoordinateLoss_le_cap_mul_absorptionMass
    (current successor : QuittingDebtPoint ι)
    (hcurrent : current ∈ quittingDebtBox reward)
    (hsuccessor : successor ∈ quittingDebtBox reward)
    (hedge : IsQuittingDynamicDebtEdge reward current successor)
    (who : ι) :
    quittingDynamicDebtCoordinateLoss current successor who ≤
      quittingPositiveSingletonDebtCap reward who *
        quittingRootAbsorptionMass
          (quittingRootOfSimplex current.1.2) := by
  have hconservation :=
    quittingDynamicDebt_eq_continueMass_mul_add_seam
      current successor hedge hsuccessor.2.1 who
  have hseamNonneg := quittingDynamicDebtSeam_nonneg current hcurrent who
  have habsorptionNonneg : 0 ≤ quittingRootAbsorptionMass
      (quittingRootOfSimplex current.1.2) := by
    unfold quittingRootAbsorptionMass
    exact sub_nonneg.mpr (quittingStationaryContinueMass_le_one _)
  have hloss : quittingDynamicDebtCoordinateLoss current successor who =
      quittingRootAbsorptionMass
          (quittingRootOfSimplex current.1.2) * successor.2 who -
        quittingDynamicDebtSeam current who := by
    unfold quittingDynamicDebtCoordinateLoss quittingRootAbsorptionMass
    rw [hconservation]
    ring
  rw [hloss]
  calc
    quittingRootAbsorptionMass
          (quittingRootOfSimplex current.1.2) * successor.2 who -
        quittingDynamicDebtSeam current who ≤
      quittingRootAbsorptionMass
          (quittingRootOfSimplex current.1.2) * successor.2 who :=
        sub_le_self _ hseamNonneg
    _ ≤ quittingRootAbsorptionMass
          (quittingRootOfSimplex current.1.2) *
        quittingPositiveSingletonDebtCap reward who :=
      mul_le_mul_of_nonneg_left (hsuccessor.2.2 who) habsorptionNonneg
    _ = quittingPositiveSingletonDebtCap reward who *
        quittingRootAbsorptionMass
          (quittingRootOfSimplex current.1.2) := mul_comm _ _

/-- On an active edge, normalized debt loss lies in its singleton-cap box. -/
theorem normalized_dynamicDebtCoordinateLoss_mem_Icc
    (current successor : QuittingDebtPoint ι)
    (hcurrent : current ∈ quittingDebtBox reward)
    (hsuccessor : successor ∈ quittingDebtBox reward)
    (hedge : IsQuittingDynamicDebtEdge reward current successor)
    (hactive : 0 < quittingRootAbsorptionMass
      (quittingRootOfSimplex current.1.2))
    (who : ι) :
    quittingDynamicDebtCoordinateLoss current successor who /
        quittingRootAbsorptionMass
          (quittingRootOfSimplex current.1.2) ∈
      Set.Icc 0 (quittingPositiveSingletonDebtCap reward who) := by
  have hlossNonneg := quittingDynamicDebtCoordinateLoss_nonneg
    reward current successor hsuccessor.2.1 hedge who
  constructor
  · exact div_nonneg hlossNonneg hactive.le
  · apply (div_le_iff₀ hactive).2
    simpa [mul_comm] using
      (dynamicDebtCoordinateLoss_le_cap_mul_absorptionMass
        current successor hcurrent hsuccessor hedge who)

omit [DecidableEq ι] in
/-- A marginal Quit hazard normalized by positive joint absorption lies in
the unit interval. -/
theorem normalized_quitProbability_mem_Icc
    (root : ι → PMF Bool)
    (hactive : 0 < quittingRootAbsorptionMass root) (who : ι) :
    (root who true).toReal / quittingRootAbsorptionMass root ∈
      Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg ENNReal.toReal_nonneg hactive.le
  · exact (div_le_one hactive).2
      (quitProbability_le_quittingRootAbsorptionMass root who)

end GameTheory

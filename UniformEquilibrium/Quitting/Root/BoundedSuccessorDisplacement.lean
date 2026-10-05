import UniformEquilibrium.Quitting.Root.BoundedEndpoint

/-! # Successor displacement with separate reward and source bounds -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem abs_quittingRootSuccessorPayoff_sub_tail_le_reward_add_source_mul_absorptionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (player : ι) (M bound : ℝ)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (htail : |tail player| ≤ bound) :
    |quittingRootSuccessorPayoff reward tail root player - tail player| ≤
      (M + bound) * quittingRootAbsorptionMass root := by
  rw [quittingRootSuccessorPayoff_sub_tail]
  have hmass := quittingRootAbsorptionMass_nonneg root
  calc
    |quittingRootAbsorbingContribution reward root player -
        quittingRootAbsorptionMass root * tail player| ≤
        |quittingRootAbsorbingContribution reward root player| +
          |quittingRootAbsorptionMass root * tail player| := abs_sub _ _
    _ ≤ M * quittingRootAbsorptionMass root +
        quittingRootAbsorptionMass root * bound := by
      apply add_le_add
      · exact abs_quittingRootAbsorbingContribution_le reward root player M hreward
      · rw [abs_mul, abs_of_nonneg hmass]
        exact mul_le_mul_of_nonneg_left htail hmass
    _ = (M + bound) * quittingRootAbsorptionMass root := by ring

end GameTheory

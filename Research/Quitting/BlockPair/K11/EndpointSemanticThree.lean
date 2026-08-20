import Research.Quitting.BlockPair.K11.FourPlayerExpectation
import MathUE.PMFProduct.FiniteFubini

noncomputable section

namespace GameTheory.BlockPairK11.ConditionalData

open Math.Probability Math.PMFProduct Math.ProbabilityMassFunction

theorem endpointDifference_three_eq_expanded
    (h : Player → ℝ) (h0 : ∀ who, 0 ≤ h who)
    (h1 : ∀ who, h who ≤ 1) (tail : Payoff Player) :
    quittingRootEndpointDifference reward tail (rootOfHazard h h0 h1) 3 =
      BlockPairCharts.expandedDifference h tail 3 := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4, Math.PMFProduct.expect_pmfPi_fin4]
  simp +decide [rootOfHazard, expect_quittingHazardCoin, reward,
    quittingRootPayoff, quittingQuitters,
    BlockPairCharts.expandedDifference,
    BlockPairCharts.terminalRewardNat]
  ring

end GameTheory.BlockPairK11.ConditionalData

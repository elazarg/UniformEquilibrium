import Research.Quitting.BlockPair.K11.FourPlayerExpectation

noncomputable section

namespace GameTheory.BlockPairK11.ConditionalData

open Math.Probability Math.PMFProduct Math.ProbabilityMassFunction

theorem endpointDifference_two_eq_expanded
    (h : Player → ℝ) (h0 : ∀ who, 0 ≤ h who)
    (h1 : ∀ who, h who ≤ 1) (tail : Payoff Player) :
    quittingRootEndpointDifference reward tail (rootOfHazard h h0 h1) 2 =
      BlockPairCharts.expandedDifference h tail 2 := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4_bool, expect_pmfPi_fin4_bool]
  simp +decide [rootOfHazard, expect_quittingHazardCoin, reward,
    quittingRootPayoff, quittingQuitters,
    BlockPairCharts.expandedDifference,
    BlockPairCharts.terminalRewardNat]
  ring

end GameTheory.BlockPairK11.ConditionalData

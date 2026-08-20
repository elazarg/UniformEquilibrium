import Research.Quitting.BlockPair.K11.FourPlayerExpectation
import MathUE.PMFProduct.FiniteFubini
import Research.Quitting.BlockPair.K11.EvalImmediateReward
import UniformEquilibrium.Quitting.Stationary.Payoff

noncomputable section

namespace GameTheory.BlockPairK11.ConditionalData

open Math.Probability Math.PMFProduct Math.ProbabilityMassFunction

theorem rootAbsorbingContribution_one_eq_chart
    (h : Player → ℝ) (h0 : ∀ who, 0 ≤ h who)
    (h1 : ∀ who, h who ≤ 1) :
    quittingRootAbsorbingContribution reward (rootOfHazard h h0 h1) 1 =
      BlockPairCharts.realSum fun mask : QuitterMask ↦
        (terminalTable mask 1 : ℝ) *
          BlockPairCharts.maskProbability h mask := by
  unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4]
  simp +decide [rootOfHazard, expect_quittingHazardCoin, reward,
    quittingRootPayoff, quittingQuitters, BlockPairCharts.realSum,
    BlockPairCharts.maskProbability, BlockPairCharts.realProduct,
    BlockPairCharts.actionFactor, BlockPairCharts.terminalRewardNat]
  ring

end GameTheory.BlockPairK11.ConditionalData

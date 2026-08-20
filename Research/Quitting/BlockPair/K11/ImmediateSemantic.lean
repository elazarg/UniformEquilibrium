import Research.Quitting.BlockPair.K11.ImmediateSemanticZero
import Research.Quitting.BlockPair.K11.ImmediateSemanticOne
import Research.Quitting.BlockPair.K11.ImmediateSemanticTwo
import Research.Quitting.BlockPair.K11.ImmediateSemanticThree

noncomputable section

namespace GameTheory.BlockPairK11.ConditionalData

open Math.Interval

theorem rootAbsorbingContribution_eq_chart
    (h : Player → ℝ) (h0 : ∀ who, 0 ≤ h who)
    (h1 : ∀ who, h who ≤ 1) (who : Player) :
    quittingRootAbsorbingContribution reward (rootOfHazard h h0 h1) who =
      BlockPairCharts.realSum fun mask : QuitterMask ↦
        (terminalTable mask who : ℝ) *
          BlockPairCharts.maskProbability h mask := by
  fin_cases who
  · exact rootAbsorbingContribution_zero_eq_chart h h0 h1
  · exact rootAbsorbingContribution_one_eq_chart h h0 h1
  · exact rootAbsorbingContribution_two_eq_chart h h0 h1
  · exact rootAbsorbingContribution_three_eq_chart h h0 h1

theorem phaseRoot_absorbingContribution_eq_evalReal_immediateReward
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (phase : Phase) (who : Player) :
    quittingRootAbsorbingContribution reward (phaseRoot x hx phase) who =
      RationalPolynomial.evalReal x (immediateReward phase who) := by
  unfold phaseRoot
  rw [rootAbsorbingContribution_eq_chart, evalReal_immediateReward]

end GameTheory.BlockPairK11.ConditionalData

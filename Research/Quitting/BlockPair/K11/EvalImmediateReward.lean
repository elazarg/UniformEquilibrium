import Research.Quitting.BlockPair.K11.ConditionalData

noncomputable section

namespace GameTheory.BlockPairK11.ConditionalData

open Math.Interval

private theorem evalReal_mul (x : HazardIndex → ℝ)
    (first second : Expression) :
    RationalPolynomial.evalReal x (first * second) =
      RationalPolynomial.evalReal x first *
        RationalPolynomial.evalReal x second := rfl

private theorem evalReal_constant (x : HazardIndex → ℝ) (q : ℚ) :
    RationalPolynomial.evalReal x (.constant q : Expression) = q := rfl

theorem evalReal_immediateReward
    (x : HazardIndex → ℝ) (phase : Phase) (who : Player) :
    RationalPolynomial.evalReal x (immediateReward phase who) =
      BlockPairCharts.realSum fun mask : QuitterMask ↦
        (terminalTable mask who : ℝ) *
          BlockPairCharts.maskProbability (hazard x phase) mask := by
  unfold immediateReward
  rw [evalReal_expressionSum]
  apply congrArg BlockPairCharts.realSum
  funext mask
  rw [evalReal_mul, evalReal_constant, evalReal_maskProbability]

end GameTheory.BlockPairK11.ConditionalData

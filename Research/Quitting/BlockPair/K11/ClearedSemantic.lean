import Research.Quitting.BlockPair.K11.EndpointSemantic

noncomputable section

namespace GameTheory.BlockPairK11.ConditionalData

open Math.Interval

private theorem evalReal_mul (x : HazardIndex → ℝ)
    (first second : Expression) :
    RationalPolynomial.evalReal x (first * second) =
      RationalPolynomial.evalReal x first *
        RationalPolynomial.evalReal x second := rfl

private theorem evalReal_one (x : HazardIndex → ℝ) :
    RationalPolynomial.evalReal x (1 : Expression) = 1 := by
  norm_num [RationalPolynomial.evalReal]

/-- The public active equation is exactly the quitting-game endpoint
difference after multiplication by the common positive cycle denominator. -/
theorem evalReal_activeEquationAt_eq_clearedEndpointDifference
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (hrho : rho x < 1) (phase : Phase) (who : Player) :
    RationalPolynomial.evalReal x (activeEquationAt phase who) =
      (1 - rho x) * quittingRootEndpointDifference reward
        (phaseValue x (nextPhase phase)) (phaseRoot x hx phase) who := by
  rw [phaseRoot_endpointDifference_eq_chart]
  unfold activeEquationAt BlockPairCharts.difference
    BlockPairCharts.predecessorValue phaseValue rho
  rw [evalReal_sub, evalReal_mul, evalReal_mul, evalReal_sub, evalReal_sub,
    evalReal_one]
  rw [evalReal_opponentQuitValue,
    evalReal_opponentAbsorbingContribution, evalReal_opponentSurvival]
  have hdenominator : 1 -
      RationalPolynomial.evalReal x jointCycleSurvival ≠ 0 := by
    unfold rho at hrho
    linarith
  field_simp
  ring

end GameTheory.BlockPairK11.ConditionalData

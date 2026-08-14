import Research.Quitting.BlockPair.K11.NumeratorAlgebra

noncomputable section

namespace GameTheory.BlockPairK11.ConditionalData

open Math.Interval

/-- Evaluation of the canonical expression recurrence follows the same named
ordered scalar recurrence. -/
theorem evalReal_numeratorAux_eq_scalarNumeratorAux
    (x : HazardIndex → ℝ) (phase : Phase) (who : Player) (fuel : ℕ) :
    (RationalPolynomial.evalReal x (numeratorAux phase who fuel).1,
      RationalPolynomial.evalReal x (numeratorAux phase who fuel).2) =
      scalarNumeratorAux
        (fun offset ↦ RationalPolynomial.evalReal x
          (immediateReward (phaseAdd phase offset) who))
        (fun offset ↦ RationalPolynomial.evalReal x
          (phaseSurvival (phaseAdd phase offset))) fuel := by
  induction fuel with
  | zero =>
      norm_num [numeratorAux, scalarNumeratorAux,
        RationalPolynomial.evalReal]
  | succ fuel inductionHypothesis =>
      simp only [numeratorAux, scalarNumeratorAux]
      change
        (RationalPolynomial.evalReal x (numeratorAux phase who fuel).1 +
            RationalPolynomial.evalReal x (numeratorAux phase who fuel).2 *
              RationalPolynomial.evalReal x
                (immediateReward (phaseAdd phase fuel) who),
          RationalPolynomial.evalReal x (numeratorAux phase who fuel).2 *
            RationalPolynomial.evalReal x
              (phaseSurvival (phaseAdd phase fuel))) = _
      have hfirst := congrArg Prod.fst inductionHypothesis
      have hsecond := congrArg Prod.snd inductionHypothesis
      simp only at hfirst hsecond
      rw [hfirst, hsecond]

end GameTheory.BlockPairK11.ConditionalData

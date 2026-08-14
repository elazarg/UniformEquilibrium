import Research.Quitting.BlockPair.K11.NumeratorEvaluation
import Research.Quitting.BlockPair.K11.CyclicNumeratorAlgebra
import Research.Quitting.BlockPair.K11.PhaseArithmetic

noncomputable section

namespace GameTheory.BlockPairK11.ConditionalData

open Math.Interval

theorem phaseAdd_eq_addLeft (phase offset : Phase) :
    phaseAdd phase offset.val = Equiv.addLeft phase offset := by
  apply Fin.ext
  simp [phaseAdd, Fin.ofNat, Fin.add_def]

/-- The survival component of any rotated eleven-step fold is the same
public full-cycle survival polynomial. -/
theorem scalarCycleSurvival_eq_evalReal_jointCycleSurvival
    (x : HazardIndex → ℝ) (phase : Phase) (who : Player) :
    (scalarCycleNumerator
      (fun current ↦ RationalPolynomial.evalReal x
        (immediateReward current who))
      (fun current ↦ RationalPolynomial.evalReal x
        (phaseSurvival current)) phase).2 =
      RationalPolynomial.evalReal x jointCycleSurvival := by
  unfold scalarCycleNumerator jointCycleSurvival
  rw [scalarNumeratorAux_survival_eq_realProduct,
    realProduct_eq_fintypeProduct, evalReal_expressionProduct,
    realProduct_eq_fintypeProduct]
  have hrotate := Equiv.prod_comp (Equiv.addLeft phase)
    (fun current : Phase ↦ RationalPolynomial.evalReal x
      (phaseSurvival current))
  simpa only [phaseAdd_eq_addLeft] using hrotate

end GameTheory.BlockPairK11.ConditionalData

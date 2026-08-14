import Research.Quitting.BlockPair.K11.CycleProduct

noncomputable section

namespace GameTheory.BlockPairK11.ConditionalData

open Math.Interval

theorem evalReal_cyclicValueNumerator_eq_scalarCycle
    (x : HazardIndex → ℝ) (phase : Phase) (who : Player) :
    RationalPolynomial.evalReal x (cyclicValueNumerator phase who) =
      (scalarCycleNumerator
        (fun current ↦ RationalPolynomial.evalReal x
          (immediateReward current who))
        (fun current ↦ RationalPolynomial.evalReal x
          (phaseSurvival current)) phase).1 := by
  unfold cyclicValueNumerator scalarCycleNumerator
  have hagree := evalReal_numeratorAux_eq_scalarNumeratorAux
    x phase who 11
  exact congrArg Prod.fst hagree

/-- Evaluated cyclic numerators satisfy the one-phase Bellman numerator
identity, derived from the named fold recurrence and cyclic rotation. -/
theorem evalReal_cyclicValueNumerator_recurrence
    (x : HazardIndex → ℝ) (phase : Phase) (who : Player) :
    RationalPolynomial.evalReal x (cyclicValueNumerator phase who) =
      (1 - RationalPolynomial.evalReal x jointCycleSurvival) *
          RationalPolynomial.evalReal x (immediateReward phase who) +
        RationalPolynomial.evalReal x (phaseSurvival phase) *
          RationalPolynomial.evalReal x
            (cyclicValueNumerator (nextPhase phase) who) := by
  rw [evalReal_cyclicValueNumerator_eq_scalarCycle,
    evalReal_cyclicValueNumerator_eq_scalarCycle]
  have hrecurrence := scalarCycleNumerator_recurrence
    (fun current ↦ RationalPolynomial.evalReal x
      (immediateReward current who))
    (fun current ↦ RationalPolynomial.evalReal x
      (phaseSurvival current)) phase
  rw [scalarCycleSurvival_eq_evalReal_jointCycleSurvival] at hrecurrence
  exact hrecurrence

end GameTheory.BlockPairK11.ConditionalData

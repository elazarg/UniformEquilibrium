import Research.Quitting.BlockPair.K11.ContinueMassRoot

noncomputable section

namespace GameTheory.BlockPairK11.ConditionalData

open Math.Interval

theorem phaseRoot_continueMass_eq_evalReal_phaseSurvival
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1) (phase : Phase) :
    quittingStationaryContinueMass (phaseRoot x hx phase) =
      RationalPolynomial.evalReal x (phaseSurvival phase) := by
  unfold phaseRoot
  rw [rootOfHazard_continueMass_eq_maskProbability,
    evalReal_phaseSurvival]

end GameTheory.BlockPairK11.ConditionalData

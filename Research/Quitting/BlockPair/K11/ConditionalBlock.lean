import Research.Quitting.BlockPair.K11.ConditionalNash
import Research.Quitting.BlockPair.K11.ConditionalAbsorption

noncomputable section

namespace GameTheory.BlockPairK11.ConditionalData

open Math.Interval

theorem block_isQuittingCyclicContinuationBlock
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (hrho : rho x < 1)
    (hequation : ∀ equation,
      RationalPolynomial.evalReal x (activeEquation equation) = 0)
    (hinactive : ∀ phase who,
      LocalInterval.activeHazardIndex? phase who = none →
        RationalPolynomial.evalReal x (activeEquationAt phase who) ≤ 0)
    (hbound : ∀ phase who,
      |phaseValue x phase who| ≤ quittingRewardBound reward) :
    IsQuittingCyclicContinuationBlock reward (phaseValue x 0) 11
      (block x hx) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro time
    change phaseValue x (pathPhase time) ∈
      Set.Icc (fun _ : Player ↦ -(quittingRewardBound reward))
        (fun _ ↦ quittingRewardBound reward)
    exact ⟨fun who ↦ (abs_le.mp (hbound _ who)).1,
      fun who ↦ (abs_le.mp (hbound _ who)).2⟩
  · rfl
  · intro time
    have hphase := pathPhase_succ time
    constructor
    · change phaseValue x (pathPhase (Fin.castSucc time)) =
        quittingRootSuccessorPayoff reward
          (phaseValue x (pathPhase (Fin.succ time)))
          (quittingRootOfSimplex
            (phasePoint x hx (pathPhase (Fin.castSucc time))).2)
      rw [rootOfSimplex_phasePoint, hphase]
      exact phaseValue_eq_quittingRootSuccessorPayoff x hx hrho _
    · change IsεQuittingRootEndpointNash reward
        (phaseValue x (pathPhase (Fin.succ time))) 0
        (quittingRootOfSimplex
          (phasePoint x hx (pathPhase (Fin.castSucc time))).2)
      rw [rootOfSimplex_phasePoint, hphase]
      exact phaseRoot_isZeroEndpointNash x hx hrho hequation hinactive _
  · rfl
  · obtain ⟨phase, hphase⟩ := exists_phaseRoot_positive_absorption x hx
    refine ⟨phase, ?_⟩
    change 0 < quittingRootAbsorptionMass
      (quittingRootOfSimplex
        (phasePoint x hx (pathPhase (Fin.castSucc phase))).2)
    rw [rootOfSimplex_phasePoint]
    simpa using hphase

end GameTheory.BlockPairK11.ConditionalData

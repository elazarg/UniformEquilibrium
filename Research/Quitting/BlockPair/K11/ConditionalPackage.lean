import Research.Quitting.BlockPair.K11.ConditionalUniformPayoff

noncomputable section

namespace GameTheory.BlockPairK11.ConditionalData

open Math.Interval

/-- Conditional K11 strategic compiler.  Every premise is numerical or a
standard finite-cycle admissibility/boundedness certificate; reward semantics,
positive absorption, and the Bellman recurrence are internal theorems. -/
theorem compile
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (hrho : rho x < 1)
    (hequation : ∀ equation,
      RationalPolynomial.evalReal x (activeEquation equation) = 0)
    (hinactive : ∀ phase who,
      LocalInterval.activeHazardIndex? phase who = none →
        RationalPolynomial.evalReal x (activeEquationAt phase who) ≤ 0)
    (hbound : ∀ phase who,
      |phaseValue x phase who| ≤ quittingRewardBound reward)
    (hadmissible : IsQuittingCycleAdmissible reward (phaseRoot x hx)) :
    IsQuittingCyclicContinuationBlock reward (phaseValue x 0) 11
        (block x hx) ∧
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0 (profile x hx) ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none
        (phaseValue x 0) := by
  have hblock : IsQuittingCyclicContinuationBlock reward (phaseValue x 0) 11
      (block x hx) := block_isQuittingCyclicContinuationBlock x hx hrho
        hequation hinactive hbound
  have hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0 (profile x hx) :=
    profile_isExactTerminalNash x hx hblock hadmissible
  have huniform : (quittingGame reward).IsUniformEquilibriumPayoff none
      (phaseValue x 0) :=
    isUniformEquilibriumPayoff_phaseZero x hx hblock hadmissible
  exact ⟨hblock, hnash, huniform⟩

end GameTheory.BlockPairK11.ConditionalData

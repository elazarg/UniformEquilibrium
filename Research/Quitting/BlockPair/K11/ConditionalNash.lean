import Research.Quitting.BlockPair.K11.ConditionalBlockData
import Research.Quitting.BlockPair.K11.ClearedSemantic

noncomputable section

namespace GameTheory.BlockPairK11.ConditionalData

open Math.Interval

theorem active_endpointDifference_eq_zero
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (hrho : rho x < 1)
    (hequation : ∀ equation,
      RationalPolynomial.evalReal x (activeEquation equation) = 0)
    {phase : Phase} {who : Player} {index : HazardIndex}
    (hindex : LocalInterval.activeHazardIndex? phase who = some index) :
    quittingRootEndpointDifference reward
        (phaseValue x (nextPhase phase)) (phaseRoot x hx phase) who = 0 := by
  have hslot : activeSlot index = (phase, who) :=
    (LocalInterval.activeHazardIndex?_eq_some_iff phase who index).mp hindex
  have heval : RationalPolynomial.evalReal x
      (activeEquationAt phase who) = 0 := by
    have h := hequation index
    unfold activeEquation at h
    simpa only [hslot] using h
  rw [evalReal_activeEquationAt_eq_clearedEndpointDifference x hx hrho]
    at heval
  have hdenominator : 1 - rho x ≠ 0 := by linarith
  exact (mul_eq_zero.mp heval).resolve_left hdenominator

theorem inactive_endpointDifference_nonpos
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (hrho : rho x < 1) {phase : Phase} {who : Player}
    (hinactive : RationalPolynomial.evalReal x
      (activeEquationAt phase who) ≤ 0) :
    quittingRootEndpointDifference reward
        (phaseValue x (nextPhase phase)) (phaseRoot x hx phase) who ≤ 0 := by
  rw [evalReal_activeEquationAt_eq_clearedEndpointDifference x hx hrho]
    at hinactive
  have hpositive : 0 < 1 - rho x := sub_pos.mpr hrho
  nlinarith

theorem phaseRoot_isZeroEndpointNash
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (hrho : rho x < 1)
    (hequation : ∀ equation,
      RationalPolynomial.evalReal x (activeEquation equation) = 0)
    (hinactive : ∀ phase who,
      LocalInterval.activeHazardIndex? phase who = none →
        RationalPolynomial.evalReal x (activeEquationAt phase who) ≤ 0)
    (phase : Phase) :
    IsεQuittingRootEndpointNash reward (phaseValue x (nextPhase phase)) 0
      (phaseRoot x hx phase) := by
  intro who
  cases hindex : LocalInterval.activeHazardIndex? phase who with
  | none =>
      have hdiff := inactive_endpointDifference_nonpos x hx hrho
        (hinactive phase who hindex)
      simp [phaseRoot_false, phaseRoot_true, hazard, hindex, hdiff]
  | some index =>
      have hdiff := active_endpointDifference_eq_zero x hx hrho hequation
        hindex
      simp [hdiff]

end GameTheory.BlockPairK11.ConditionalData

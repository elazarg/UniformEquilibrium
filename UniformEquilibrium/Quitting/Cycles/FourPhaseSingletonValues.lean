import UniformEquilibrium.Quitting.Circulation.SingletonFlowMesh
import UniformEquilibrium.Quitting.Boundary.Exceptional.TailFallback
import MathUE.FourPhasePositiveMass

noncomputable section

namespace GameTheory

namespace FourPhaseSingletonValues

variable (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
variable (mass : Math.FourPhasePositiveMass)

def targetValue : Payoff (Fin 4) := fun who =>
  (mass.normalizedWeightZero * quittingSoloReward reward 0 who +
    mass.normalizedWeightOne * quittingSoloReward reward 1 who +
    mass.normalizedWeightTwo * quittingSoloReward reward 2 who +
    mass.normalizedWeightThree * quittingSoloReward reward 3 who) /
      (1 - mass.periodSurvival)

def afterZeroValue : Payoff (Fin 4) := fun who =>
  (mass.periodSurvival * mass.normalizedWeightZero *
      quittingSoloReward reward 0 who +
    mass.normalizedWeightOne * quittingSoloReward reward 1 who +
    mass.normalizedWeightTwo * quittingSoloReward reward 2 who +
    mass.normalizedWeightThree * quittingSoloReward reward 3 who) /
      (mass.tailOne * (1 - mass.periodSurvival))

def afterOneValue : Payoff (Fin 4) := fun who =>
  (mass.periodSurvival * (mass.normalizedWeightZero *
      quittingSoloReward reward 0 who +
    mass.normalizedWeightOne * quittingSoloReward reward 1 who) +
    mass.normalizedWeightTwo * quittingSoloReward reward 2 who +
    mass.normalizedWeightThree * quittingSoloReward reward 3 who) /
      (mass.tailTwo * (1 - mass.periodSurvival))

def afterTwoValue : Payoff (Fin 4) := fun who =>
  (mass.periodSurvival * (mass.normalizedWeightZero *
      quittingSoloReward reward 0 who +
    mass.normalizedWeightOne * quittingSoloReward reward 1 who +
    mass.normalizedWeightTwo * quittingSoloReward reward 2 who) +
    mass.normalizedWeightThree * quittingSoloReward reward 3 who) /
      (mass.tailThree * (1 - mass.periodSurvival))

def coarseValue : Fin 4 → Payoff (Fin 4)
  | 0 => targetValue reward mass
  | 1 => afterZeroValue reward mass
  | 2 => afterOneValue reward mass
  | 3 => afterTwoValue reward mass

def phaseHazard : Fin 4 → ℝ
  | 0 => mass.hazardZero
  | 1 => mass.hazardOne
  | 2 => mass.hazardTwo
  | 3 => mass.hazardThree

private theorem one_sub_period_pos : 0 < 1 - mass.periodSurvival :=
  sub_pos.mpr mass.periodSurvival_lt_one

private theorem coarse_bellman_zero :
    targetValue reward mass = quittingSingletonArcPayoff
      (mass.hazardZero) (quittingSoloReward reward 0)
      (afterZeroValue reward mass) := by
  funext who
  have ht := mass.tails_pos
  have ht1 : 0 < 1 - mass.normalizedWeightZero := by
    simpa [Math.FourPhasePositiveMass.tailOne] using ht.1
  have hsurvival := mass.survival_eq_one_sub_hazard
  simp only [targetValue, afterZeroValue, quittingSingletonArcPayoff]
  rw [← hsurvival.1]
  unfold Math.FourPhasePositiveMass.hazardZero
    Math.FourPhasePositiveMass.survivalZero
  dsimp [Math.FourPhasePositiveMass.tailZero,
    Math.FourPhasePositiveMass.tailOne]
  field_simp [ne_of_gt ht1, ne_of_gt (one_sub_period_pos mass)]
  ring

private theorem coarse_bellman_one :
    afterZeroValue reward mass = quittingSingletonArcPayoff
      (mass.hazardOne) (quittingSoloReward reward 1)
      (afterOneValue reward mass) := by
  funext who
  obtain ⟨ht1, ht2, -, -⟩ := mass.tails_pos
  have hsurvival := mass.survival_eq_one_sub_hazard
  simp only [afterZeroValue, afterOneValue, quittingSingletonArcPayoff]
  rw [← hsurvival.2.1]
  unfold Math.FourPhasePositiveMass.hazardOne
    Math.FourPhasePositiveMass.survivalOne
  field_simp [ne_of_gt ht1, ne_of_gt ht2,
    ne_of_gt (one_sub_period_pos mass)]
  ring

private theorem coarse_bellman_two :
    afterOneValue reward mass = quittingSingletonArcPayoff
      (mass.hazardTwo) (quittingSoloReward reward 2)
      (afterTwoValue reward mass) := by
  funext who
  obtain ⟨-, ht2, ht3, -⟩ := mass.tails_pos
  have hsurvival := mass.survival_eq_one_sub_hazard
  simp only [afterOneValue, afterTwoValue, quittingSingletonArcPayoff]
  rw [← hsurvival.2.2.1]
  unfold Math.FourPhasePositiveMass.hazardTwo
    Math.FourPhasePositiveMass.survivalTwo
  field_simp [ne_of_gt ht2, ne_of_gt ht3,
    ne_of_gt (one_sub_period_pos mass)]
  ring

private theorem coarse_bellman_three :
    afterTwoValue reward mass = quittingSingletonArcPayoff
      (mass.hazardThree) (quittingSoloReward reward 3)
      (targetValue reward mass) := by
  funext who
  obtain ⟨-, -, ht3, ht4⟩ := mass.tails_pos
  have htail := mass.tail_identities
  have hsurvival := mass.survival_eq_one_sub_hazard
  simp only [afterTwoValue, targetValue, quittingSingletonArcPayoff]
  rw [← hsurvival.2.2.2]
  unfold Math.FourPhasePositiveMass.hazardThree
    Math.FourPhasePositiveMass.survivalThree
  have ht4eq : mass.tailFour = mass.periodSurvival := by
    exact htail.2.2.2
  rw [ht4eq]
  field_simp [ne_of_gt ht3, ne_of_gt ht4,
    ne_of_gt (one_sub_period_pos mass)]
  ring

theorem coarse_bellman (phase : Fin 4) :
    coarseValue reward mass phase = quittingSingletonArcPayoff
      (phaseHazard mass phase) (quittingSoloReward reward phase)
      (coarseValue reward mass (finRotate 4 phase)) := by
  fin_cases phase
  · simpa [coarseValue, phaseHazard, finRotate_apply] using
      coarse_bellman_zero reward mass
  · simpa [coarseValue, phaseHazard, finRotate_apply] using
      coarse_bellman_one reward mass
  · simpa [coarseValue, phaseHazard, finRotate_apply] using
      coarse_bellman_two reward mass
  · simpa [coarseValue, phaseHazard, finRotate_apply] using
      coarse_bellman_three reward mass

end FourPhaseSingletonValues
end GameTheory

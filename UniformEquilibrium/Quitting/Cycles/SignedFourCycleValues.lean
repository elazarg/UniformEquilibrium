import UniformEquilibrium.Quitting.Circulation.SingletonFlowMesh
import UniformEquilibrium.Quitting.Boundary.Exceptional.TailFallback
import UniformEquilibrium.Quitting.Cycles.SignedFourCycleRewardAdapter

noncomputable section

namespace GameTheory

namespace SignedFourCycleSingletonData

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable (data : SignedFourCycleSingletonData reward) (tests : data.StrictTests)

private abbrev weights := tests.weights
private abbrev period := data.coefficients.periodSurvival

def targetValue : Payoff (Fin 4) := fun who =>
  ((weights data tests).normalizedWeightZero * quittingSoloReward reward 0 who +
    (weights data tests).normalizedWeightOne * quittingSoloReward reward 1 who +
    (weights data tests).normalizedWeightTwo * quittingSoloReward reward 2 who +
    (weights data tests).normalizedWeightThree * quittingSoloReward reward 3 who) /
      (1 - period data)

def afterZeroValue : Payoff (Fin 4) := fun who =>
  (period data * (weights data tests).normalizedWeightZero *
      quittingSoloReward reward 0 who +
    (weights data tests).normalizedWeightOne * quittingSoloReward reward 1 who +
    (weights data tests).normalizedWeightTwo * quittingSoloReward reward 2 who +
    (weights data tests).normalizedWeightThree * quittingSoloReward reward 3 who) /
      ((weights data tests).tailOne * (1 - period data))

def afterOneValue : Payoff (Fin 4) := fun who =>
  (period data * ((weights data tests).normalizedWeightZero *
      quittingSoloReward reward 0 who +
    (weights data tests).normalizedWeightOne * quittingSoloReward reward 1 who) +
    (weights data tests).normalizedWeightTwo * quittingSoloReward reward 2 who +
    (weights data tests).normalizedWeightThree * quittingSoloReward reward 3 who) /
      ((weights data tests).tailTwo * (1 - period data))

def afterTwoValue : Payoff (Fin 4) := fun who =>
  (period data * ((weights data tests).normalizedWeightZero *
      quittingSoloReward reward 0 who +
    (weights data tests).normalizedWeightOne * quittingSoloReward reward 1 who +
    (weights data tests).normalizedWeightTwo * quittingSoloReward reward 2 who) +
    (weights data tests).normalizedWeightThree * quittingSoloReward reward 3 who) /
      ((weights data tests).tailThree * (1 - period data))

def coarseValue : Fin 4 → Payoff (Fin 4)
  | 0 => data.targetValue tests
  | 1 => data.afterZeroValue tests
  | 2 => data.afterOneValue tests
  | 3 => data.afterTwoValue tests

def phaseHazard : Fin 4 → ℝ
  | 0 => (weights data tests).hazardZero
  | 1 => (weights data tests).hazardOne
  | 2 => (weights data tests).hazardTwo
  | 3 => (weights data tests).hazardThree

private theorem one_sub_period_pos (tests : data.StrictTests) : 0 < 1 - period data :=
  sub_pos.mpr (data.coefficients.periodSurvival_lt_one
    (StrictTests.smallerEigenvalue_gt_one tests))

private theorem coarse_bellman_zero :
    data.targetValue tests = quittingSingletonArcPayoff
      ((weights data tests).hazardZero) (quittingSoloReward reward 0)
      (data.afterZeroValue tests) := by
  funext who
  have ht := (weights data tests).tails_pos
  have ht1 : 0 < 1 - (weights data tests).normalizedWeightZero := by
    simpa [Math.SignedFourCycleStrictData.tailOne] using ht.1
  have hsurvival := (weights data tests).survival_eq_one_sub_hazard
  simp only [targetValue, afterZeroValue, quittingSingletonArcPayoff]
  rw [← hsurvival.1]
  unfold Math.SignedFourCycleStrictData.hazardZero
    Math.SignedFourCycleStrictData.survivalZero
  dsimp [Math.SignedFourCycleStrictData.tailZero,
    Math.SignedFourCycleStrictData.tailOne]
  field_simp [ne_of_gt ht1, ne_of_gt (data.one_sub_period_pos tests)]
  ring

private theorem coarse_bellman_one :
    data.afterZeroValue tests = quittingSingletonArcPayoff
      ((weights data tests).hazardOne) (quittingSoloReward reward 1)
      (data.afterOneValue tests) := by
  funext who
  obtain ⟨ht1, ht2, -, -⟩ := (weights data tests).tails_pos
  have hsurvival := (weights data tests).survival_eq_one_sub_hazard
  simp only [afterZeroValue, afterOneValue, quittingSingletonArcPayoff]
  rw [← hsurvival.2.1]
  unfold Math.SignedFourCycleStrictData.hazardOne
    Math.SignedFourCycleStrictData.survivalOne
  field_simp [ne_of_gt ht1, ne_of_gt ht2,
    ne_of_gt (data.one_sub_period_pos tests)]
  ring

private theorem coarse_bellman_two :
    data.afterOneValue tests = quittingSingletonArcPayoff
      ((weights data tests).hazardTwo) (quittingSoloReward reward 2)
      (data.afterTwoValue tests) := by
  funext who
  obtain ⟨-, ht2, ht3, -⟩ := (weights data tests).tails_pos
  have hsurvival := (weights data tests).survival_eq_one_sub_hazard
  simp only [afterOneValue, afterTwoValue, quittingSingletonArcPayoff]
  rw [← hsurvival.2.2.1]
  unfold Math.SignedFourCycleStrictData.hazardTwo
    Math.SignedFourCycleStrictData.survivalTwo
  field_simp [ne_of_gt ht2, ne_of_gt ht3,
    ne_of_gt (data.one_sub_period_pos tests)]
  ring

private theorem coarse_bellman_three :
    data.afterTwoValue tests = quittingSingletonArcPayoff
      ((weights data tests).hazardThree) (quittingSoloReward reward 3)
      (data.targetValue tests) := by
  funext who
  obtain ⟨-, -, ht3, ht4⟩ := (weights data tests).tails_pos
  have htail := (weights data tests).tail_identities
  have hsurvival := (weights data tests).survival_eq_one_sub_hazard
  simp only [afterTwoValue, targetValue, quittingSingletonArcPayoff]
  rw [← hsurvival.2.2.2]
  unfold Math.SignedFourCycleStrictData.hazardThree
    Math.SignedFourCycleStrictData.survivalThree
  have ht4eq : (weights data tests).tailFour = period data := by
    simpa [weights, StrictTests.weights] using htail.2.2.2
  rw [ht4eq]
  field_simp [ne_of_gt ht3, ne_of_gt ht4,
    ne_of_gt (data.one_sub_period_pos tests)]
  ring

theorem coarse_bellman (phase : Fin 4) :
    data.coarseValue tests phase = quittingSingletonArcPayoff
      (data.phaseHazard tests phase) (quittingSoloReward reward phase)
      (data.coarseValue tests (finRotate 4 phase)) := by
  fin_cases phase
  · simpa [coarseValue, phaseHazard, finRotate_apply] using
      data.coarse_bellman_zero tests
  · simpa [coarseValue, phaseHazard, finRotate_apply] using
      data.coarse_bellman_one tests
  · simpa [coarseValue, phaseHazard, finRotate_apply] using
      data.coarse_bellman_two tests
  · simpa [coarseValue, phaseHazard, finRotate_apply] using
      data.coarse_bellman_three tests

end SignedFourCycleSingletonData
end GameTheory

import UniformEquilibrium.Quitting.Circulation.SingletonFlowMesh
import UniformEquilibrium.Quitting.Boundary.Exceptional.TailFallback
import UniformEquilibrium.Quitting.Cycles.SignedFourCycleRewardAdapter
import UniformEquilibrium.Quitting.Cycles.FourPhaseSingletonValues

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

/-- The branch-independent four-phase Bellman reconstruction. -/
theorem coarse_bellman (phase : Fin 4) :
    data.coarseValue tests phase = quittingSingletonArcPayoff
      (data.phaseHazard tests phase) (quittingSoloReward reward phase)
      (data.coarseValue tests (finRotate 4 phase)) :=
  FourPhaseSingletonValues.coarse_bellman reward tests.weights.positiveMass phase

end SignedFourCycleSingletonData
end GameTheory

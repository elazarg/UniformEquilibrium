import MathUE.Finset.FinFourNonemptyCoalitions
import UniformEquilibrium.ProofView.Concepts.Stochastic.Models.Quitting.Game

/-!
# The four-player overlapping-support period-three reward table
-/

noncomputable section

namespace GameTheory
namespace FourPlayerOverlappingPeriodThree

abbrev Player := Fin 4
abbrev HazardCoordinate := Fin 8
abbrev RewardRow := Fin 15
abbrev NormalizedCoordinate := Fin 68

/-- The chart uses the canonical binary-mask coalition enumeration. -/
abbrev coalitionOfRow := Math.Finset.finFourCoalitionOfRow
abbrev coalitionOfRow_nonempty := Math.Finset.finFourCoalitionOfRow_nonempty
abbrev coalitionRowEquiv := Math.Finset.finFourCoalitionRowEquiv

/-- Sixty independent reward coordinates, indexed by coalition row and
player. -/
abbrev RewardCoordinates := RewardRow → Player → ℝ

/-- Convert sixty row coordinates to the project's quitting-reward type. -/
def rewardOfCoordinates (reward : RewardCoordinates) :
    {coalition : Finset Player // coalition.Nonempty} → Payoff Player :=
  fun coalition who ↦ reward (coalitionRowEquiv.symm coalition) who

/-- Read an arbitrary quitting reward as sixty row coordinates. -/
def coordinatesOfReward
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player) :
    RewardCoordinates :=
  fun row who ↦ reward (coalitionRowEquiv row) who

@[simp] theorem rewardOfCoordinates_coordinatesOfReward
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player) :
    rewardOfCoordinates (coordinatesOfReward reward) = reward := by
  funext coalition who
  simp [rewardOfCoordinates, coordinatesOfReward]

@[simp] theorem coordinatesOfReward_rewardOfCoordinates
    (reward : RewardCoordinates) :
    coordinatesOfReward (rewardOfCoordinates reward) = reward := by
  funext row who
  simp [rewardOfCoordinates, coordinatesOfReward]

/-- The literal rational reward rows of the overlapping-support example. -/
def overlappingPeriodThreeRewardRow (row : RewardRow) : Player → ℚ :=
  match row.val with
  | 0 => ![1, 4, 0, 0]
  | 1 => ![4, 1, 0, 0]
  | 2 => ![1, 1, 1, 1]
  | 3 => ![0, 0, 1, 4]
  | 4 => ![1, -5 / 2, 1, 2]
  | 5 => ![0, 1, 1, 1]
  | 6 => ![1, -4, 0, 0]
  | 7 => ![0, 0, 4, 1]
  | 8 => ![1, 0, 1, 1]
  | 9 => ![2, 1, 16, 1]
  | 10 => ![0, 7, 0, 0]
  | 11 => ![1, 1, 1, 1]
  | 12 => ![0, 0, 0, 4]
  | 13 => ![0, 0, 17, 0]
  | _ => ![-1, -1, -1, -1]

/-- The complete rational table, stated as one literal function equality. -/
theorem overlappingPeriodThreeRewardRow_values :
    overlappingPeriodThreeRewardRow =
      ![![1, 4, 0, 0],
        ![4, 1, 0, 0],
        ![1, 1, 1, 1],
        ![0, 0, 1, 4],
        ![1, -5 / 2, 1, 2],
        ![0, 1, 1, 1],
        ![1, -4, 0, 0],
        ![0, 0, 4, 1],
        ![1, 0, 1, 1],
        ![2, 1, 16, 1],
        ![0, 7, 0, 0],
        ![1, 1, 1, 1],
        ![0, 0, 0, 4],
        ![0, 0, 17, 0],
        ![-1, -1, -1, -1]] := by
  funext row who
  fin_cases row <;> fin_cases who <;>
    norm_num [overlappingPeriodThreeRewardRow]

/-- The literal rational table as a real quitting reward. -/
def overlappingPeriodThreeReward :
    {coalition : Finset Player // coalition.Nonempty} → Payoff Player :=
  rewardOfCoordinates fun row who ↦ overlappingPeriodThreeRewardRow row who

end FourPlayerOverlappingPeriodThree
end GameTheory

end

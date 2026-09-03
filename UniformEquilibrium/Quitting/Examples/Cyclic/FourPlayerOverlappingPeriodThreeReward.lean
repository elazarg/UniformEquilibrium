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

/-- Binary-mask enumeration of the fifteen nonempty coalitions. -/
def coalitionOfRow (row : RewardRow) : Finset Player :=
  match row.val with
  | 0 => {0}
  | 1 => {1}
  | 2 => {0, 1}
  | 3 => {2}
  | 4 => {0, 2}
  | 5 => {1, 2}
  | 6 => {0, 1, 2}
  | 7 => {3}
  | 8 => {0, 3}
  | 9 => {1, 3}
  | 10 => {0, 1, 3}
  | 11 => {2, 3}
  | 12 => {0, 2, 3}
  | 13 => {1, 2, 3}
  | _ => {0, 1, 2, 3}

theorem coalitionOfRow_nonempty (row : RewardRow) :
    (coalitionOfRow row).Nonempty := by
  fin_cases row <;> simp [coalitionOfRow]

/-- The row enumeration as an equivalence with nonempty coalitions. -/
def coalitionRowEquiv : RewardRow ≃
    {coalition : Finset Player // coalition.Nonempty} :=
  Equiv.ofBijective (fun row ↦ ⟨coalitionOfRow row, coalitionOfRow_nonempty row⟩) <| by
    rw [Fintype.bijective_iff_injective_and_card]
    constructor
    · decide
    · change 15 = Fintype.card {coalition : Finset Player // coalition.Nonempty}
      decide

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

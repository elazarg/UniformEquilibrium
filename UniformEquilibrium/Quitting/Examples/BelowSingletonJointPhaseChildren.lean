import UniformEquilibrium.Quitting.Examples.BelowSingletonJointPhaseFixture
import UniformEquilibrium.Quitting.Classification.BlockDeletion
import UniformEquilibrium.Quitting.Classification.QuietExtension.PureAbsorbingChildDebtObstruction
import UniformEquilibrium.Quitting.Stationary.JointNeverMass

/-! # All fourteen proper children of the below-singleton fixture

Each literal child has an exact pure stationary terminal Nash profile with
zero joint Never probability. Its actual quiet lift admits a profitable
omitted-player Quit-now deviation. These chosen witnesses do not assert that
every equilibrium of a child has a bad lift.
-/

noncomputable section

namespace GameTheory.BelowSingletonJointPhaseFixture

open QuittingSureSetOwnerRepair
open scoped BigOperators

def childSet (row : Fin 14) : Finset (Fin 4) :=
  Math.Finset.finFourCoalitionOfRow row.castSucc

def childExitSet (row : Fin 14) : Finset (Fin 4) :=
  match row.val with
  | 0 => {0}
  | 1 => {1}
  | 2 => {0}
  | 3 => {2}
  | 4 => {0}
  | 5 => {1, 2}
  | 6 => {0}
  | 7 => {3}
  | 8 => {0, 3}
  | 9 => {1}
  | 10 => {1}
  | 11 => {2}
  | 12 => {2}
  | _ => {3}

def childOutside (row : Fin 14) : Fin 4 :=
  (![3, 2, 3, 1, 3, 0, 3, 0, 1, 2, 2, 1, 1, 0] : Fin 14 → Fin 4) row

theorem childExit_nonempty (row : Fin 14) : (childExitSet row).Nonempty := by
  fin_cases row <;> simp [childExitSet]

theorem childExit_subset (row : Fin 14) : childExitSet row ⊆ childSet row := by
  fin_cases row <;> decide

theorem childOutside_not_mem (row : Fin 14) : childOutside row ∉ childSet row := by
  fin_cases row <;> decide

theorem child_insertion_and_withdrawal (row : Fin 14) (player : Fin 4)
    (hplayer : player ∈ childSet row) :
    quittingSetReward reward ((childExitSet row).erase player) player ≤
        quittingSetReward reward (childExitSet row) player ∧
      quittingSetReward reward (insert player (childExitSet row)) player ≤
        quittingSetReward reward (childExitSet row) player := by
  fin_cases row <;> fin_cases player
  all_goals
    norm_num +decide [childSet, childExitSet, Math.Finset.finFourCoalitionOfRow,
      quittingSetReward, reward, Math.FiniteCoalition.binaryCode_finFour]
      at hplayer
  all_goals
    norm_num +decide [childExitSet, quittingSetReward, reward,
      Math.FiniteCoalition.binaryCode_finFour]

theorem childSet_covers_all_proper (selected : Finset (Fin 4))
    (hnonempty : selected.Nonempty) (hproper : selected ≠ Finset.univ) :
    ∃ row : Fin 14, childSet row = selected :=
  Math.Finset.finFour_properNonemptyCoalition_row selected hnonempty hproper

theorem childOutside_gain_eq (row : Fin 14) :
    quittingSetReward reward (insert (childOutside row) (childExitSet row))
        (childOutside row) -
      quittingSetReward reward (childExitSet row) (childOutside row) =
        if row = 5 ∨ row = 8 then 100 else 1 / 2 := by
  fin_cases row <;>
    norm_num +decide [childOutside, childExitSet, quittingSetReward, reward,
      Math.FiniteCoalition.binaryCode_finFour]

theorem childOutside_gain (row : Fin 14) :
    (1 / 2 : ℝ) ≤
      quittingSetReward reward (insert (childOutside row) (childExitSet row))
          (childOutside row) -
        quittingSetReward reward (childExitSet row) (childOutside row) := by
  rw [childOutside_gain_eq]
  split_ifs <;> norm_num

/-- Withdrawal at a singleton background may use any supplied fallback. -/
def childWithdrawalValue (row : Fin 14) (fallback : Fin 4 → ℝ) (player : Fin 4) : ℝ :=
  if ((childExitSet row).erase player).Nonempty then
    quittingSetReward reward ((childExitSet row).erase player) player
  else fallback player

theorem child_raw_joining_gain_eq (row : Fin 14) (player : Fin 4)
    (hplayer : player ∈ childSet row) :
    quittingSetReward reward (insert player (childExitSet row)) player -
      quittingSetReward reward (childExitSet row) player =
        if player ∈ childExitSet row then 0 else
          if player = Math.CrossedMatching.favorite (Math.CrossedMatching.other
            (childOutside row)) then -7 / 2 else -1 / 10 := by
  fin_cases row <;> fin_cases player
  all_goals
    norm_num +decide [childSet, Math.Finset.finFourCoalitionOfRow] at hplayer
  all_goals
    norm_num +decide [childExitSet, childOutside, quittingSetReward, reward,
      Math.FiniteCoalition.binaryCode_finFour, Math.CrossedMatching.favorite,
      Math.CrossedMatching.other]

theorem child_raw_withdrawal_gain_eq (row : Fin 14) (fallback : Fin 4 → ℝ)
    (player : Fin 4) (hplayer : player ∈ childSet row) :
    childWithdrawalValue row fallback player -
      quittingSetReward reward (childExitSet row) player =
        if player ∈ childExitSet row then
          if row = 5 ∨ row = 8 then -1 / 2 else fallback player - 1
        else 0 := by
  fin_cases row <;> fin_cases player
  all_goals
    norm_num +decide [childSet, Math.Finset.finFourCoalitionOfRow] at hplayer
  all_goals
    norm_num +decide [childWithdrawalValue, childExitSet, quittingSetReward,
      reward, Math.FiniteCoalition.binaryCode_finFour]

theorem child_raw_joining_gain_nonpos (row : Fin 14) (player : Fin 4)
    (hplayer : player ∈ childSet row) :
    quittingSetReward reward (insert player (childExitSet row)) player -
      quittingSetReward reward (childExitSet row) player ≤ 0 :=
  sub_nonpos.mpr (child_insertion_and_withdrawal row player hplayer).2

theorem child_raw_withdrawal_gain_nonpos (row : Fin 14) (fallback : Fin 4 → ℝ)
    (player : Fin 4) (hfallback : fallback player ≤ 1)
    (hplayer : player ∈ childSet row) :
    childWithdrawalValue row fallback player -
      quittingSetReward reward (childExitSet row) player ≤ 0 := by
  rw [child_raw_withdrawal_gain_eq row fallback player hplayer]
  split_ifs <;> norm_num
  exact hfallback

/-- Literal raw joining and withdrawal rows cannot charge the omitted gain.
Unlike exact child debts, these merely nonpositive rows require nonnegative weights. -/
theorem child_raw_weighted_row_failure (row : Fin 14) (fallback : Fin 4 → ℝ)
    (hfallback : ∀ player ∈ childSet row, fallback player ≤ 1)
    (joiningWeight withdrawalWeight : Fin 4 → ℝ)
    (hjoining : ∀ player ∈ childSet row, 0 ≤ joiningWeight player)
    (hwithdrawal : ∀ player ∈ childSet row, 0 ≤ withdrawalWeight player) :
    (∑ player ∈ childSet row,
      (joiningWeight player *
        (quittingSetReward reward (insert player (childExitSet row)) player -
          quittingSetReward reward (childExitSet row) player) +
      withdrawalWeight player *
        (childWithdrawalValue row fallback player -
          quittingSetReward reward (childExitSet row) player))) <
      quittingSetReward reward (insert (childOutside row) (childExitSet row))
          (childOutside row) -
        quittingSetReward reward (childExitSet row) (childOutside row) := by
  have hsum : (∑ player ∈ childSet row,
      (joiningWeight player *
        (quittingSetReward reward (insert player (childExitSet row)) player -
          quittingSetReward reward (childExitSet row) player) +
      withdrawalWeight player *
        (childWithdrawalValue row fallback player -
          quittingSetReward reward (childExitSet row) player))) ≤ 0 := by
    apply Finset.sum_nonpos
    intro player hplayer
    exact add_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (hjoining player hplayer)
        (child_raw_joining_gain_nonpos row player hplayer))
      (mul_nonpos_of_nonneg_of_nonpos (hwithdrawal player hplayer)
        (child_raw_withdrawal_gain_nonpos row fallback player
          (hfallback player hplayer) hplayer))
  exact hsum.trans_lt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
    (childOutside_gain row))

abbrev Child (row : Fin 14) := QuittingBlockSurvivor (childSet row)ᶜ

def childActive (row : Fin 14) : Finset (Child row) :=
  (childExitSet row).subtype (fun player => player ∉ (childSet row)ᶜ)

theorem childActive_map (row : Fin 14) :
    (childActive row).map (Function.Embedding.subtype
      (p := fun player : Fin 4 => player ∉ (childSet row)ᶜ)) = childExitSet row := by
  apply Finset.subtype_map_of_mem
  intro player hplayer
  simpa using childExit_subset row hplayer

theorem childActive_nonempty (row : Fin 14) : (childActive row).Nonempty := by
  apply Finset.map_nonempty.mp
  rw [childActive_map]
  exact childExit_nonempty row

def childReward (row : Fin 14) := quittingDeleteBlockReward reward (childSet row)ᶜ

def childProfile (row : Fin 14) : (quittingGame (childReward row)).BehaviorProfile :=
  quittingStationaryProfile (childReward row) (quittingPureSetRoot (childActive row))

theorem child_terminalNash (row : Fin 14) :
    (quittingGame (childReward row)).IsεAsymptoticNash
      (quittingTerminalPayoff (childReward row)) 0 (childProfile row) := by
  apply (isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet _ _).mpr
  apply (isQuittingSureExitSet_deleteBlockReward_iff reward (childSet row)ᶜ _).mpr
  rw [childActive_map]
  constructor
  · intro player hplayer
    exact (child_insertion_and_withdrawal row player
      (childExit_subset row hplayer)).1
  · intro player hplayer _
    exact (child_insertion_and_withdrawal row player (by simpa using hplayer)).2

theorem child_jointNever_eq_zero (row : Fin 14) :
    (∏ player, (quittingBehaviorStoppingLaw (childReward row)
      (childProfile row player) none).toReal) = 0 := by
  apply prod_stoppingLaw_none_stationary_eq_zero
  rw [stationaryContinueMass_pureSetRoot_of_nonempty (childActive_nonempty row)]
  norm_num

def childQuietLift (row : Fin 14) : (quittingGame reward).BehaviorProfile :=
  quittingLiftDeletedProfile reward (fun player => player ∈ (childSet row)ᶜ)
    (childProfile row)

theorem childQuietLift_eq (row : Fin 14) :
    childQuietLift row =
      quittingStationaryProfile reward (quittingPureSetRoot (childExitSet row)) := by
  unfold childQuietLift childProfile childReward
  rw [quittingLiftDeletedProfile_stationary_pureSetRoot, childActive_map]

theorem childQuietLift_quitNow_gain_eq (row : Fin 14) :
    quittingTerminalPayoff reward
        (Function.update (childQuietLift row) (childOutside row)
          (quittingPureTimeBehaviorStrategy reward (childOutside row) (some 0)))
        (childOutside row) -
      quittingTerminalPayoff reward (childQuietLift row) (childOutside row) =
        if row = 5 ∨ row = 8 then 100 else 1 / 2 := by
  rw [childQuietLift_eq, quittingTerminalPayoff_update_pureSetRoot_quitNow,
    quittingTerminalPayoff_pureSetRoot]
  exact childOutside_gain_eq row

/-- All real debt weights and finite Never charges fail at this chosen child. -/
theorem childQuietLift_gain_gt_all_weighted_debt (row : Fin 14)
    (weight : Child row → ℝ) (neverCoefficient : ℝ) :
    (∑ player, weight player *
      (quittingBehaviorDeviationPayoffCap (childReward row) (childProfile row) player -
        quittingTerminalPayoff (childReward row) (childProfile row) player)) +
      neverCoefficient * (∏ player, (quittingBehaviorStoppingLaw (childReward row)
        (childProfile row player) none).toReal) <
      quittingTerminalPayoff reward
          (Function.update (childQuietLift row) (childOutside row)
            (quittingPureTimeBehaviorStrategy reward (childOutside row) (some 0)))
          (childOutside row) -
        quittingTerminalPayoff reward (childQuietLift row) (childOutside row) := by
  apply quietLift_gain_gt_weighted_childDebt_add_never_of_exact_child
    reward (fun player => player ∈ (childSet row)ᶜ) (childProfile row)
    (child_terminalNash row) (child_jointNever_eq_zero row)
    ⟨childOutside row, by simpa using childOutside_not_mem row⟩
    (quittingPureTimeBehaviorStrategy reward (childOutside row) (some 0))
    _ weight neverCoefficient
  change 0 < quittingTerminalPayoff reward
      (Function.update (childQuietLift row) (childOutside row)
        (quittingPureTimeBehaviorStrategy reward (childOutside row) (some 0)))
      (childOutside row) -
    quittingTerminalPayoff reward (childQuietLift row) (childOutside row)
  rw [childQuietLift_quitNow_gain_eq]
  split_ifs <;> norm_num

/-- Every proper nonempty child has one actual absorbing Nash witness with unsafe lift. -/
theorem exists_unsafe_witness_for_every_proper_child (selected : Finset (Fin 4))
    (hnonempty : selected.Nonempty) (hproper : selected ≠ Finset.univ) :
    ∃ row : Fin 14, childSet row = selected ∧
      (quittingGame (childReward row)).IsεAsymptoticNash
        (quittingTerminalPayoff (childReward row)) 0 (childProfile row) ∧
      (∏ player, (quittingBehaviorStoppingLaw (childReward row)
        (childProfile row player) none).toReal) = 0 ∧
      ∀ (weight : Child row → ℝ) (neverCoefficient : ℝ),
        (∑ player, weight player *
          (quittingBehaviorDeviationPayoffCap (childReward row) (childProfile row) player -
            quittingTerminalPayoff (childReward row) (childProfile row) player)) +
          neverCoefficient * (∏ player, (quittingBehaviorStoppingLaw (childReward row)
            (childProfile row player) none).toReal) <
          quittingTerminalPayoff reward
              (Function.update (childQuietLift row) (childOutside row)
                (quittingPureTimeBehaviorStrategy reward (childOutside row) (some 0)))
              (childOutside row) -
            quittingTerminalPayoff reward (childQuietLift row) (childOutside row) := by
  obtain ⟨row, hrow⟩ := childSet_covers_all_proper selected hnonempty hproper
  exact ⟨row, hrow, child_terminalNash row, child_jointNever_eq_zero row,
    childQuietLift_gain_gt_all_weighted_debt row⟩

end GameTheory.BelowSingletonJointPhaseFixture

import UniformEquilibrium.Quitting.Examples.GuardedCrossedResponseTables
import UniformEquilibrium.Quitting.Examples.FinFourLastPlayerChild
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalRaw

/-! # The complete strict deadline-withdrawal reward table

The row translation defines this new game's data. It is not a claim of
strategic equivalence: the canonical payoff on joint Never remains zero.
The child is the literal deletion of player index 3 from the actual table.
-/

noncomputable section

namespace GameTheory.StrictDeadlineWithdrawal

open GuardedCrossedResponseExamples FinFourLastPlayerChild
open scoped BigOperators

def integerReward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun terminal => match coalitionCode terminal.1 with
    | 1 => ![1, 3, -1, -1]
    | 2 => ![4, 0, -1, -1]
    | 3 => ![0, 0, -1, 0]
    | 4 => ![0, -1, 0, 3]
    | 5 => ![1, 0, 0, 1]
    | 6 => ![2, -2, 0, 1]
    | 7 => ![0, 1, -1, 0]
    | 8 => ![0, -1, 3, 0]
    | 9 => ![0, -1, 0, -1]
    | 10 => ![0, 0, 0, 0]
    | 11 => ![1, 0, -1, 0]
    | 12 => ![0, 1, 1, 1]
    | 13 => ![0, 0, 0, -1]
    | 14 => ![1, 0, 0, 0]
    | 15 => ![0, 1, 0, 1]
    | _ => 0

def terminalShift : Fin 4 → ℝ := ![0, 1 / 16, 1 / 16, 1 / 16]

def reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun terminal who => integerReward terminal who - terminalShift who

def advanceWeight (who : Child) : ℝ :=
  if who = child 0 then 1 / 8 else if who = child 2 then 2 else 0

def withdrawalWeight (who : Child) : ℝ := if who = child 0 then 1 else 0

theorem advanceWeight_nonneg (who : Child) : 0 ≤ advanceWeight who := by
  unfold advanceWeight
  split_ifs <;> norm_num

theorem withdrawalWeight_nonneg (who : Child) : 0 ≤ withdrawalWeight who := by
  unfold withdrawalWeight
  split_ifs <;> norm_num

theorem sum_advanceWeight : (∑ who, advanceWeight who) = 17 / 8 := by
  norm_num [sum_child, advanceWeight, child]

theorem sum_withdrawalWeight : (∑ who, withdrawalWeight who) = 1 := by
  norm_num [sum_child, withdrawalWeight, child]

theorem max_weights (who : Child) :
    max (advanceWeight who) (withdrawalWeight who) =
      if who = child 0 then 1 else if who = child 2 then 2 else 0 := by
  fin_cases who <;> norm_num [advanceWeight, withdrawalWeight, child]

theorem singleton_payoffs (who : Fin 4) :
    reward ⟨{who}, Finset.singleton_nonempty who⟩ who = ![1, -1 / 16, -1 / 16, -1 / 16] who := by
  fin_cases who <;> norm_num [reward, integerReward, terminalShift, coalitionCode]

/-- The positive-weight player's fresh canonical zero-or-passive floor is zero. -/
theorem zeroFloor_playerZero :
    deadlineWithdrawalZeroFloor (childReward reward) (child 0) = 0 := by
  classical
  apply le_antisymm (deadlineWithdrawalZeroFloor_le_zero _ _)
  unfold deadlineWithdrawalZeroFloor
  apply (Finset.le_min'_iff _ _).mpr
  intro value hvalue
  rcases Finset.mem_insert.mp hvalue with rfl | hpassive
  · exact le_rfl
  · obtain ⟨B, _, rfl⟩ := Finset.mem_image.mp hpassive
    obtain ⟨A, hA, hnot⟩ := B
    obtain ⟨index, rfl⟩ := exists_coalition_index A hA
    fin_cases index
    all_goals norm_num [coalition, child] at hnot
    all_goals norm_num [childReward_childCoalition_image, reward, integerReward,
      terminalShift, coalitionCode, coalition, child]

end GameTheory.StrictDeadlineWithdrawal

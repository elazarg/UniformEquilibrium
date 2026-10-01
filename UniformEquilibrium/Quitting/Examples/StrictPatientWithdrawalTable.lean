import UniformEquilibrium.Quitting.Examples.GuardedCrossedResponseTables
import UniformEquilibrium.Quitting.Examples.FinFourLastPlayerChild
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockSampledLPDual
import UniformEquilibrium.Quitting.Classification.QuietExtension.PatientWithdrawalRaw

/-! # The complete strict patient-withdrawal table

All sixty terminal reward coordinates are literal data. Never remains zero
under the canonical quitting-game semantics. The child is the actual deletion
of player three, not an independently supplied three-player fixture.
-/

noncomputable section

namespace GameTheory.StrictPatientWithdrawal

open GuardedCrossedResponseExamples
open scoped BigOperators

def reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun terminal => match coalitionCode terminal.1 with
    | 1 => ![1, 3, -1, -1]
    | 2 => ![4, 0, -1, -1]
    | 3 => ![2, 4, -1, -3]
    | 4 => ![0, -1, 0, 3]
    | 5 => ![2, -1, -2, -4]
    | 6 => ![0, -2, 1, 5]
    | 7 => ![-3, 0, 0, 0]
    | 8 => ![0, -1, 3, 0]
    | 9 => ![2, -1, -1, -6]
    | 10 => ![0, 1, -1, 3]
    | 11 => ![1, 0, 1, -4]
    | 12 => ![0, -1, 1, 1]
    | 13 => ![1, -1, 0, -6]
    | 14 => ![0, 0, 0, 3]
    | 15 => ![1, 0, -1, 1 / 2]
    | _ => 0

abbrev Child := FinFourLastPlayerChild.Child
abbrev child := FinFourLastPlayerChild.child
abbrev outside := FinFourLastPlayerChild.outside
abbrev childReward := FinFourLastPlayerChild.childReward

theorem childReward_childCoalition
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (A : Finset Child) (hA : A.Nonempty) (who : Child) :
    childReward table
        ⟨cappedClockChildCoalition A, cappedClockChildCoalition_nonempty hA⟩ (some who) =
      table ⟨A.map (Function.Embedding.subtype (p := fun who : Fin 4 => who ≠ 3)),
        Finset.map_nonempty.mpr hA⟩ who.1 :=
  FinFourLastPlayerChild.childReward_childCoalition table A hA who

theorem childReward_childCoalition_image
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (A : Finset Child) (hA : A.Nonempty) (who : Child) :
    childReward table
        ⟨cappedClockChildCoalition A, cappedClockChildCoalition_nonempty hA⟩ (some who) =
      table ⟨A.image (fun player : Child => player.1), hA.image (fun player => player.1)⟩
        who.1 :=
  FinFourLastPlayerChild.childReward_childCoalition_image table A hA who

theorem sum_child (function : Child → ℝ) :
    ∑ who, function who = function (child 0) + function (child 1) + function (child 2) :=
  FinFourLastPlayerChild.sum_child function

abbrev coalition := FinFourLastPlayerChild.coalition

theorem coalition_nonempty (index : Fin 7) : (coalition index).Nonempty :=
  FinFourLastPlayerChild.coalition_nonempty index

theorem exists_coalition_index (A : Finset Child) (hA : A.Nonempty) :
    ∃ index, A = coalition index :=
  FinFourLastPlayerChild.exists_coalition_index A hA

def advanceWeight (who : Child) : ℝ := if who = child 2 then 3 else 0
def withdrawalWeight (who : Child) : ℝ := if who = child 0 then 1 / 2 else 0

theorem advanceWeight_nonneg (who : Child) : 0 ≤ advanceWeight who := by
  unfold advanceWeight
  split_ifs <;> norm_num

theorem withdrawalWeight_nonneg (who : Child) : 0 ≤ withdrawalWeight who := by
  unfold withdrawalWeight
  split_ifs <;> norm_num

theorem singleton_payoffs (who : Fin 4) :
    reward ⟨{who}, Finset.singleton_nonempty who⟩ who = ![1, 0, 0, 0] who := by
  fin_cases who <;> norm_num [reward, coalitionCode]

theorem ownNeverAlternative (who : Child) :
    patientWithdrawalOwnNeverAlternative (childReward reward) who =
      if who = child 0 then 1 else 0 := by
  fin_cases who <;> norm_num [patientWithdrawalOwnNeverAlternative, childReward,
    quittingChildWithOutsiderReward_apply_original, reward, coalitionCode, child]

/-- The fresh canonical patient minima are exactly the printed vector (0,-1,-1). -/
theorem patientFloor (who : Child) :
    patientWithdrawalFloor (childReward reward) who =
      if who = child 0 then 0 else -1 := by
  classical
  apply le_antisymm
  · fin_cases who
    all_goals first
    | exact (patientWithdrawalFloor_le_passiveReward (childReward reward) _
        {child 2} (by decide) (by decide)).trans_eq (by
          norm_num [childReward_childCoalition_image, reward, coalitionCode, child])
    | exact (patientWithdrawalFloor_le_passiveReward (childReward reward) _
        {child 0} (by decide) (by decide)).trans_eq (by
          norm_num [childReward_childCoalition_image, reward, coalitionCode, child])
  · unfold patientWithdrawalFloor
    apply (Finset.le_min'_iff _ _).mpr
    intro value hvalue
    rcases Finset.mem_insert.mp hvalue with rfl | hpassive
    · rw [ownNeverAlternative]
      split_ifs <;> norm_num
    · obtain ⟨B, _, rfl⟩ := Finset.mem_image.mp hpassive
      obtain ⟨B, hB, hnot⟩ := B
      fin_cases who
      all_goals fin_cases B
      all_goals norm_num at hB
      all_goals norm_num [child] at hnot
      all_goals norm_num [childReward_childCoalition_image, reward, coalitionCode, child]

/-- At the full child coalition, player zero's actual withdrawal gain is three. -/
theorem withdrawalGain_fullChild_playerZero_eq_three :
    patientWithdrawalGainFloor (childReward reward) (child 0)
      (coalition 6) (coalition_nonempty 6) = 3 := by
  norm_num +decide [patientWithdrawalGainFloor, deadlineSecurityGainFloorWithRestart,
    deadlineWithdrawalGainFloor, childReward_childCoalition, reward, coalitionCode, child,
    coalition, Function.Embedding.subtype, Function.Embedding.coeFn_mk]

end GameTheory.StrictPatientWithdrawal

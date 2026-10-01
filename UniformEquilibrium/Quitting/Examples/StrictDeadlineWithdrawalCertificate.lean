import UniformEquilibrium.Quitting.Examples.StrictDeadlineWithdrawalTable

/-! # Exact N/F/J slacks for the strict deadline fixture

Future rows are advancing-only. The fresh zero-or-passive withdrawal gain
appears in joining rows only, exactly as in the canonical raw certificate.
All seven actual child coalitions are covered by the shared finite enumeration.
-/

noncomputable section

namespace GameTheory.StrictDeadlineWithdrawal

open GuardedCrossedResponseExamples FinFourLastPlayerChild
open scoped BigOperators

def neverSlack (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) : ℝ :=
  (∑ who, advanceWeight who *
    childReward table ⟨{some who}, Finset.singleton_nonempty (some who)⟩ (some who)) -
    childReward table ⟨{none}, Finset.singleton_nonempty none⟩ none

def futureSlack (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (A : Finset Child) (hA : A.Nonempty) : ℝ :=
  (∑ who, advanceWeight who * cappedClockExactLPDelta (childReward table)
    (.future ⟨A, hA⟩) who) - cappedClockExactLPBase (childReward table) (.future ⟨A, hA⟩)

def joiningSlack (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (A : Finset Child) (hA : A.Nonempty) : ℝ :=
  (∑ who, (advanceWeight who * cappedClockExactLPDelta (childReward table)
      (.joining ⟨A, hA⟩) who +
    withdrawalWeight who * deadlineWithdrawalGainFloor (childReward table) who A hA)) -
    cappedClockExactLPBase (childReward table) (.joining ⟨A, hA⟩)

def futureSlacks : Fin 7 → ℝ := ![1, 5 / 8, 17 / 8, 25 / 8, 1, 7 / 8, 17 / 8]
def joiningSlacks : Fin 7 → ℝ := ![1, 1 / 2, 4, 17 / 8, 1, 3 / 4, 1]

theorem neverSlack_reduced
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    neverSlack table =
      (1 / 8) * childReward table ⟨{some (child 0)}, Finset.singleton_nonempty _⟩
          (some (child 0)) +
        2 * childReward table ⟨{some (child 2)}, Finset.singleton_nonempty _⟩
          (some (child 2)) -
        childReward table ⟨{none}, Finset.singleton_nonempty _⟩ none := by
  simp [neverSlack, sum_child, advanceWeight, child]

theorem neverSlack_eq : neverSlack reward = 1 / 16 := by
  norm_num [neverSlack, sum_child, advanceWeight,
    quittingChildWithOutsiderReward_singleton_original,
    quittingChildWithOutsiderOriginalEmbedding_some,
    quittingChildWithOutsiderOriginalEmbedding_none,
    reward, integerReward, terminalShift, coalitionCode, child, outside]

private theorem future_delta_zero_eq (index : Fin 7) :
    cappedClockExactLPDelta (childReward reward)
      (.future ⟨coalition index, coalition_nonempty index⟩) (child 0) =
      ![0, -3, 1, 1, 0, -1, 1] index := by
  fin_cases index
  all_goals dsimp only [cappedClockExactLPDelta]
  all_goals norm_num +decide [childReward_childCoalition_image,
    quittingChildWithOutsiderReward_singleton_original,
    quittingChildWithOutsiderOriginalEmbedding_some,
    reward, integerReward, terminalShift, coalitionCode, child, coalition]

private theorem future_delta_two_eq (index : Fin 7) :
    cappedClockExactLPDelta (childReward reward)
      (.future ⟨coalition index, coalition_nonempty index⟩) (child 2) =
      ![1, 1, 1, 0, 0, 0, 1] index := by
  fin_cases index
  all_goals dsimp only [cappedClockExactLPDelta]
  all_goals norm_num +decide [childReward_childCoalition_image,
    quittingChildWithOutsiderReward_singleton_original,
    quittingChildWithOutsiderOriginalEmbedding_some,
    reward, integerReward, terminalShift, coalitionCode, child, coalition]

private theorem future_base_eq (index : Fin 7) :
    cappedClockExactLPBase (childReward reward)
      (.future ⟨coalition index, coalition_nonempty index⟩) =
      ![1, 1, 0, -3, -1, -1, 0] index := by
  fin_cases index
  all_goals dsimp only [cappedClockExactLPBase]
  all_goals norm_num +decide [quittingChildWithOutsiderReward_childCoalition_image,
    quittingChildWithOutsiderReward_singleton_original,
    quittingChildWithOutsiderOriginalEmbedding_none,
    reward, integerReward, terminalShift, coalitionCode, child, coalition, outside]

private theorem joining_delta_zero_eq (index : Fin 7) :
    cappedClockExactLPDelta (childReward reward)
      (.joining ⟨coalition index, coalition_nonempty index⟩) (child 0) =
      ![0, -4, 0, 1, 0, -2, 0] index := by
  fin_cases index
  all_goals dsimp only [cappedClockExactLPDelta]
  all_goals norm_num +decide [childReward_childCoalition_image,
    reward, integerReward, terminalShift, coalitionCode, child, coalition]

private theorem joining_delta_two_eq (index : Fin 7) :
    cappedClockExactLPDelta (childReward reward)
      (.joining ⟨coalition index, coalition_nonempty index⟩) (child 2) =
      ![1, 1, 0, 0, 0, 0, 0] index := by
  fin_cases index
  all_goals dsimp only [cappedClockExactLPDelta]
  all_goals norm_num +decide [childReward_childCoalition_image,
    reward, integerReward, terminalShift, coalitionCode, child, coalition]

private theorem joining_base_eq (index : Fin 7) :
    cappedClockExactLPBase (childReward reward)
      (.joining ⟨coalition index, coalition_nonempty index⟩) =
      ![0, 1, 0, -2, -2, -1, 1] index := by
  fin_cases index
  all_goals dsimp only [cappedClockExactLPBase]
  all_goals norm_num +decide [quittingChildWithOutsiderReward_joinedCoalition_image,
    quittingChildWithOutsiderReward_childCoalition_image,
    quittingChildWithOutsiderOriginalEmbedding_none,
    reward, integerReward, terminalShift, coalitionCode, child, coalition, outside]

private theorem withdrawalGain_zero_eq (index : Fin 7) :
    deadlineWithdrawalGainFloor (childReward reward) (child 0)
      (coalition index) (coalition_nonempty index) = ![-1, 0, 4, 0, -1, 0, 2] index := by
  fin_cases index
  · change deadlineWithdrawalGainFloor (childReward reward) (child 0) {child 0}
      (Finset.singleton_nonempty (child 0)) = -1
    rw [deadlineWithdrawalGainFloor_singleton, zeroFloor_playerZero]
    norm_num [quittingChildWithOutsiderReward_singleton_original,
      quittingChildWithOutsiderOriginalEmbedding_some,
      reward, integerReward, terminalShift, coalitionCode, child]
  all_goals norm_num +decide [deadlineWithdrawalGainFloor,
    childReward_childCoalition_image,
    reward, integerReward, terminalShift, coalitionCode, child, coalition]

theorem futureSlack_reduced
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (A : Finset Child) (hA : A.Nonempty) :
    futureSlack table A hA =
      (1 / 8) * cappedClockExactLPDelta (childReward table) (.future ⟨A, hA⟩) (child 0) +
        2 * cappedClockExactLPDelta (childReward table) (.future ⟨A, hA⟩) (child 2) -
        cappedClockExactLPBase (childReward table) (.future ⟨A, hA⟩) := by
  simp [futureSlack, sum_child, advanceWeight, child]

theorem joiningSlack_reduced
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (A : Finset Child) (hA : A.Nonempty) :
    joiningSlack table A hA =
      (1 / 8) * cappedClockExactLPDelta (childReward table) (.joining ⟨A, hA⟩) (child 0) +
        deadlineWithdrawalGainFloor (childReward table) (child 0) A hA +
        2 * cappedClockExactLPDelta (childReward table) (.joining ⟨A, hA⟩) (child 2) -
        cappedClockExactLPBase (childReward table) (.joining ⟨A, hA⟩) := by
  simp [joiningSlack, sum_child, advanceWeight, withdrawalWeight, child]

theorem futureSlack_eq (index : Fin 7) :
    futureSlack reward (coalition index) (coalition_nonempty index) = futureSlacks index := by
  rw [futureSlack_reduced, future_delta_zero_eq, future_delta_two_eq, future_base_eq]
  fin_cases index <;> norm_num [futureSlacks]

theorem joiningSlack_eq (index : Fin 7) :
    joiningSlack reward (coalition index) (coalition_nonempty index) = joiningSlacks index := by
  rw [joiningSlack_reduced, joining_delta_zero_eq, joining_delta_two_eq,
    joining_base_eq, withdrawalGain_zero_eq]
  fin_cases index <;> norm_num [joiningSlacks]

theorem futureSlack_five_eighths_le (A : Finset Child) (hA : A.Nonempty) :
    5 / 8 ≤ futureSlack reward A hA := by
  obtain ⟨index, rfl⟩ := exists_coalition_index A hA
  rw [futureSlack_eq]
  fin_cases index <;> norm_num [futureSlacks]

theorem joiningSlack_half_le (A : Finset Child) (hA : A.Nonempty) :
    1 / 2 ≤ joiningSlack reward A hA := by
  obtain ⟨index, rfl⟩ := exists_coalition_index A hA
  rw [joiningSlack_eq]
  fin_cases index <;> norm_num [joiningSlacks]

/-- Actual table slacks produce the canonical certificate, without supplied strategic caps. -/
def certificateOfSlacks
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnever : 0 ≤ neverSlack table)
    (hfuture : ∀ A hA, 0 ≤ futureSlack table A hA)
    (hjoining : ∀ A hA, 0 ≤ joiningSlack table A hA) :
    DeadlineWithdrawalRewardCertificate (childReward table) where
  advanceWeight := advanceWeight
  withdrawalWeight := withdrawalWeight
  advanceWeight_nonneg := advanceWeight_nonneg
  withdrawalWeight_nonneg := withdrawalWeight_nonneg
  never_row := sub_nonneg.mp hnever
  future_row A hA := sub_nonneg.mp (hfuture A hA)
  join_row A hA := sub_nonneg.mp (hjoining A hA)

def certificate : DeadlineWithdrawalRewardCertificate (childReward reward) :=
  certificateOfSlacks reward (by rw [neverSlack_eq]; norm_num)
    (fun A hA => le_trans (by norm_num) (futureSlack_five_eighths_le A hA))
    (fun A hA => le_trans (by norm_num) (joiningSlack_half_le A hA))

theorem certificate_debtWeight (who : Child) :
    certificate.debtWeight who =
      if who = child 0 then 1 else if who = child 2 then 2 else 0 :=
  max_weights who

theorem sum_certificate_debtWeight : (∑ who, certificate.debtWeight who) = 3 := by
  norm_num [sum_child, certificate_debtWeight, child]

end GameTheory.StrictDeadlineWithdrawal

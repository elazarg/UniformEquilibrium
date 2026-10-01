import UniformEquilibrium.Quitting.Examples.StrictPatientWithdrawalTable

/-! # All fifteen literal patient reward rows and their exact margins -/

noncomputable section

namespace GameTheory.StrictPatientWithdrawal

open GuardedCrossedResponseExamples
open scoped BigOperators

/-- Patient N slack with the fixed displayed weights and freshly computed alternatives. -/
def neverSlack (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) : ℝ :=
  (∑ who, advanceWeight who *
    childReward table ⟨{some who}, Finset.singleton_nonempty (some who)⟩ (some who)) +
  (∑ who, withdrawalWeight who *
    patientWithdrawalOwnNeverAlternative (childReward table) who) -
    childReward table ⟨{none}, Finset.singleton_nonempty none⟩ none

/-- A literal patient F or J slack, using the canonical advancing-only row coefficients. -/
def rowSlack (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (joining : Bool) (A : Finset Child) (hA : A.Nonempty) : ℝ :=
  let row : CappedClockExactLPRow Child :=
    if joining then .joining ⟨A, hA⟩ else .future ⟨A, hA⟩
  (∑ who, (advanceWeight who * cappedClockExactLPDelta (childReward table) row who +
    withdrawalWeight who * patientWithdrawalGainFloor (childReward table) who A hA)) -
    cappedClockExactLPBase (childReward table) row

def futureSlacks : Fin 7 → ℝ := ![3 / 2, 2, 1, 3, 1, 2, 3 / 2]
def joiningSlacks : Fin 7 → ℝ := ![3 / 2, 2, 5, 2, 1, 2, 1]

private theorem childSoloImage
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (who : Child) :
    childReward table ⟨{some who}, Finset.singleton_nonempty (some who)⟩ (some who) =
      table ⟨{who.1}, Finset.singleton_nonempty who.1⟩ who.1 := by
  simp only [childReward, quittingChildWithOutsiderReward_apply_original,
    Finset.map_singleton, quittingChildWithOutsiderOriginalEmbedding_some]

private theorem childOutsideImage
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (A : Finset Child) (hA : A.Nonempty) :
    childReward table ⟨cappedClockChildCoalition A,
        cappedClockChildCoalition_nonempty hA⟩ none =
      table ⟨A.image (fun who : Child => who.1), hA.image (fun who => who.1)⟩ 3 := by
  have hmap : (cappedClockChildCoalition A).map
      (quittingChildWithOutsiderOriginalEmbedding (· = 3) outside) =
      A.image (fun who : Child => who.1) :=
    (quittingChildWithOutsiderOriginalEmbedding_childCoalition (· = 3) outside A).trans
      (Finset.map_eq_image _ A)
  simp only [childReward, quittingChildWithOutsiderReward_apply_original]
  simp only [hmap]
  simp only [quittingChildWithOutsiderOriginalEmbedding_none, outside]

private theorem joinedOutsideImage
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (A : Finset Child) :
    childReward table ⟨cappedClockJoinedCoalition A,
        cappedClockJoinedCoalition_nonempty A⟩ none =
      table ⟨insert 3 (A.image (fun who : Child => who.1)),
        Finset.insert_nonempty 3 _⟩ 3 := by
  have hmap : (cappedClockChildCoalition A).map
      (quittingChildWithOutsiderOriginalEmbedding (· = 3) outside) =
      A.image (fun who : Child => who.1) :=
    (quittingChildWithOutsiderOriginalEmbedding_childCoalition (· = 3) outside A).trans
      (Finset.map_eq_image _ A)
  have hjoined : (cappedClockJoinedCoalition A).map
      (quittingChildWithOutsiderOriginalEmbedding (· = 3) outside) =
      insert 3 (A.image (fun who : Child => who.1)) := by
    rw [cappedClockJoinedCoalition, Finset.map_insert,
      quittingChildWithOutsiderOriginalEmbedding_none]
    change insert 3 ((cappedClockChildCoalition A).map
      (quittingChildWithOutsiderOriginalEmbedding (· = 3) outside)) = _
    exact congrArg (insert 3) hmap
  simp only [childReward, quittingChildWithOutsiderReward_apply_original]
  simp only [hjoined]
  simp only [quittingChildWithOutsiderOriginalEmbedding_none, outside]

private theorem outsideSoloImage
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    childReward table ⟨{none}, Finset.singleton_nonempty none⟩ none =
      table ⟨{3}, Finset.singleton_nonempty 3⟩ 3 := by
  simp only [childReward, quittingChildWithOutsiderReward_apply_original,
    Finset.map_singleton, quittingChildWithOutsiderOriginalEmbedding_none, outside]

private theorem withdrawalGain_zero_eq (index : Fin 7) :
    patientWithdrawalGainFloor (childReward reward) (child 0)
      (coalition index) (coalition_nonempty index) = ![-1, 0, 2, 0, -2, 0, 3] index := by
  fin_cases index
  · change patientWithdrawalGainFloor (childReward reward) (child 0) {child 0}
      (Finset.singleton_nonempty (child 0)) = -1
    rw [patientWithdrawalGainFloor, deadlineSecurityGainFloor_singletonWithRestart,
      patientFloor]
    norm_num [childSoloImage, reward, coalitionCode, child]
  all_goals norm_num +decide [patientWithdrawalGainFloor,
    deadlineSecurityGainFloorWithRestart, deadlineWithdrawalGainFloor, patientFloor,
    childReward_childCoalition_image, childSoloImage, reward, coalitionCode, child, coalition]

private theorem future_delta_two_eq (index : Fin 7) :
    cappedClockExactLPDelta (childReward reward)
      (.future ⟨coalition index, coalition_nonempty index⟩) (child 2) =
      ![1, 1, 1, 0, 2, -1, 0] index := by
  fin_cases index
  all_goals dsimp only [cappedClockExactLPDelta]
  all_goals norm_num +decide [childReward_childCoalition_image, childSoloImage,
    reward, coalitionCode, child, coalition]

private theorem future_base_eq (index : Fin 7) :
    cappedClockExactLPBase (childReward reward)
      (.future ⟨coalition index, coalition_nonempty index⟩) = ![1, 1, 3, -3, 4, -5, 0] index := by
  fin_cases index
  all_goals dsimp only [cappedClockExactLPBase]
  all_goals norm_num +decide [childOutsideImage, outsideSoloImage,
    reward, coalitionCode, child, coalition]

private theorem joining_delta_two_eq (index : Fin 7) :
    cappedClockExactLPDelta (childReward reward)
      (.joining ⟨coalition index, coalition_nonempty index⟩) (child 2) =
      ![-1, 2, 1, 0, 0, 0, 0] index := by
  fin_cases index
  all_goals dsimp only [cappedClockExactLPDelta]
  all_goals norm_num +decide [childReward_childCoalition_image,
    reward, coalitionCode, child, coalition]

private theorem joining_base_eq (index : Fin 7) :
    cappedClockExactLPBase (childReward reward)
      (.joining ⟨coalition index, coalition_nonempty index⟩) =
      ![-5, 4, -1, -2, -2, -2, 1 / 2] index := by
  fin_cases index
  all_goals dsimp only [cappedClockExactLPBase]
  all_goals norm_num +decide [joinedOutsideImage, childOutsideImage,
    reward, coalitionCode, child, coalition]

private theorem rowSlack_reduced
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (joining : Bool) (A : Finset Child) (hA : A.Nonempty) :
    rowSlack table joining A hA =
      (1 / 2) * patientWithdrawalGainFloor (childReward table) (child 0) A hA +
        3 * cappedClockExactLPDelta (childReward table)
          (if joining then .joining ⟨A, hA⟩ else .future ⟨A, hA⟩) (child 2) -
        cappedClockExactLPBase (childReward table)
          (if joining then .joining ⟨A, hA⟩ else .future ⟨A, hA⟩) := by
  simp [rowSlack, sum_child, advanceWeight, withdrawalWeight, child]

theorem neverSlack_eq : neverSlack reward = 1 / 2 := by
  norm_num [neverSlack, sum_child, advanceWeight, withdrawalWeight, ownNeverAlternative,
    childSoloImage, outsideSoloImage, reward, coalitionCode, child]

/-- Every original nonempty child coalition has the exact displayed future-row margin. -/
theorem futureSlack_eq (index : Fin 7) :
    rowSlack reward false (coalition index) (coalition_nonempty index) =
      futureSlacks index := by
  rw [rowSlack_reduced]
  change (1 / 2) * patientWithdrawalGainFloor (childReward reward) (child 0)
    (coalition index) (coalition_nonempty index) +
      3 * cappedClockExactLPDelta (childReward reward)
        (.future ⟨coalition index, coalition_nonempty index⟩) (child 2) -
      cappedClockExactLPBase (childReward reward)
        (.future ⟨coalition index, coalition_nonempty index⟩) = futureSlacks index
  rw [withdrawalGain_zero_eq, future_delta_two_eq, future_base_eq]
  fin_cases index <;> norm_num [futureSlacks]

/-- Every original nonempty child coalition has the exact displayed joining-row margin. -/
theorem joiningSlack_eq (index : Fin 7) :
    rowSlack reward true (coalition index) (coalition_nonempty index) =
      joiningSlacks index := by
  rw [rowSlack_reduced]
  change (1 / 2) * patientWithdrawalGainFloor (childReward reward) (child 0)
    (coalition index) (coalition_nonempty index) +
      3 * cappedClockExactLPDelta (childReward reward)
        (.joining ⟨coalition index, coalition_nonempty index⟩) (child 2) -
      cappedClockExactLPBase (childReward reward)
        (.joining ⟨coalition index, coalition_nonempty index⟩) = joiningSlacks index
  rw [withdrawalGain_zero_eq, joining_delta_two_eq, joining_base_eq]
  fin_cases index <;> norm_num [joiningSlacks]

theorem rowSlack_one_le (joining : Bool) (A : Finset Child) (hA : A.Nonempty) :
    1 ≤ rowSlack reward joining A hA := by
  obtain ⟨index, rfl⟩ := exists_coalition_index A hA
  cases joining
  · rw [futureSlack_eq]
    fin_cases index <;> norm_num [futureSlacks]
  · rw [joiningSlack_eq]
    fin_cases index <;> norm_num [joiningSlacks]

/-- Raw slack verification produces the ordinary canonical patient certificate. -/
def certificateOfSlacks
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnever : 0 ≤ neverSlack table)
    (hrows : ∀ joining A hA, 0 ≤ rowSlack table joining A hA) :
    PatientWithdrawalRewardCertificate (childReward table) where
  advanceWeight := advanceWeight
  withdrawalWeight := withdrawalWeight
  advanceWeight_nonneg := advanceWeight_nonneg
  withdrawalWeight_nonneg := withdrawalWeight_nonneg
  never_row := sub_nonneg.mp hnever
  future_row A hA := sub_nonneg.mp (hrows false A hA)
  join_row A hA := sub_nonneg.mp (hrows true A hA)

/-- Internally verified literal weights lambda=(0,0,3), mu=(1/2,0,0). -/
def certificate : PatientWithdrawalRewardCertificate (childReward reward) :=
  certificateOfSlacks reward (by rw [neverSlack_eq]; norm_num)
    (fun joining A hA => le_trans (by norm_num) (rowSlack_one_le joining A hA))

end GameTheory.StrictPatientWithdrawal

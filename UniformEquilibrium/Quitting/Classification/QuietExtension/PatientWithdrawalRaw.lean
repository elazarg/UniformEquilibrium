import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalRestartPointwiseCore

/-!
# Literal future-patient-withdrawal reward rows

The patient singleton floor includes the favorable finite late-own-quit
alternative when all opponents use Never. It is a terminal floor; no positive
value is assigned to Never itself or to a finite-horizon evaluation.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The best of own singleton quitting and Never against all opponent Never. -/
def patientWithdrawalOwnNeverAlternative
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) (i : ι) : ℝ :=
  max (reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i)) 0

/-- The finite patient floor includes all passive child-coalition rewards and
the actual late-own-quit alternative on opponent Never. -/
def patientWithdrawalFloor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) (i : ι) : ℝ := by
  classical
  let passive : Finset ℝ :=
    Finset.univ.image fun B : {A : Finset ι // A.Nonempty ∧ i ∉ A} =>
      reward ⟨cappedClockChildCoalition B.1,
        cappedClockChildCoalition_nonempty B.2.1⟩ (some i)
  exact (insert (patientWithdrawalOwnNeverAlternative reward i) passive).min'
    (Finset.insert_nonempty _ passive)

theorem patientWithdrawalFloor_le_ownNeverAlternative
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) (i : ι) :
    patientWithdrawalFloor reward i ≤ patientWithdrawalOwnNeverAlternative reward i := by
  classical
  unfold patientWithdrawalFloor
  exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem patientWithdrawalFloor_le_passiveReward
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (B : Finset ι) (hB : B.Nonempty) (hi : i ∉ B) :
    patientWithdrawalFloor reward i ≤
      reward ⟨cappedClockChildCoalition B,
        cappedClockChildCoalition_nonempty hB⟩ (some i) := by
  classical
  unfold patientWithdrawalFloor
  apply Finset.min'_le
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨⟨B, hB, hi⟩, Finset.mem_univ _, rfl⟩)

/-- The literal terminal withdrawal coefficient W with the patient floor.
The erased-coalition branch never evaluates an empty reward coalition. -/
def patientWithdrawalGainFloor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (A : Finset ι) (hA : A.Nonempty) : ℝ :=
  deadlineSecurityGainFloorWithRestart reward (patientWithdrawalFloor reward i) i A hA

/-- Raw patient N/F/J rows. The two response experiments have separate
nonnegative weights; their terminal full-debt coefficient is lambda plus mu,
not the deadline operation's maximum coefficient. -/
structure PatientWithdrawalRewardCertificate
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) where
  advanceWeight : ι → ℝ
  withdrawalWeight : ι → ℝ
  advanceWeight_nonneg : ∀ i, 0 ≤ advanceWeight i
  withdrawalWeight_nonneg : ∀ i, 0 ≤ withdrawalWeight i
  never_row :
    reward ⟨{none}, Finset.singleton_nonempty none⟩ none ≤
      (∑ i, advanceWeight i *
        reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i)) +
      ∑ i, withdrawalWeight i * patientWithdrawalOwnNeverAlternative reward i
  future_row : ∀ A (hA : A.Nonempty),
    reward ⟨{none}, Finset.singleton_nonempty none⟩ none -
        reward ⟨cappedClockChildCoalition A,
          cappedClockChildCoalition_nonempty hA⟩ none ≤
      ∑ i, (advanceWeight i *
          (reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) -
            reward ⟨cappedClockChildCoalition A,
              cappedClockChildCoalition_nonempty hA⟩ (some i)) +
        withdrawalWeight i * patientWithdrawalGainFloor reward i A hA)
  join_row : ∀ A (hA : A.Nonempty),
    reward ⟨cappedClockJoinedCoalition A,
          cappedClockJoinedCoalition_nonempty A⟩ none -
        reward ⟨cappedClockChildCoalition A,
          cappedClockChildCoalition_nonempty hA⟩ none ≤
      ∑ i, (advanceWeight i *
          (reward ⟨cappedClockChildCoalition (insert i A),
              cappedClockChildCoalition_nonempty (Finset.insert_nonempty i A)⟩ (some i) -
            reward ⟨cappedClockChildCoalition A,
              cappedClockChildCoalition_nonempty hA⟩ (some i)) +
        withdrawalWeight i * patientWithdrawalGainFloor reward i A hA)

/-- The sum coefficient from the two separately legal response experiments. -/
def PatientWithdrawalRewardCertificate.debtWeight
    {reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : PatientWithdrawalRewardCertificate reward) (i : ι) : ℝ :=
  certificate.advanceWeight i + certificate.withdrawalWeight i

theorem PatientWithdrawalRewardCertificate.debtWeight_nonneg
    {reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : PatientWithdrawalRewardCertificate reward) (i : ι) :
    0 ≤ certificate.debtWeight i :=
  add_nonneg (certificate.advanceWeight_nonneg i) (certificate.withdrawalWeight_nonneg i)

end GameTheory

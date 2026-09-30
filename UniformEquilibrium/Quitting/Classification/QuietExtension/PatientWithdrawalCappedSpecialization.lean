import UniformEquilibrium.Quitting.Classification.QuietExtension.PatientWithdrawalRaw

/-! # The advancing-only raw cone is a patient zero-withdrawal specialization -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A literal advancing-only N/F/J certificate produces the literal patient
rows with zero withdrawal weight; no new strategic hypotheses are required. -/
def CappedClockParentRewardCertificate.patientZeroWithdrawal
    {reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : CappedClockParentRewardCertificate reward) :
    PatientWithdrawalRewardCertificate reward where
  advanceWeight := certificate.weight
  withdrawalWeight := fun _ => 0
  advanceWeight_nonneg := certificate.weight_nonneg
  withdrawalWeight_nonneg := fun _ => le_rfl
  never_row := by simpa only [zero_mul, Finset.sum_const_zero, add_zero] using certificate.never_row
  future_row A hA := by
    simpa only [zero_mul, add_zero] using certificate.future_row A hA
  join_row A hA := by
    simpa only [zero_mul, add_zero] using certificate.join_row A hA

/-- The patient debt coefficient is exactly the original advancing weight
on the zero-withdrawal specialization. -/
theorem CappedClockParentRewardCertificate.patientZeroWithdrawal_debtWeight
    {reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : CappedClockParentRewardCertificate reward) (i : ι) :
    certificate.patientZeroWithdrawal.debtWeight i = certificate.weight i := by
  simp only [PatientWithdrawalRewardCertificate.debtWeight,
    CappedClockParentRewardCertificate.patientZeroWithdrawal, add_zero]

end GameTheory

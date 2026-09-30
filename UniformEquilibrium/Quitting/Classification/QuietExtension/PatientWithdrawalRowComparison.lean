import UniformEquilibrium.Quitting.Classification.QuietExtension.PatientWithdrawalCoalitionGain

/-! # Literal patient terminal N/F/J rows imply their clock-sample comparisons -/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- On joint child Never, the patient experiment contributes the actual
own-singleton-or-Never alternative rather than zero. -/
theorem patientWithdrawal_neverRow_pointwise
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : PatientWithdrawalRewardCertificate reward)
    (times : ι → Option ℕ) (time : ℕ)
    (hfirst : quittingEarliestStoppingValue times = ⊤) :
    cappedClockActualOutsideGain reward times (some time) ≤
      ∑ i, (certificate.advanceWeight i * cappedClockActualChildGain reward times (some time) i +
        certificate.withdrawalWeight i * patientWithdrawalTerminalGain reward times
          (some time) i) := by
  have hnever := (quittingEarliestStoppingValue_eq_top_iff times).mp hfirst
  have hquiet := quittingFirstStoppingOutcome_quietParentClocks_of_first_eq_top times hfirst
  have houtside := quittingFirstStoppingOutcome_outsideDeadlineClocks_of_lt_first
    times time (by simp [hfirst])
  have hcap (i : ι) := quittingFirstStoppingOutcome_cappedChildParentClocks_of_lt_first
    times time i (by simp [hfirst])
  have hpatient (i : ι) : patientWithdrawalTerminalGain reward times (some time) i =
      patientWithdrawalOwnNeverAlternative reward i := by
    have hbefore : ¬ quittingStoppingTimeValue (times i) < (time : WithTop ℕ) := by
      simp [hnever i, quittingStoppingTimeValue]
    have hall : ∀ j, j ≠ i → times j = none := fun j _ => hnever j
    rw [patientWithdrawalTerminalGain, patientWithdrawalTerminalPayoffLimit,
      ite_eq_right hbefore, ite_eq_left hall]
    simp only [quittingPureClockTerminalPayoff, hquiet, sub_zero]
  have hrow := certificate.never_row
  rw [← Finset.sum_add_distrib] at hrow
  simpa only [cappedClockActualOutsideGain, cappedClockActualChildGain,
    quittingPureClockTerminalPayoff, hquiet, houtside, hcap, hpatient, sub_zero] using hrow

/-- Patient F charges advancement and patient withdrawal together when the
outsider deadline strictly precedes the finite first child absorption. -/
theorem patientWithdrawal_futureRow_pointwise
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : PatientWithdrawalRewardCertificate reward)
    (times : ι → Option ℕ) (time first : ℕ)
    (hfirst : quittingEarliestStoppingValue times = (first : WithTop ℕ))
    (hbefore : time < first) :
    cappedClockActualOutsideGain reward times (some time) ≤
      ∑ i, (certificate.advanceWeight i * cappedClockActualChildGain reward times (some time) i +
        certificate.withdrawalWeight i * patientWithdrawalTerminalGain reward times
          (some time) i) := by
  let A := quittingEarliestStoppingCoalition times
  have hA : A.Nonempty := quittingEarliestStoppingCoalition_nonempty times
  have hquiet := quittingFirstStoppingOutcome_quietParentClocks_of_first_eq times first hfirst
  have hbefore' : (time : WithTop ℕ) < quittingEarliestStoppingValue times := by
    rw [hfirst]
    exact_mod_cast hbefore
  have houtside := quittingFirstStoppingOutcome_outsideDeadlineClocks_of_lt_first
    times time hbefore'
  have hcap (i : ι) := quittingFirstStoppingOutcome_cappedChildParentClocks_of_lt_first
    times time i hbefore'
  have hrow : cappedClockActualOutsideGain reward times (some time) ≤
      ∑ i, (certificate.advanceWeight i * cappedClockActualChildGain reward times (some time) i +
        certificate.withdrawalWeight i * patientWithdrawalGainFloor reward i A hA) := by
    simpa only [cappedClockActualOutsideGain, cappedClockActualChildGain,
      quittingPureClockTerminalPayoff, hquiet, houtside, hcap] using certificate.future_row A hA
  refine hrow.trans (Finset.sum_le_sum fun i _ => ?_)
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (patientWithdrawalTerminalGain_ge_coalitionFloor reward times time first i hfirst
      hbefore.le) (certificate.withdrawalWeight_nonneg i))

/-- Patient J charges the joining advancement gain and limiting withdrawal
gain together at an exact first-date tie. -/
theorem patientWithdrawal_joinRow_pointwise
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : PatientWithdrawalRewardCertificate reward)
    (times : ι → Option ℕ) (time : ℕ)
    (hfirst : quittingEarliestStoppingValue times = (time : WithTop ℕ)) :
    cappedClockActualOutsideGain reward times (some time) ≤
      ∑ i, (certificate.advanceWeight i * cappedClockActualChildGain reward times (some time) i +
        certificate.withdrawalWeight i * patientWithdrawalTerminalGain reward times
          (some time) i) := by
  let A := quittingEarliestStoppingCoalition times
  have hA : A.Nonempty := quittingEarliestStoppingCoalition_nonempty times
  have hquiet := quittingFirstStoppingOutcome_quietParentClocks_of_first_eq times time hfirst
  have houtside := quittingFirstStoppingOutcome_outsideDeadlineClocks_of_eq_first times time hfirst
  have hcap (i : ι) := quittingFirstStoppingOutcome_cappedChildParentClocks_of_eq_first
    times time i hfirst
  have hrow : cappedClockActualOutsideGain reward times (some time) ≤
      ∑ i, (certificate.advanceWeight i * cappedClockActualChildGain reward times (some time) i +
        certificate.withdrawalWeight i * patientWithdrawalGainFloor reward i A hA) := by
    simpa only [cappedClockActualOutsideGain, cappedClockActualChildGain,
      quittingPureClockTerminalPayoff, hquiet, houtside, hcap] using certificate.join_row A hA
  refine hrow.trans (Finset.sum_le_sum fun i _ => ?_)
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (patientWithdrawalTerminalGain_ge_coalitionFloor reward times time time i hfirst le_rfl)
    (certificate.withdrawalWeight_nonneg i))

end GameTheory

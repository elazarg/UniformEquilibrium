import UniformEquilibrium.Quitting.Classification.QuietExtension.PatientWithdrawalRowComparison
import UniformEquilibrium.Quitting.Classification.QuietExtension.PatientWithdrawalAfterAbsorption

/-! # Terminal clock-sample domination from the literal patient certificate -/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Literal P-N/F/J imply terminal domination by separately tested child
advancement and actual patient payoff-limit gains, on every clock sample. -/
theorem patientWithdrawalActualOutsideGain_le_weighted_childGains
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : PatientWithdrawalRewardCertificate reward)
    (times : ι → Option ℕ) (deadline : Option ℕ) :
    cappedClockActualOutsideGain reward times deadline ≤
      ∑ i, (certificate.advanceWeight i * cappedClockActualChildGain reward times deadline i +
        certificate.withdrawalWeight i *
          patientWithdrawalTerminalGain reward times deadline i) := by
  cases deadline with
  | none =>
      have h := deadlineWithdrawal_allEvaluatedGains_zero_of_deadline_none
        reward quittingTerminalEvaluation times
      have houtside : cappedClockActualOutsideGain reward times none = 0 := by
        simpa only [cappedClockActualEvaluatedOutsideGain, cappedClockActualOutsideGain,
          quittingPureClockEvaluatedPayoff_terminalEvaluation] using h.1
      have hchild (i : ι) : cappedClockActualChildGain reward times none i = 0 := by
        simpa only [cappedClockActualEvaluatedChildGain, cappedClockActualChildGain,
          quittingPureClockEvaluatedPayoff_terminalEvaluation] using (h.2 i).1
      simp [houtside, hchild, patientWithdrawalTerminalGain_none]
  | some time =>
      by_cases hafter : quittingEarliestStoppingValue times < (time : WithTop ℕ)
      · have h := deadlineWithdrawal_allEvaluatedGains_zero_of_first_lt
          reward quittingTerminalEvaluation times time hafter
        have houtside : cappedClockActualOutsideGain reward times (some time) = 0 := by
          simpa only [cappedClockActualEvaluatedOutsideGain, cappedClockActualOutsideGain,
            quittingPureClockEvaluatedPayoff_terminalEvaluation] using h.1
        have hchild (i : ι) : cappedClockActualChildGain reward times (some time) i = 0 := by
          simpa only [cappedClockActualEvaluatedChildGain, cappedClockActualChildGain,
            quittingPureClockEvaluatedPayoff_terminalEvaluation] using (h.2 i).1
        have hpatient (i : ι) : patientWithdrawalTerminalGain reward times (some time) i = 0 :=
          patientWithdrawalTerminalGain_of_first_lt reward times time i hafter
        simp [houtside, hchild, hpatient]
      · induction hfirst : quittingEarliestStoppingValue times using WithTop.recTopCoe with
        | top => exact patientWithdrawal_neverRow_pointwise reward certificate times time hfirst
        | coe first =>
            have hle : time ≤ first := by
              have hle := not_lt.mp hafter
              rw [hfirst] at hle
              exact WithTop.coe_le_coe.mp hle
            by_cases hbefore : time < first
            · exact patientWithdrawal_futureRow_pointwise reward certificate times time first
                hfirst hbefore
            · have heq : first = time := by omega
              subst first
              exact patientWithdrawal_joinRow_pointwise reward certificate times time hfirst

end GameTheory

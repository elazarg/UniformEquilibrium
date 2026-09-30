import UniformEquilibrium.Quitting.Classification.QuietExtension.PatientWithdrawalLimitFloor

/-! # Patient withdrawal after an already completed child absorption -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- When the outsider deadline is later than the original child absorption,
patient withdrawal has zero limiting gain, including owners whose clock is
changed but was not responsible for that absorption. -/
theorem patientWithdrawalTerminalGain_of_first_lt
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (times : ι → Option ℕ) (time : ℕ) (i : ι)
    (hafter : quittingEarliestStoppingValue times < (time : WithTop ℕ)) :
    patientWithdrawalTerminalGain reward times (some time) i = 0 := by
  by_cases hbefore : quittingStoppingTimeValue (times i) < (time : WithTop ℕ)
  · simp [patientWithdrawalTerminalGain, patientWithdrawalTerminalPayoffLimit, hbefore]
  · obtain ⟨blocker, hblocker⟩ := quittingEarliestStoppingCoalition_nonempty times
    have hvalue : quittingStoppingTimeValue (times blocker) =
        quittingEarliestStoppingValue times := by
      simpa [quittingEarliestStoppingCoalition] using hblocker
    have hne : blocker ≠ i := by
      intro heq
      rw [heq] at hvalue
      apply hbefore
      rw [hvalue]
      exact hafter
    have hnew : ∀ delay : ℕ, quittingEarliestStoppingValue times <
        quittingStoppingTimeValue (patientWithdrawalClock reward i delay (times i)
          (some time)) := by
      intro delay
      by_cases hsingleton : 0 ≤
          reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i)
      · rw [patientWithdrawalClock_some_of_nonnegativeSingleton
          reward i delay (times i) time hbefore hsingleton, quittingStoppingTimeValue]
        exact hafter.trans (by exact_mod_cast (show time < time + delay + 1 by omega))
      · rw [patientWithdrawalClock_some_of_negativeSingleton reward i delay (times i)
          time hbefore (lt_of_not_ge hsingleton), quittingStoppingTimeValue]
        exact hafter.trans (WithTop.coe_lt_top time)
    have hpay (delay : ℕ) : quittingPureClockTerminalPayoff reward
        (patientWithdrawalParentClocks reward times (some time) delay i) (some i) =
        quittingPureClockTerminalPayoff reward (quietParentClocks times) (some i) := by
      have houtcome := quittingFirstStoppingOutcome_eq_of_earlier_stopper
        (patientWithdrawalParentClocks reward times (some time) delay i)
        (quietParentClocks times) (hidden := some i) (blocker := some blocker)
        (by
          intro player hplayer
          cases player with
          | none => rfl
          | some j =>
              have hj : j ≠ i := by simpa using hplayer
              simp [patientWithdrawalParentClocks, deadlinePrivateChildClocks,
                quietParentClocks, hj])
        (by
          simpa [patientWithdrawalParentClocks, deadlinePrivateChildClocks, hne, hvalue] using
            hnew delay)
        (by
          simpa only [quietParentClocks, hvalue] using
            hafter.trans_le (not_lt.mp hbefore))
      simp only [quittingPureClockTerminalPayoff, houtcome]
    obtain ⟨delay, hlimit⟩ :=
      (patientWithdrawal_terminalPayoff_eventually_eq_limit reward times (some time) i).exists
    rw [patientWithdrawalTerminalGain, ← hlimit, hpay, sub_self]

end GameTheory

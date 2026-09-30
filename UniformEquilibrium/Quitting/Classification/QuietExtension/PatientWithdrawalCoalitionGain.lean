import UniformEquilibrium.Quitting.Classification.QuietExtension.PatientWithdrawalLimitFloor

/-!
# Patient gains at finite first child coalitions

Away from a singleton first coalition owned by the responding player, the
patient payoff limit equals the existing first-atom withdrawal payoff. Thus
the unchanged nonsingleton calculation is reused, including nonmembers.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- For a nonsingleton relative to the queried owner, every earlier/tied
patient deadline has precisely the existing first-atom withdrawal gain. -/
theorem patientWithdrawalTerminalGain_eq_atomWithdrawal_of_nonsingletonFirst
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (times : ι → Option ℕ) (time first : ℕ) (i : ι)
    (hfirst : quittingEarliestStoppingValue times = (first : WithTop ℕ))
    (htime : time ≤ first)
    (hsingleton : quittingEarliestStoppingCoalition times ≠ {i}) :
    patientWithdrawalTerminalGain reward times (some time) i =
      deadlineWithdrawalActualEvaluatedChildGain reward quittingTerminalEvaluation
        times (some first) i := by
  let A := quittingEarliestStoppingCoalition times
  have hrest : (A.erase i).Nonempty := by
    by_contra h
    have hempty := Finset.not_nonempty_iff_eq_empty.mp h
    rcases (Finset.erase_eq_empty_iff A i).mp hempty with hempty | heq
    · exact (quittingEarliestStoppingCoalition_nonempty times).ne_empty hempty
    · exact hsingleton heq
  obtain ⟨blocker, hblocker⟩ := hrest
  have hparts := Finset.mem_erase.mp hblocker
  have hvalue : quittingStoppingTimeValue (times blocker) = (first : WithTop ℕ) := by
    simpa [A, quittingEarliestStoppingCoalition, hfirst] using hparts.2
  have hbefore : ¬ quittingStoppingTimeValue (times i) < (time : WithTop ℕ) := by
    apply not_lt.mpr
    have hle : quittingEarliestStoppingValue times ≤
        quittingStoppingTimeValue (times i) := Finset.inf_le (Finset.mem_univ i)
    rw [hfirst] at hle
    exact (WithTop.coe_le_coe.mpr htime).trans hle
  have hall : ¬ ∀ j, j ≠ i → times j = none := by
    intro hall
    rw [hall blocker hparts.1] at hvalue
    simp [quittingStoppingTimeValue] at hvalue
  rw [patientWithdrawalTerminalGain, patientWithdrawalTerminalPayoffLimit,
    ite_eq_right hbefore, ite_eq_right hall, deadlineWithdrawalActualEvaluatedChildGain]
  simp only [quittingPureClockEvaluatedPayoff_terminalEvaluation]
  congr 1
  by_cases hclock : times i = some first
  · rw [withdrawnChildParentClocks_eq_quiet_update_none times first i hclock]
    congr 1
    funext player
    cases player with
    | none => rfl
    | some j => by_cases hj : j = i <;>
        simp [deadlinePrivateChildClocks, quietParentClocks, hj]
  · rw [withdrawnChildParentClocks_some_of_ne times first i hclock]
    have hne : quittingStoppingTimeValue (times i) ≠ (first : WithTop ℕ) := by
      intro heq
      apply hclock
      cases h : times i with
      | none => simp [h, quittingStoppingTimeValue] at heq
      | some date =>
          have hdate : date = first := by simpa [h, quittingStoppingTimeValue] using heq
          simp [hdate]
    have hle : (first : WithTop ℕ) ≤ quittingStoppingTimeValue (times i) := by
      rw [← hfirst]
      exact Finset.inf_le (Finset.mem_univ i)
    have houtcome := quittingFirstStoppingOutcome_eq_of_earlier_stopper
      (deadlinePrivateChildClocks times i none) (quietParentClocks times)
      (hidden := some i) (blocker := some blocker)
      (by
        intro player hplayer
        cases player with
        | none => rfl
        | some j =>
            have hj : j ≠ i := by simpa using hplayer
            simp [deadlinePrivateChildClocks, quietParentClocks, hj])
      (by
        have hlt : quittingStoppingTimeValue (times blocker) < (⊤ : WithTop ℕ) := by
          rw [hvalue]
          exact WithTop.coe_lt_top first
        simpa only [deadlinePrivateChildClocks, hparts.1, ↓reduceIte,
          quittingStoppingTimeValue] using hlt)
      (by
        simpa only [quietParentClocks, hvalue] using lt_of_le_of_ne hle hne.symm)
    simp only [quittingPureClockTerminalPayoff, houtcome]

/-- The literal patient W row is a lower bound for the limiting gain at
every finite first coalition and every earlier or tied outsider date. -/
theorem patientWithdrawalTerminalGain_ge_coalitionFloor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (times : ι → Option ℕ) (time first : ℕ) (i : ι)
    (hfirst : quittingEarliestStoppingValue times = (first : WithTop ℕ))
    (htime : time ≤ first) :
    patientWithdrawalGainFloor reward i (quittingEarliestStoppingCoalition times)
        (quittingEarliestStoppingCoalition_nonempty times) ≤
      patientWithdrawalTerminalGain reward times (some time) i := by
  by_cases hsingleton : quittingEarliestStoppingCoalition times = {i}
  · simpa only [hsingleton] using patientWithdrawalTerminalGain_singleton_ge_floor
      reward times time first i hfirst hsingleton htime
  · rw [patientWithdrawalTerminalGain_eq_atomWithdrawal_of_nonsingletonFirst
      reward times time first i hfirst htime hsingleton]
    have hfloor : patientWithdrawalGainFloor reward i
        (quittingEarliestStoppingCoalition times)
        (quittingEarliestStoppingCoalition_nonempty times) =
        deadlineWithdrawalGainFloor reward i (quittingEarliestStoppingCoalition times)
          (quittingEarliestStoppingCoalition_nonempty times) := by
      simp [patientWithdrawalGainFloor, deadlineSecurityGainFloorWithRestart, hsingleton]
    rw [hfloor]
    simpa only [quittingTerminalEvaluation_coe, one_mul] using
      deadlineWithdrawalActualEvaluatedChildGain_tie_ge_floor reward quittingTerminalEvaluation
        quittingTerminalEvaluation_nonneg quittingTerminalEvaluation_antitone times first i hfirst

end GameTheory

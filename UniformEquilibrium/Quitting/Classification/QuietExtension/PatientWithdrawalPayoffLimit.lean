import UniformEquilibrium.Quitting.Classification.QuietExtension.PatientWithdrawalLaw

/-!
# Actual terminal payoff limit of patient withdrawal

The private finite-delay responses retain the favorable own-singleton payoff
on opponent Never. On every sample with a finite opponent clock their payoff
eventually equals the payoff of cancelling the owner's clock. In particular,
this result does not replace a limit of rewards by the reward of Never.
-/

noncomputable section

namespace GameTheory

open Filter Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The literal patient payoff limit on one coupled clock sample. -/
def patientWithdrawalTerminalPayoffLimit
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (times : ι → Option ℕ) (deadline : Option ℕ) (i : ι) : ℝ :=
  match deadline with
  | none => quittingPureClockTerminalPayoff reward (quietParentClocks times) (some i)
  | some time =>
      if quittingStoppingTimeValue (times i) < (time : WithTop ℕ) then
        quittingPureClockTerminalPayoff reward (quietParentClocks times) (some i)
      else if ∀ j, j ≠ i → times j = none then
        patientWithdrawalOwnNeverAlternative reward i
      else quittingPureClockTerminalPayoff reward
        (deadlinePrivateChildClocks times i none) (some i)

omit [Fintype ι] in
private theorem patient_privateClocks_base (times : ι → Option ℕ) (i : ι) :
    deadlinePrivateChildClocks times i (times i) = quietParentClocks times := by
  funext player
  cases player with
  | none => rfl
  | some j => by_cases hj : j = i <;>
      simp [deadlinePrivateChildClocks, quietParentClocks, hj]

omit [Fintype ι] in
private theorem patient_privateClocks_opponentsNever
    (times : ι → Option ℕ) (i : ι) (clock : Option ℕ)
    (hall : ∀ j, j ≠ i → times j = none) :
    deadlinePrivateChildClocks times i clock =
      Function.update (fun _ : Option ι => none) (some i) clock := by
  funext player
  cases player with
  | none => simp [deadlinePrivateChildClocks]
  | some j =>
      by_cases hj : j = i
      · subst j
        simp [deadlinePrivateChildClocks]
      · simp [deadlinePrivateChildClocks, hj, hall j hj]

/-- Actual finite-delay terminal payoffs are eventually equal to the patient
payoff limit. The threshold may depend on the coupled opponent sample. -/
theorem patientWithdrawal_terminalPayoff_eventually_eq_limit
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (times : ι → Option ℕ) (deadline : Option ℕ) (i : ι) :
    ∀ᶠ delay : ℕ in atTop,
      quittingPureClockTerminalPayoff reward
          (patientWithdrawalParentClocks reward times deadline delay i) (some i) =
        patientWithdrawalTerminalPayoffLimit reward times deadline i := by
  cases deadline with
  | none =>
      exact Eventually.of_forall fun delay => by
        simp [patientWithdrawalParentClocks, patientWithdrawalClock_none,
          patientWithdrawalTerminalPayoffLimit, patient_privateClocks_base]
  | some time =>
      by_cases hbefore : quittingStoppingTimeValue (times i) < (time : WithTop ℕ)
      · exact Eventually.of_forall fun delay => by
          simp [patientWithdrawalParentClocks,
            patientWithdrawalClock_some_of_before reward i delay (times i) time hbefore,
            patientWithdrawalTerminalPayoffLimit, hbefore, patient_privateClocks_base]
      · by_cases hsingleton : 0 ≤
          reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i)
        · by_cases hall : ∀ j, j ≠ i → times j = none
          · exact Eventually.of_forall fun delay => by
              rw [patientWithdrawalParentClocks,
                patientWithdrawalClock_some_of_nonnegativeSingleton
                  reward i delay (times i) time hbefore hsingleton,
                patient_privateClocks_opponentsNever times i _ hall,
                deadlineWithdrawalSecurity_terminalPayoff_opponentsNever]
              rw [patientWithdrawalTerminalPayoffLimit, ite_eq_right hbefore, ite_eq_left hall]
              exact (max_eq_left hsingleton).symm
          · obtain ⟨j, hj⟩ := not_forall.mp hall
            have hne : j ≠ i := by
              intro heq
              exact hj (fun h => (h heq).elim)
            have hclock : times j ≠ none := by
              intro heq
              exact hj (fun _ => heq)
            obtain ⟨stop, hstop⟩ := Option.ne_none_iff_exists'.mp hclock
            filter_upwards [eventually_ge_atTop stop] with delay hdelay
            have houtcome := quittingFirstStoppingOutcome_eq_of_earlier_stopper
              (deadlinePrivateChildClocks times i (some (time + delay + 1)))
              (deadlinePrivateChildClocks times i none)
              (hidden := some i) (blocker := some j)
              (by
                intro player hplayer
                cases player with
                | none => rfl
                | some other =>
                    have hother : other ≠ i := by simpa using hplayer
                    simp [deadlinePrivateChildClocks, hother])
              (by
                simp only [deadlinePrivateChildClocks, hne, ↓reduceIte,
                  quittingStoppingTimeValue, hstop]
                exact_mod_cast (show stop < time + delay + 1 by omega))
              (by simp [deadlinePrivateChildClocks, hne, quittingStoppingTimeValue, hstop])
            rw [patientWithdrawalParentClocks,
              patientWithdrawalClock_some_of_nonnegativeSingleton
                reward i delay (times i) time hbefore hsingleton]
            simp [patientWithdrawalTerminalPayoffLimit, hbefore, hall,
              quittingPureClockTerminalPayoff, houtcome]
        · exact Eventually.of_forall fun delay => by
            rw [patientWithdrawalParentClocks,
              patientWithdrawalClock_some_of_negativeSingleton
                reward i delay (times i) time hbefore (lt_of_not_ge hsingleton)]
            by_cases hall : ∀ j, j ≠ i → times j = none
            · rw [patient_privateClocks_opponentsNever times i none hall]
              rw [patientWithdrawalTerminalPayoffLimit, ite_eq_right hbefore, ite_eq_left hall]
              simp [patientWithdrawalOwnNeverAlternative,
                max_eq_right (le_of_not_ge hsingleton),
                quittingPureClockTerminalPayoff]
            · simp [patientWithdrawalTerminalPayoffLimit, hbefore, hall]

/-- Pointwise terminal payoff convergence of the actual private patient law. -/
theorem patientWithdrawal_terminalPayoff_tendsto
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (times : ι → Option ℕ) (deadline : Option ℕ) (i : ι) :
    Tendsto (fun delay : ℕ => quittingPureClockTerminalPayoff reward
        (patientWithdrawalParentClocks reward times deadline delay i) (some i))
      atTop (𝓝 (patientWithdrawalTerminalPayoffLimit reward times deadline i)) :=
  tendsto_const_nhds.congr'
    ((patientWithdrawal_terminalPayoff_eventually_eq_limit reward times deadline i).mono
      (fun _ h => h.symm))

end GameTheory

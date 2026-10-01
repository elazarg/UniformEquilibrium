import UniformEquilibrium.Quitting.Classification.QuietExtension.CancellationWithdrawal
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalDomination
import UniformEquilibrium.Quitting.Paths.CommonStoppingCalendarRetiming

/-! # Deterministic and expected evaluated cancellation comparison

The literal future-cancellation law uses the owner's unchanged opponents.
Its before/tie withdrawal floor delegates to the checked atom-withdrawal
calculation at the owner's original clock, rather than to a patient payoff limit.
The raw N/F/J certificate controls every deterministic tuple and every bounded
coupled expectation. Independence and actual behavioral debt are separate adapters.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.PMFProduct
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Fintype ι] [Nonempty ι] in
/-- Before the replica deadline, future cancellation leaves the tuple unchanged. -/
theorem cancellationParentClocks_of_before
    (times : ι → Option ℕ) (deadline : ℕ) (i : ι)
    (hbefore : quittingStoppingTimeValue (times i) < (deadline : WithTop ℕ)) :
    cancellationParentClocks times (some deadline) i = quietParentClocks times := by
  rw [cancellationParentClocks, cancellationStoppingClock_some_of_before _ _ hbefore]
  funext player
  cases player with
  | none => rfl
  | some j => by_cases hj : j = i <;>
      simp [deadlinePrivateChildClocks, quietParentClocks, hj]

omit [Fintype ι] [Nonempty ι] in
/-- An active cancellation equals atom withdrawal at the owner's original
clock. Own Never is also unchanged on both sides. -/
theorem cancellationParentClocks_eq_withdrawn_at_own
    (times : ι → Option ℕ) (deadline : ℕ) (i : ι)
    (hbefore : ¬ quittingStoppingTimeValue (times i) < (deadline : WithTop ℕ)) :
    cancellationParentClocks times (some deadline) i =
      withdrawnChildParentClocks times (times i) i := by
  rw [cancellationParentClocks,
    cancellationStoppingClock_some_of_not_before _ _ hbefore,
    quietExtensionPrivateClocks_cancel]
  cases hclock : times i with
  | none =>
      rw [withdrawnChildParentClocks_none]
      congr 1
      simpa only [hclock] using Function.update_eq_self i times
  | some time =>
      exact (withdrawnChildParentClocks_eq_quiet_update_none times time i hclock).symm

theorem cancellationActualEvaluatedChildGain_eq_withdrawal_at_own
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ) (times : ι → Option ℕ) (deadline : ℕ) (i : ι)
    (hbefore : ¬ quittingStoppingTimeValue (times i) < (deadline : WithTop ℕ)) :
    cancellationActualEvaluatedChildGain reward evaluation times (some deadline) i =
      deadlineWithdrawalActualEvaluatedChildGain reward evaluation times (times i) i := by
  rw [cancellationActualEvaluatedChildGain,
    cancellationParentClocks_eq_withdrawn_at_own times deadline i hbefore]
  rfl

/-- Cancelling a clock after absorption has no evaluated gain. The actual
atom-withdrawal after-first theorem supplies the unchanged outcome calculation. -/
theorem cancellationActualEvaluatedChildGain_of_first_lt
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (times : ι → Option ℕ) (deadline : ℕ) (i : ι)
    (hafter : quittingEarliestStoppingValue times < (deadline : WithTop ℕ)) :
    cancellationActualEvaluatedChildGain reward evaluation times (some deadline) i = 0 := by
  by_cases hbefore : quittingStoppingTimeValue (times i) < (deadline : WithTop ℕ)
  · simp [cancellationActualEvaluatedChildGain,
      cancellationParentClocks_of_before times deadline i hbefore]
  · rw [cancellationActualEvaluatedChildGain_eq_withdrawal_at_own
      reward evaluation times deadline i hbefore]
    cases hclock : times i with
    | none => exact deadlineWithdrawalActualEvaluatedChildGain_none reward evaluation times i
    | some time =>
        apply deadlineWithdrawalActualEvaluatedChildGain_of_first_lt
        exact hafter.trans_le (by simpa [hclock, quittingStoppingTimeValue] using not_lt.mp hbefore)

/-- Before or at a finite first stop, cancellation pays at least the same
zero-based W floor as atom withdrawal at that first stop. -/
theorem cancellationActualEvaluatedChildGain_ge_floor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (times : ι → Option ℕ) (deadline first : ℕ) (i : ι)
    (hfirst : quittingEarliestStoppingValue times = (first : WithTop ℕ))
    (hdeadline : deadline ≤ first) :
    evaluation first * deadlineWithdrawalGainFloor reward i
        (quittingEarliestStoppingCoalition times)
        (quittingEarliestStoppingCoalition_nonempty times) ≤
      cancellationActualEvaluatedChildGain reward evaluation times (some deadline) i := by
  have hown : (first : WithTop ℕ) ≤ quittingStoppingTimeValue (times i) := by
    rw [← hfirst]
    exact Finset.inf_le (Finset.mem_univ i)
  have hbefore : ¬ quittingStoppingTimeValue (times i) < (deadline : WithTop ℕ) :=
    not_lt.mpr ((by exact_mod_cast hdeadline : (deadline : WithTop ℕ) ≤ first).trans hown)
  rw [cancellationActualEvaluatedChildGain_eq_withdrawal_at_own
    reward evaluation times deadline i hbefore]
  by_cases hclock : times i = some first
  · rw [hclock]
    exact deadlineWithdrawalActualEvaluatedChildGain_tie_ge_floor
      reward evaluation evaluation_nonneg evaluation_antitone times first i hfirst
  · have hi : i ∉ quittingEarliestStoppingCoalition times := by
      intro hi
      have hvalue : quittingStoppingTimeValue (times i) = (first : WithTop ℕ) := by
        simpa [quittingEarliestStoppingCoalition, hfirst] using hi
      cases htime : times i with
      | none => simp [htime, quittingStoppingTimeValue] at hvalue
      | some time =>
          have heq : time = first := by
            simpa [htime, quittingStoppingTimeValue] using hvalue
          exact hclock (by simp [htime, heq])
    rw [deadlineWithdrawalGainFloor_of_not_mem reward i
      (quittingEarliestStoppingCoalition times)
      (quittingEarliestStoppingCoalition_nonempty times) hi, mul_zero]
    cases htime : times i with
    | none => simp only [deadlineWithdrawalActualEvaluatedChildGain_none, le_refl]
    | some time =>
        have hne : first ≠ time := by
          intro heq
          exact hclock (by simp [htime, heq])
        have hlt : (first : WithTop ℕ) < (time : WithTop ℕ) := by
          apply lt_of_le_of_ne
          · simpa [htime, quittingStoppingTimeValue] using hown
          · exact fun heq => hne (WithTop.coe_eq_coe.mp heq)
        simp only [deadlineWithdrawalActualEvaluatedChildGain_of_first_lt
          reward evaluation times time i (by simpa only [hfirst] using hlt), le_refl]

private theorem evaluated_outside_future
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ) (times : ι → Option ℕ)
    (deadline first : ℕ) (A : Finset ι) (hA : A.Nonempty)
    (hfirst : quittingEarliestStoppingValue times = (first : WithTop ℕ))
    (hAeq : quittingEarliestStoppingCoalition times = A) (hbefore : deadline < first) :
    cappedClockActualEvaluatedOutsideGain reward evaluation times (some deadline) =
      evaluation deadline * reward ⟨{none}, Finset.singleton_nonempty none⟩ none -
        evaluation first *
          reward ⟨cappedClockChildCoalition A, cappedClockChildCoalition_nonempty hA⟩ none := by
  have hquiet := quietExtension_terminalPayoff_of_first
    reward times first A hA hfirst hAeq none
  have hgain := quietExtension_outsideGain_of_before
    reward times deadline first A hA hfirst hAeq hbefore
  unfold cappedClockActualOutsideGain at hgain
  rw [hquiet] at hgain
  have hnew : quittingPureClockTerminalPayoff reward
      (outsideDeadlineClocks times (some deadline)) none =
      reward ⟨{none}, Finset.singleton_nonempty none⟩ none := by linarith
  have hbefore' : (deadline : WithTop ℕ) ≤ (first : WithTop ℕ) := by
    exact_mod_cast hbefore.le
  rw [cappedClockActualEvaluatedOutsideGain,
    quittingPureClockEvaluatedPayoff_eq_evaluation_mul_terminalPayoff,
    quittingPureClockEvaluatedPayoff_eq_evaluation_mul_terminalPayoff,
    hnew, hquiet, quittingEarliestStoppingValue_outsideDeadlineClocks,
    quittingEarliestStoppingValue_quietParentClocks, hfirst]
  simp only [quittingStoppingTimeValue, min_eq_right hbefore']

private theorem evaluated_child_future
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ) (times : ι → Option ℕ)
    (deadline first : ℕ) (A : Finset ι) (hA : A.Nonempty)
    (hfirst : quittingEarliestStoppingValue times = (first : WithTop ℕ))
    (hAeq : quittingEarliestStoppingCoalition times = A) (hbefore : deadline < first) (i : ι) :
    cappedClockActualEvaluatedChildGain reward evaluation times (some deadline) i =
      evaluation deadline * reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) -
        evaluation first * reward ⟨cappedClockChildCoalition A,
          cappedClockChildCoalition_nonempty hA⟩ (some i) := by
  have hquiet := quietExtension_terminalPayoff_of_first
    reward times first A hA hfirst hAeq (some i)
  have hgain := quietExtension_childGain_of_before
    reward times deadline first A hA hfirst hAeq hbefore i
  unfold cappedClockActualChildGain at hgain
  rw [hquiet] at hgain
  have hnew : quittingPureClockTerminalPayoff reward
      (cappedChildParentClocks times (some deadline) i) (some i) =
      reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) := by linarith
  have hbefore' : (deadline : WithTop ℕ) ≤ (first : WithTop ℕ) := by
    exact_mod_cast hbefore.le
  rw [cappedClockActualEvaluatedChildGain,
    quittingPureClockEvaluatedPayoff_eq_evaluation_mul_terminalPayoff,
    quittingPureClockEvaluatedPayoff_eq_evaluation_mul_terminalPayoff,
    hnew, hquiet, quittingEarliestStoppingValue_cappedChildParentClocks,
    quittingEarliestStoppingValue_quietParentClocks, hfirst]
  simp only [quittingStoppingTimeValue, min_eq_right hbefore']

omit [DecidableEq ι] in
private theorem evaluated_outside_tie
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ) (times : ι → Option ℕ) (time : ℕ)
    (hfirst : quittingEarliestStoppingValue times = (time : WithTop ℕ)) :
    cappedClockActualEvaluatedOutsideGain reward evaluation times (some time) =
      evaluation time * cappedClockActualOutsideGain reward times (some time) := by
  rw [cappedClockActualEvaluatedOutsideGain,
    quittingPureClockEvaluatedPayoff_eq_evaluation_mul_terminalPayoff,
    quittingPureClockEvaluatedPayoff_eq_evaluation_mul_terminalPayoff,
    quittingEarliestStoppingValue_outsideDeadlineClocks,
    quittingEarliestStoppingValue_quietParentClocks, hfirst]
  simp only [quittingStoppingTimeValue, min_self]
  rw [← mul_sub]
  rfl

private theorem evaluated_child_tie
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ) (times : ι → Option ℕ) (time : ℕ) (i : ι)
    (hfirst : quittingEarliestStoppingValue times = (time : WithTop ℕ)) :
    cappedClockActualEvaluatedChildGain reward evaluation times (some time) i =
      evaluation time * cappedClockActualChildGain reward times (some time) i := by
  rw [cappedClockActualEvaluatedChildGain,
    quittingPureClockEvaluatedPayoff_eq_evaluation_mul_terminalPayoff,
    quittingPureClockEvaluatedPayoff_eq_evaluation_mul_terminalPayoff,
    quittingEarliestStoppingValue_cappedChildParentClocks,
    quittingEarliestStoppingValue_quietParentClocks, hfirst]
  simp only [quittingStoppingTimeValue, min_self]
  rw [← mul_sub]
  rfl

/-- Future rows compare early advancement and the later cancellation floor. -/
theorem cancellationWithdrawal_futureRow_pointwise
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : CancellationWithdrawalRewardCertificate reward)
    (evaluation : WithTop ℕ → ℝ) (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (times : ι → Option ℕ) (deadline first : ℕ)
    (hfirst : quittingEarliestStoppingValue times = (first : WithTop ℕ))
    (hbefore : deadline < first) :
    cappedClockActualEvaluatedOutsideGain reward evaluation times (some deadline) ≤
      ∑ i, (certificate.advanceWeight i *
          cappedClockActualEvaluatedChildGain reward evaluation times (some deadline) i +
        certificate.withdrawalWeight i *
          cancellationActualEvaluatedChildGain reward evaluation times (some deadline) i) := by
  let A := quittingEarliestStoppingCoalition times
  have hA := quittingEarliestStoppingCoalition_nonempty times
  have hrow := certificate.futureRows_evaluated A hA (evaluation deadline) (evaluation first)
    (evaluation_nonneg _) (evaluation_antitone (by exact_mod_cast hbefore.le))
  rw [← evaluated_outside_future reward evaluation times deadline first A hA hfirst rfl hbefore]
    at hrow
  simp_rw [← evaluated_child_future reward evaluation times deadline first A hA hfirst rfl
    hbefore] at hrow
  refine hrow.trans (Finset.sum_le_sum fun i _ => add_le_add le_rfl ?_)
  have hfloor := cancellationActualEvaluatedChildGain_ge_floor
    reward evaluation evaluation_nonneg evaluation_antitone
    times deadline first i hfirst hbefore.le
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hfloor (certificate.withdrawalWeight_nonneg i)

/-- At a first-date tie, the shared terminal response witnesses and the
checked atom-withdrawal floor supply the evaluated J comparison. -/
theorem cancellationWithdrawal_joinRow_pointwise
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : CancellationWithdrawalRewardCertificate reward)
    (evaluation : WithTop ℕ → ℝ) (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (times : ι → Option ℕ) (time : ℕ)
    (hfirst : quittingEarliestStoppingValue times = (time : WithTop ℕ)) :
    cappedClockActualEvaluatedOutsideGain reward evaluation times (some time) ≤
      ∑ i, (certificate.advanceWeight i *
          cappedClockActualEvaluatedChildGain reward evaluation times (some time) i +
        certificate.withdrawalWeight i *
          cancellationActualEvaluatedChildGain reward evaluation times (some time) i) := by
  let A := quittingEarliestStoppingCoalition times
  have hA := quittingEarliestStoppingCoalition_nonempty times
  have hraw : cappedClockActualOutsideGain reward times (some time) ≤
      ∑ i, (certificate.advanceWeight i * cappedClockActualChildGain reward times (some time) i +
        certificate.withdrawalWeight i * deadlineWithdrawalGainFloor reward i A hA) := by
    simpa only [quietExtension_outsideGain_of_tie reward times time A hA hfirst rfl,
      quietExtension_childGain_of_tie reward times time A hA hfirst rfl] using
        certificate.join_row A hA
  rw [evaluated_outside_tie reward evaluation times time hfirst]
  have hrow := mul_le_mul_of_nonneg_left hraw (evaluation_nonneg (time : WithTop ℕ))
  rw [Finset.mul_sum] at hrow
  refine hrow.trans (Finset.sum_le_sum fun i _ => ?_)
  have hfloor := cancellationActualEvaluatedChildGain_ge_floor
    reward evaluation evaluation_nonneg evaluation_antitone times time time i hfirst le_rfl
  rw [evaluated_child_tie reward evaluation times time i hfirst]
  nlinarith [mul_le_mul_of_nonneg_left hfloor (certificate.withdrawalWeight_nonneg i)]

/-- Joint child Never contributes zero cancellation gain and the original
advancing-only Never row. No patient singleton-or-Never floor is inserted. -/
theorem cancellationWithdrawal_neverRow_pointwise
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : CancellationWithdrawalRewardCertificate reward)
    (evaluation : WithTop ℕ → ℝ) (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (times : ι → Option ℕ) (deadline : ℕ)
    (hfirst : quittingEarliestStoppingValue times = ⊤) :
    cappedClockActualEvaluatedOutsideGain reward evaluation times (some deadline) ≤
      ∑ i, (certificate.advanceWeight i *
          cappedClockActualEvaluatedChildGain reward evaluation times (some deadline) i +
        certificate.withdrawalWeight i *
          cancellationActualEvaluatedChildGain reward evaluation times (some deadline) i) := by
  have hnever := (quittingEarliestStoppingValue_eq_top_iff times).mp hfirst
  have htimes : times = fun _ => none := funext hnever
  have hquiet := quittingFirstStoppingOutcome_quietParentClocks_of_first_eq_top times hfirst
  have hquietZero (who : Option ι) :
      quittingPureClockTerminalPayoff reward (quietParentClocks times) who = 0 := by
    simp [quittingPureClockTerminalPayoff, hquiet]
  have hraw := quietExtension_allNeverGains (ι := ι) reward deadline
  rw [← htimes] at hraw
  have hnewOutside : quittingPureClockTerminalPayoff reward
      (outsideDeadlineClocks times (some deadline)) none =
      reward ⟨{none}, Finset.singleton_nonempty none⟩ none := by
    have h := hraw.1
    rw [cappedClockActualOutsideGain, hquietZero, sub_zero] at h
    exact h
  have hnewChild (i : ι) : quittingPureClockTerminalPayoff reward
      (cappedChildParentClocks times (some deadline) i) (some i) =
      reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) := by
    have h := hraw.2 i
    rw [cappedClockActualChildGain, hquietZero, sub_zero] at h
    exact h
  have hcancel (i : ι) :
      cancellationActualEvaluatedChildGain reward evaluation times (some deadline) i = 0 := by
    rw [cancellationActualEvaluatedChildGain_eq_withdrawal_at_own
      reward evaluation times deadline i (by simp [hnever i, quittingStoppingTimeValue]),
      hnever i, deadlineWithdrawalActualEvaluatedChildGain_none]
  have hrow := mul_le_mul_of_nonneg_left certificate.never_row (evaluation_nonneg deadline)
  rw [Finset.mul_sum] at hrow
  simpa only [cappedClockActualEvaluatedOutsideGain, cappedClockActualEvaluatedChildGain,
    quittingPureClockEvaluatedPayoff_eq_evaluation_mul_terminalPayoff, hnewOutside, hnewChild,
    hquietZero, quittingEarliestStoppingValue_outsideDeadlineClocks,
    quittingEarliestStoppingValue_cappedChildParentClocks,
    quittingEarliestStoppingValue_quietParentClocks, hfirst, hcancel,
    quittingStoppingTimeValue, min_top_left, mul_zero, sub_zero, add_zero, mul_left_comm,
    mul_assoc] using hrow

/-- The complete deterministic evaluated cancellation comparison, including
Never deadlines and every relative first-date ordering. -/
theorem cancellationWithdrawalActualEvaluatedOutsideGain_le_weighted_childGains
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : CancellationWithdrawalRewardCertificate reward)
    (evaluation : WithTop ℕ → ℝ) (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (times : ι → Option ℕ) (deadline : Option ℕ) :
    cappedClockActualEvaluatedOutsideGain reward evaluation times deadline ≤
      ∑ i, (certificate.advanceWeight i *
          cappedClockActualEvaluatedChildGain reward evaluation times deadline i +
        certificate.withdrawalWeight i *
          cancellationActualEvaluatedChildGain reward evaluation times deadline i) := by
  cases deadline with
  | none =>
      have h := deadlineWithdrawal_allEvaluatedGains_zero_of_deadline_none reward evaluation times
      have hadvance (i : ι) := (h.2 i).1
      simp only [h.1, hadvance, cancellationActualEvaluatedChildGain_none,
        mul_zero, add_zero, Finset.sum_const_zero, le_refl]
  | some time =>
      by_cases hafter : quittingEarliestStoppingValue times < (time : WithTop ℕ)
      · have h := deadlineWithdrawal_allEvaluatedGains_zero_of_first_lt
          reward evaluation times time hafter
        have hadvance (i : ι) := (h.2 i).1
        have hcancel (i : ι) := cancellationActualEvaluatedChildGain_of_first_lt
          reward evaluation times time i hafter
        simp only [h.1, hadvance, hcancel, mul_zero, add_zero, Finset.sum_const_zero, le_refl]
      · induction hfirst : quittingEarliestStoppingValue times using WithTop.recTopCoe with
        | top =>
            exact cancellationWithdrawal_neverRow_pointwise
              reward certificate evaluation evaluation_nonneg times time hfirst
        | coe first =>
            have hle : time ≤ first := by
              have hle' := not_lt.mp hafter
              rw [hfirst] at hle'
              exact WithTop.coe_le_coe.mp hle'
            rcases hle.eq_or_lt with htie | hbefore
            · subst first
              exact cancellationWithdrawal_joinRow_pointwise reward certificate
                evaluation evaluation_nonneg evaluation_antitone times time hfirst
            · exact cancellationWithdrawal_futureRow_pointwise reward certificate
                evaluation evaluation_nonneg evaluation_antitone times time first hfirst hbefore

end GameTheory

import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalPointwise

/-!
# Deadline-withdrawal deterministic comparison

The three finite raw D rows dominate the outsider's evaluated gain by
separate advancing and atom-withdrawal gains at every pure clock tuple.
The independent-law and full behavioral-cap transports remain separate.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A withdrawal at a deadline strictly after child absorption leaves the
first coalition and evaluation date unchanged, hence has zero gain. -/
theorem deadlineWithdrawalActualEvaluatedChildGain_of_first_lt
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (times : ι → Option ℕ) (deadline : ℕ) (i : ι)
    (hafter : quittingEarliestStoppingValue times < (deadline : WithTop ℕ)) :
    deadlineWithdrawalActualEvaluatedChildGain reward evaluation times
      (some deadline) i = 0 := by
  by_cases hclock : times i = some deadline
  · induction hfirst : quittingEarliestStoppingValue times using WithTop.recTopCoe with
    | top => simp [hfirst] at hafter
    | coe firstTime =>
        have hfirst' : quittingEarliestStoppingValue times =
            (firstTime : WithTop ℕ) := hfirst
        have hbefore : (firstTime : WithTop ℕ) < (deadline : WithTop ℕ) := by
          simpa [hfirst] using hafter
        let A := quittingEarliestStoppingCoalition times
        have hA : A.Nonempty := quittingEarliestStoppingCoalition_nonempty times
        obtain ⟨blocker, hblocker⟩ := hA
        have hblockerClock : quittingStoppingTimeValue (times blocker) =
            (firstTime : WithTop ℕ) := by
          simpa [A, quittingEarliestStoppingCoalition, hfirst'] using hblocker
        have hne : blocker ≠ i := by
          intro heq
          subst blocker
          rw [hclock] at hblockerClock
          simp [quittingStoppingTimeValue] at hblockerClock
          exact (Nat.ne_of_lt (WithTop.coe_lt_coe.mp hbefore))
            hblockerClock.symm
        have hrest : (A.erase i).Nonempty := by
          exact ⟨blocker, Finset.mem_erase.mpr ⟨hne, hblocker⟩⟩
        have hwithdraw := withdrawnChildParentClocks_eq_quiet_update_none
          times deadline i hclock
        have hnewFirst : quittingEarliestStoppingValue
            (withdrawnChildParentClocks times (some deadline) i) =
            (firstTime : WithTop ℕ) := by
          rw [hwithdraw, quittingEarliestStoppingValue_quietParentClocks]
          exact quittingEarliestStoppingValue_update_none_eq_of_erase_nonempty
            times firstTime i hfirst' hrest
        have hquietFirst := quittingEarliestStoppingValue_quietParentClocks times
        have houtcome : quittingFirstStoppingOutcome
            (withdrawnChildParentClocks times (some deadline) i) =
            quittingFirstStoppingOutcome (quietParentClocks times) := by
          rw [hwithdraw]
          apply quittingFirstStoppingOutcome_eq_of_earlier_stopper
            (hidden := some i) (blocker := some blocker)
          · intro other hother
            cases other with
            | none => rfl
            | some j =>
                have hji : j ≠ i := by
                  intro h
                  exact hother (congrArg some h)
                simp [quietParentClocks, Function.update_of_ne hji]
          · change quittingStoppingTimeValue
                ((Function.update times i none) blocker) <
              quittingStoppingTimeValue ((Function.update times i none) i)
            rw [Function.update_of_ne hne, Function.update_self, hblockerClock]
            simp [quittingStoppingTimeValue]
          · change quittingStoppingTimeValue (times blocker) <
              quittingStoppingTimeValue (times i)
            rw [hblockerClock, hclock]
            exact hbefore
        simp [deadlineWithdrawalActualEvaluatedChildGain,
          quittingPureClockEvaluatedPayoff, houtcome, hnewFirst,
          hquietFirst, hfirst']
  · exact deadlineWithdrawalActualEvaluatedChildGain_some_of_ne
      reward evaluation times deadline i hclock

/-- Every tested gain is zero when the proposed outsider deadline is after
the original finite first child absorption. -/
theorem deadlineWithdrawal_allEvaluatedGains_zero_of_first_lt
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (times : ι → Option ℕ) (deadline : ℕ)
    (hafter : quittingEarliestStoppingValue times < (deadline : WithTop ℕ)) :
    cappedClockActualEvaluatedOutsideGain reward evaluation times
        (some deadline) = 0 ∧
      ∀ i, cappedClockActualEvaluatedChildGain reward evaluation times
          (some deadline) i = 0 ∧
        deadlineWithdrawalActualEvaluatedChildGain reward evaluation times
          (some deadline) i = 0 := by
  induction hfirst : quittingEarliestStoppingValue times using WithTop.recTopCoe with
  | top => simp [hfirst] at hafter
  | coe firstTime =>
      have hfirst' : quittingEarliestStoppingValue times =
          (firstTime : WithTop ℕ) := hfirst
      have hafter' : (firstTime : WithTop ℕ) < (deadline : WithTop ℕ) := by
        simpa [hfirst] using hafter
      have hquiet := quittingFirstStoppingOutcome_quietParentClocks_of_first_eq
        times firstTime hfirst'
      have houtside := quittingFirstStoppingOutcome_outsideDeadlineClocks_of_first_lt
        times deadline hafter
      have hcap (i : ι) := quittingFirstStoppingOutcome_cappedChildParentClocks_of_first_lt
        times firstTime deadline i hfirst' hafter'
      have hquietFirst := quittingEarliestStoppingValue_quietParentClocks times
      have houtsideFirst := quittingEarliestStoppingValue_outsideDeadlineClocks
        times (some deadline)
      have hcapFirst (i : ι) := quittingEarliestStoppingValue_cappedChildParentClocks
        times (some deadline) i
      have hmin : min (firstTime : WithTop ℕ)
          (quittingStoppingTimeValue (some deadline)) = (firstTime : WithTop ℕ) := by
        simpa [quittingStoppingTimeValue] using (min_eq_left hafter'.le)
      constructor
      · simp [cappedClockActualEvaluatedOutsideGain,
          quittingPureClockEvaluatedPayoff, houtside, hquietFirst,
          houtsideFirst, hfirst', hmin]
      · intro i
        constructor
        · simp [cappedClockActualEvaluatedChildGain,
            quittingPureClockEvaluatedPayoff, hquiet, hcap,
            hquietFirst, hcapFirst, hfirst', hmin]
        · exact deadlineWithdrawalActualEvaluatedChildGain_of_first_lt
            reward evaluation times deadline i hafter

/-- An outsider Never clock changes no experiment. -/
theorem deadlineWithdrawal_allEvaluatedGains_zero_of_deadline_none
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (times : ι → Option ℕ) :
    cappedClockActualEvaluatedOutsideGain reward evaluation times none = 0 ∧
      ∀ i, cappedClockActualEvaluatedChildGain reward evaluation times none i = 0 ∧
        deadlineWithdrawalActualEvaluatedChildGain reward evaluation times none i = 0 := by
  have houtside : outsideDeadlineClocks times none = quietParentClocks times := by
    funext player
    cases player <;> rfl
  have hcap (i : ι) : cappedChildParentClocks times none i =
      quietParentClocks times := by
    funext player
    cases player with
    | none => rfl
    | some j =>
        by_cases h : j = i
        · subst j
          simp [cappedChildParentClocks, quietParentClocks,
            cappedStoppingClock, quittingStoppingTimeValue]
        · simp [cappedChildParentClocks, quietParentClocks, h]
  constructor
  · simp [cappedClockActualEvaluatedOutsideGain, houtside]
  · intro i
    simp [cappedClockActualEvaluatedChildGain, hcap,
      deadlineWithdrawalActualEvaluatedChildGain_none]

/-- The joint-child-Never case is exactly the D-N row, with every
withdrawal gain zero because no child has a finite deadline atom. -/
theorem deadlineWithdrawal_neverRow_pointwise
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : DeadlineWithdrawalRewardCertificate reward)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (times : ι → Option ℕ) (deadline : ℕ)
    (hfirst : quittingEarliestStoppingValue times = ⊤) :
    cappedClockActualEvaluatedOutsideGain reward evaluation times
        (some deadline) ≤
      ∑ i, (certificate.advanceWeight i *
          cappedClockActualEvaluatedChildGain reward evaluation times
            (some deadline) i +
        certificate.withdrawalWeight i *
          deadlineWithdrawalActualEvaluatedChildGain reward evaluation times
            (some deadline) i) := by
  have hquiet := quittingFirstStoppingOutcome_quietParentClocks_of_first_eq_top
    times hfirst
  have houtside := quittingFirstStoppingOutcome_outsideDeadlineClocks_of_lt_first
    times deadline (by simp [hfirst])
  have hcap (i : ι) := quittingFirstStoppingOutcome_cappedChildParentClocks_of_lt_first
    times deadline i (by simp [hfirst])
  have hquietFirst := quittingEarliestStoppingValue_quietParentClocks times
  have houtsideFirst := quittingEarliestStoppingValue_outsideDeadlineClocks
    times (some deadline)
  have hcapFirst (i : ι) := quittingEarliestStoppingValue_cappedChildParentClocks
    times (some deadline) i
  have hwithdraw (i : ι) :
      deadlineWithdrawalActualEvaluatedChildGain reward evaluation times
        (some deadline) i = 0 := by
    apply deadlineWithdrawalActualEvaluatedChildGain_some_of_ne
    intro hclock
    have hle : quittingEarliestStoppingValue times ≤
        quittingStoppingTimeValue (times i) :=
      Finset.inf_le (Finset.mem_univ i)
    rw [hfirst, hclock] at hle
    simp [quittingStoppingTimeValue] at hle
  have hrow := mul_le_mul_of_nonneg_left certificate.never_row
    (evaluation_nonneg (deadline : WithTop ℕ))
  rw [Finset.mul_sum] at hrow
  simpa [cappedClockActualEvaluatedOutsideGain,
    cappedClockActualEvaluatedChildGain, quittingPureClockEvaluatedPayoff,
    hquiet, houtside, hcap, hquietFirst, houtsideFirst, hcapFirst,
    hfirst, hwithdraw, quittingStoppingTimeValue,
    mul_assoc, mul_left_comm, mul_comm] using hrow

/-- When the deadline strictly precedes a finite child first stop, the
withdrawal atom never fires. The evaluated comparison is precisely D-N/F
with its early-minus-late cancellation. -/
theorem deadlineWithdrawal_futureRow_pointwise
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : DeadlineWithdrawalRewardCertificate reward)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (times : ι → Option ℕ) (deadline firstTime : ℕ)
    (hfirst : quittingEarliestStoppingValue times = (firstTime : WithTop ℕ))
    (hbefore : (deadline : WithTop ℕ) < (firstTime : WithTop ℕ)) :
    cappedClockActualEvaluatedOutsideGain reward evaluation times
        (some deadline) ≤
      ∑ i, (certificate.advanceWeight i *
          cappedClockActualEvaluatedChildGain reward evaluation times
            (some deadline) i +
        certificate.withdrawalWeight i *
          deadlineWithdrawalActualEvaluatedChildGain reward evaluation times
            (some deadline) i) := by
  let A := quittingEarliestStoppingCoalition times
  have hA : A.Nonempty := quittingEarliestStoppingCoalition_nonempty times
  have hquiet := quittingFirstStoppingOutcome_quietParentClocks_of_first_eq
    times firstTime hfirst
  have houtside := quittingFirstStoppingOutcome_outsideDeadlineClocks_of_lt_first
    times deadline (by simpa [hfirst] using hbefore)
  have hcap (i : ι) := quittingFirstStoppingOutcome_cappedChildParentClocks_of_lt_first
    times deadline i (by simpa [hfirst] using hbefore)
  have hquietFirst := quittingEarliestStoppingValue_quietParentClocks times
  have houtsideFirst := quittingEarliestStoppingValue_outsideDeadlineClocks
    times (some deadline)
  have hcapFirst (i : ι) := quittingEarliestStoppingValue_cappedChildParentClocks
    times (some deadline) i
  have hwithdraw (i : ι) :
      deadlineWithdrawalActualEvaluatedChildGain reward evaluation times
        (some deadline) i = 0 := by
    apply deadlineWithdrawalActualEvaluatedChildGain_some_of_ne
    intro hclock
    have hle : quittingEarliestStoppingValue times ≤
        quittingStoppingTimeValue (times i) :=
      Finset.inf_le (Finset.mem_univ i)
    rw [hfirst, hclock] at hle
    exact (not_le_of_gt hbefore) (by simpa [quittingStoppingTimeValue] using hle)
  have hrow := deadlineWithdrawal_futureRows_evaluated
    certificate.advanceWeight
    (fun i => reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i))
    (fun i => reward ⟨cappedClockChildCoalition A,
      cappedClockChildCoalition_nonempty hA⟩ (some i))
    (reward ⟨{none}, Finset.singleton_nonempty none⟩ none)
    (reward ⟨cappedClockChildCoalition A,
      cappedClockChildCoalition_nonempty hA⟩ none)
    (evaluation deadline) (evaluation firstTime)
    (evaluation_nonneg _) (evaluation_antitone hbefore.le)
    certificate.never_row (certificate.future_row A hA)
  simpa [cappedClockActualEvaluatedOutsideGain,
    cappedClockActualEvaluatedChildGain, quittingPureClockEvaluatedPayoff,
    hquiet, houtside, hcap, hquietFirst, houtsideFirst, hcapFirst,
    hfirst, hwithdraw, quittingStoppingTimeValue,
    min_eq_right hbefore.le, mul_comm] using hrow

/-- At an exact tie, D-J pays for the advancing join gain and the
withdrawal floor separately; the latter is bounded by the actual
atom-withdrawal gain for every child. -/
theorem deadlineWithdrawal_joinRow_pointwise
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : DeadlineWithdrawalRewardCertificate reward)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (times : ι → Option ℕ) (deadline : ℕ)
    (hfirst : quittingEarliestStoppingValue times = (deadline : WithTop ℕ)) :
    cappedClockActualEvaluatedOutsideGain reward evaluation times
        (some deadline) ≤
      ∑ i, (certificate.advanceWeight i *
          cappedClockActualEvaluatedChildGain reward evaluation times
            (some deadline) i +
        certificate.withdrawalWeight i *
          deadlineWithdrawalActualEvaluatedChildGain reward evaluation times
            (some deadline) i) := by
  let A := quittingEarliestStoppingCoalition times
  have hA : A.Nonempty := quittingEarliestStoppingCoalition_nonempty times
  have hquiet := quittingFirstStoppingOutcome_quietParentClocks_of_first_eq
    times deadline hfirst
  have houtcome := quittingFirstStoppingOutcome_outsideDeadlineClocks_of_eq_first
    times deadline hfirst
  have hcap (i : ι) := quittingFirstStoppingOutcome_cappedChildParentClocks_of_eq_first
    times deadline i hfirst
  have hquietFirst := quittingEarliestStoppingValue_quietParentClocks times
  have houtsideFirst := quittingEarliestStoppingValue_outsideDeadlineClocks
    times (some deadline)
  have hcapFirst (i : ι) := quittingEarliestStoppingValue_cappedChildParentClocks
    times (some deadline) i
  have houtsideEq : cappedClockActualEvaluatedOutsideGain reward evaluation
      times (some deadline) =
    evaluation deadline *
      (reward ⟨cappedClockJoinedCoalition A,
          cappedClockJoinedCoalition_nonempty A⟩ none -
        reward ⟨cappedClockChildCoalition A,
          cappedClockChildCoalition_nonempty hA⟩ none) := by
    simp [cappedClockActualEvaluatedOutsideGain,
      quittingPureClockEvaluatedPayoff, hquiet, houtcome,
      hquietFirst, houtsideFirst, hfirst, A, quittingStoppingTimeValue,
      mul_sub]
  have hcapEq (i : ι) : cappedClockActualEvaluatedChildGain reward evaluation
      times (some deadline) i =
    evaluation deadline *
      (reward ⟨cappedClockChildCoalition (insert i A),
          cappedClockChildCoalition_nonempty (Finset.insert_nonempty i A)⟩ (some i) -
        reward ⟨cappedClockChildCoalition A,
          cappedClockChildCoalition_nonempty hA⟩ (some i)) := by
    simp [cappedClockActualEvaluatedChildGain,
      quittingPureClockEvaluatedPayoff, hquiet, hcap,
      hquietFirst, hcapFirst, hfirst, A, quittingStoppingTimeValue,
      mul_sub]
  have hrow := mul_le_mul_of_nonneg_left (certificate.join_row A hA)
    (evaluation_nonneg (deadline : WithTop ℕ))
  rw [Finset.mul_sum] at hrow
  calc
    cappedClockActualEvaluatedOutsideGain reward evaluation times (some deadline) =
        evaluation deadline *
          (reward ⟨cappedClockJoinedCoalition A,
              cappedClockJoinedCoalition_nonempty A⟩ none -
            reward ⟨cappedClockChildCoalition A,
              cappedClockChildCoalition_nonempty hA⟩ none) := houtsideEq
    _ ≤ ∑ i, evaluation deadline *
          (certificate.advanceWeight i *
              (reward ⟨cappedClockChildCoalition (insert i A),
                cappedClockChildCoalition_nonempty
                  (Finset.insert_nonempty i A)⟩ (some i) -
                reward ⟨cappedClockChildCoalition A,
                  cappedClockChildCoalition_nonempty hA⟩ (some i)) +
            certificate.withdrawalWeight i *
              deadlineWithdrawalGainFloor reward i A hA) := hrow
    _ ≤ ∑ i, (certificate.advanceWeight i *
            cappedClockActualEvaluatedChildGain reward evaluation times
              (some deadline) i +
          certificate.withdrawalWeight i *
            deadlineWithdrawalActualEvaluatedChildGain reward evaluation times
              (some deadline) i) := by
      apply Finset.sum_le_sum
      intro i _
      have hfloor := deadlineWithdrawalActualEvaluatedChildGain_tie_ge_floor
        reward evaluation evaluation_nonneg evaluation_antitone
        times deadline i hfirst
      calc
        evaluation deadline *
            (certificate.advanceWeight i *
                (reward ⟨cappedClockChildCoalition (insert i A),
                  cappedClockChildCoalition_nonempty
                    (Finset.insert_nonempty i A)⟩ (some i) -
                  reward ⟨cappedClockChildCoalition A,
                    cappedClockChildCoalition_nonempty hA⟩ (some i)) +
              certificate.withdrawalWeight i *
                deadlineWithdrawalGainFloor reward i A hA) =
          certificate.advanceWeight i *
              cappedClockActualEvaluatedChildGain reward evaluation times
                (some deadline) i +
            certificate.withdrawalWeight i *
              (evaluation deadline * deadlineWithdrawalGainFloor reward i A hA) := by
          rw [hcapEq]
          ring
        _ ≤ _ := add_le_add_right
          (mul_le_mul_of_nonneg_left hfloor
            (certificate.withdrawalWeight_nonneg i)) _

/-- Literal all-clock deterministic D comparison: the outsider's evaluated
gain is bounded by separate a-weighted advance and b-weighted atom-withdrawal
gains. No strategy or cap is supplied. -/
theorem deadlineWithdrawalActualEvaluatedOutsideGain_le_weighted_childGains
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : DeadlineWithdrawalRewardCertificate reward)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (times : ι → Option ℕ) (deadline : Option ℕ) :
    cappedClockActualEvaluatedOutsideGain reward evaluation times deadline ≤
      ∑ i, (certificate.advanceWeight i *
          cappedClockActualEvaluatedChildGain reward evaluation times deadline i +
        certificate.withdrawalWeight i *
          deadlineWithdrawalActualEvaluatedChildGain reward evaluation times
            deadline i) := by
  cases deadline with
  | none =>
      have h := deadlineWithdrawal_allEvaluatedGains_zero_of_deadline_none
        reward evaluation times
      have hsum : (∑ i, (certificate.advanceWeight i *
            cappedClockActualEvaluatedChildGain reward evaluation times none i +
          certificate.withdrawalWeight i *
            deadlineWithdrawalActualEvaluatedChildGain reward evaluation times
              none i)) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [(h.2 i).1, (h.2 i).2]
        ring
      rw [h.1, hsum]
  | some time =>
      let first := quittingEarliestStoppingValue times
      by_cases hafter : first < (time : WithTop ℕ)
      · have h := deadlineWithdrawal_allEvaluatedGains_zero_of_first_lt
          reward evaluation times time hafter
        have hsum : (∑ i, (certificate.advanceWeight i *
              cappedClockActualEvaluatedChildGain reward evaluation times
                (some time) i +
            certificate.withdrawalWeight i *
              deadlineWithdrawalActualEvaluatedChildGain reward evaluation times
                (some time) i)) = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          rw [(h.2 i).1, (h.2 i).2]
          ring
        rw [h.1, hsum]
      · by_cases htie : first = (time : WithTop ℕ)
        · exact deadlineWithdrawal_joinRow_pointwise reward certificate evaluation
            evaluation_nonneg evaluation_antitone times time htie
        · have hbefore : (time : WithTop ℕ) < first :=
            lt_of_le_of_ne (le_of_not_gt hafter) (fun h => htie h.symm)
          induction hfirst : first using WithTop.recTopCoe with
          | top =>
              exact deadlineWithdrawal_neverRow_pointwise reward certificate
                evaluation evaluation_nonneg times time (by simpa [first] using hfirst)
          | coe firstTime =>
              exact deadlineWithdrawal_futureRow_pointwise reward certificate
                evaluation evaluation_nonneg evaluation_antitone
                times time firstTime (by simpa [first] using hfirst)
                (by simpa [hfirst] using hbefore)

end GameTheory

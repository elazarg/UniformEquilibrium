import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalRestartPointwiseCore

/-! # Shared raw-row comparison for private post-deadline restarts -/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Internal N/F/J interface with an explicit singleton floor and join-row error. -/
structure DeadlineRestartRewardCertificate
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (floor : ι → ℝ) (rowError : ℝ) where
  advanceWeight : ι → ℝ
  withdrawalWeight : ι → ℝ
  advanceWeight_nonneg : ∀ i, 0 ≤ advanceWeight i
  withdrawalWeight_nonneg : ∀ i, 0 ≤ withdrawalWeight i
  never_row :
    reward ⟨{none}, Finset.singleton_nonempty none⟩ none ≤
      ∑ i, advanceWeight i *
        reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i)
  future_row : ∀ A (hA : A.Nonempty),
    reward ⟨{none}, Finset.singleton_nonempty none⟩ none -
        reward ⟨cappedClockChildCoalition A,
          cappedClockChildCoalition_nonempty hA⟩ none ≤
      ∑ i, advanceWeight i *
        (reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) -
          reward ⟨cappedClockChildCoalition A,
            cappedClockChildCoalition_nonempty hA⟩ (some i))
  join_row : ∀ A (hA : A.Nonempty),
    reward ⟨cappedClockJoinedCoalition A,
          cappedClockJoinedCoalition_nonempty A⟩ none -
        reward ⟨cappedClockChildCoalition A,
          cappedClockChildCoalition_nonempty hA⟩ none ≤
      (∑ i, (advanceWeight i *
          (reward ⟨cappedClockChildCoalition (insert i A),
              cappedClockChildCoalition_nonempty (Finset.insert_nonempty i A)⟩ (some i) -
            reward ⟨cappedClockChildCoalition A,
              cappedClockChildCoalition_nonempty hA⟩ (some i)) +
        withdrawalWeight i *
          deadlineSecurityGainFloorWithRestart reward (floor i) i A hA)) + rowError


variable {floor : ι → ℝ} {rowError : ℝ}

/-- Every tested gain is zero when the proposed outsider deadline is after
the original finite first child absorption. -/
theorem deadlineSecurity_allEvaluatedGains_zero_of_first_ltWithRestart
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (restart : ι → ℕ → PMF (Option ℕ))
    (evaluation : WithTop ℕ → ℝ)
    (times : ι → Option ℕ) (deadline : ℕ)
    (hafter : quittingEarliestStoppingValue times < (deadline : WithTop ℕ))
    (hbefore : ∀ i date chosen, chosen ≤ date → restart i date (some chosen) = 0) :
    cappedClockActualEvaluatedOutsideGain reward evaluation times
        (some deadline) = 0 ∧
      ∀ i, cappedClockActualEvaluatedChildGain reward evaluation times
          (some deadline) i = 0 ∧
        deadlineSecurityActualEvaluatedChildGainWithRestart reward (restart i) evaluation times
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
        · exact deadlineSecurityActualEvaluatedChildGain_of_first_ltWithRestart reward (restart i)
            evaluation times deadline i hafter (hbefore i)

/-- An outsider Never clock changes no experiment. -/
theorem deadlineSecurity_allEvaluatedGains_zero_of_deadline_noneWithRestart
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (restart : ι → ℕ → PMF (Option ℕ))
    (evaluation : WithTop ℕ → ℝ)
    (times : ι → Option ℕ) :
    cappedClockActualEvaluatedOutsideGain reward evaluation times none = 0 ∧
      ∀ i, cappedClockActualEvaluatedChildGain reward evaluation times none i = 0 ∧
        deadlineSecurityActualEvaluatedChildGainWithRestart reward (restart i) evaluation times
          none i = 0 := by
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
      deadlineSecurityActualEvaluatedChildGain_noneWithRestart]

/-- The joint-child-Never case is exactly the D-N row, with every
withdrawal gain zero because no child has a finite deadline atom. -/
theorem deadlineSecurity_neverRow_pointwiseWithRestart
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (restart : ι → ℕ → PMF (Option ℕ))
    (certificate : DeadlineRestartRewardCertificate reward floor rowError)
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
          deadlineSecurityActualEvaluatedChildGainWithRestart reward (restart i) evaluation times
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
      deadlineSecurityActualEvaluatedChildGainWithRestart reward (restart i) evaluation times
        (some deadline) i = 0 := by
    apply deadlineSecurityActualEvaluatedChildGain_of_neWithRestart
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
theorem deadlineSecurity_futureRow_pointwiseWithRestart
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (restart : ι → ℕ → PMF (Option ℕ))
    (certificate : DeadlineRestartRewardCertificate reward floor rowError)
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
          deadlineSecurityActualEvaluatedChildGainWithRestart reward (restart i) evaluation times
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
      deadlineSecurityActualEvaluatedChildGainWithRestart reward (restart i) evaluation times
        (some deadline) i = 0 := by
    apply deadlineSecurityActualEvaluatedChildGain_of_neWithRestart
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
theorem deadlineSecurity_joinRow_pointwiseWithRestart
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (restart : ι → ℕ → PMF (Option ℕ))
    (certificate : DeadlineRestartRewardCertificate reward floor rowError)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (times : ι → Option ℕ) (deadline : ℕ)
    (hfirst : quittingEarliestStoppingValue times = (deadline : WithTop ℕ))
    (hbefore : ∀ i date chosen, chosen ≤ date → restart i date (some chosen) = 0)
    (hplan : ∀ i (date : ℕ) (opponents : ι → Option ℕ), opponents i = none →
      (∀ j, (date : WithTop ℕ) < quittingStoppingTimeValue (opponents j)) →
      evaluation date * floor i ≤ _root_.Math.Probability.expect (restart i date)
        (fun clock => quittingPureClockEvaluatedPayoff reward evaluation
          (Function.update (quietParentClocks opponents) (some i) clock) (some i))) :
    cappedClockActualEvaluatedOutsideGain reward evaluation times
        (some deadline) ≤
      (∑ i, (certificate.advanceWeight i *
          cappedClockActualEvaluatedChildGain reward evaluation times
            (some deadline) i +
        certificate.withdrawalWeight i *
          deadlineSecurityActualEvaluatedChildGainWithRestart reward (restart i) evaluation times
            (some deadline) i)) + evaluation deadline * rowError := by
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
  rw [mul_add, Finset.mul_sum] at hrow
  calc
    cappedClockActualEvaluatedOutsideGain reward evaluation times (some deadline) =
        evaluation deadline *
          (reward ⟨cappedClockJoinedCoalition A,
              cappedClockJoinedCoalition_nonempty A⟩ none -
            reward ⟨cappedClockChildCoalition A,
              cappedClockChildCoalition_nonempty hA⟩ none) := houtsideEq
    _ ≤ (∑ i, evaluation deadline *
          (certificate.advanceWeight i *
              (reward ⟨cappedClockChildCoalition (insert i A),
                cappedClockChildCoalition_nonempty
                  (Finset.insert_nonempty i A)⟩ (some i) -
                reward ⟨cappedClockChildCoalition A,
                  cappedClockChildCoalition_nonempty hA⟩ (some i)) +
            certificate.withdrawalWeight i *
              deadlineSecurityGainFloorWithRestart reward (floor i) i A hA)) +
          evaluation deadline * rowError := hrow
    _ ≤ (∑ i, (certificate.advanceWeight i *
            cappedClockActualEvaluatedChildGain reward evaluation times
              (some deadline) i +
          certificate.withdrawalWeight i *
            deadlineSecurityActualEvaluatedChildGainWithRestart reward (restart i) evaluation times
              (some deadline) i)) + evaluation deadline * rowError := by
      refine add_le_add ?_ le_rfl
      apply Finset.sum_le_sum
      intro i _
      have hfloor := deadlineSecurityActualEvaluatedChildGain_tie_floorWithRestart reward (restart
        i) (floor i) evaluation evaluation_nonneg evaluation_antitone
        times deadline i hfirst (hbefore i) (hplan i)
      calc
        evaluation deadline *
            (certificate.advanceWeight i *
                (reward ⟨cappedClockChildCoalition (insert i A),
                  cappedClockChildCoalition_nonempty
                    (Finset.insert_nonempty i A)⟩ (some i) -
                  reward ⟨cappedClockChildCoalition A,
                    cappedClockChildCoalition_nonempty hA⟩ (some i)) +
              certificate.withdrawalWeight i *
                deadlineSecurityGainFloorWithRestart reward (floor i) i A hA) =
          certificate.advanceWeight i *
              cappedClockActualEvaluatedChildGain reward evaluation times
                (some deadline) i +
            certificate.withdrawalWeight i *
              (evaluation deadline * deadlineSecurityGainFloorWithRestart reward (floor i) i A hA)
                := by
          rw [hcapEq]
          ring
        _ ≤ _ := add_le_add_right
          (mul_le_mul_of_nonneg_left hfloor
            (certificate.withdrawalWeight_nonneg i)) _

/-- The common deterministic comparison allows a nonnegative join-row
error. Post-deadline support and singleton security are supplied internally
by the actual evaluated or terminal reward-table plan producer. -/
theorem deadlineSecurityActualEvaluatedOutsideGain_le_weighted_childGainsWithRestart
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (restart : ι → ℕ → PMF (Option ℕ))
    (certificate : DeadlineRestartRewardCertificate reward floor rowError)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (times : ι → Option ℕ) (deadline : Option ℕ)
    (hrowError : 0 ≤ rowError)
    (hbefore : ∀ i date chosen, chosen ≤ date → restart i date (some chosen) = 0)
    (hplan : ∀ i (date : ℕ) (opponents : ι → Option ℕ), opponents i = none →
      (∀ j, (date : WithTop ℕ) < quittingStoppingTimeValue (opponents j)) →
      evaluation date * floor i ≤ _root_.Math.Probability.expect (restart i date)
        (fun clock => quittingPureClockEvaluatedPayoff reward evaluation
          (Function.update (quietParentClocks opponents) (some i) clock) (some i))) :
    cappedClockActualEvaluatedOutsideGain reward evaluation times deadline ≤
      (∑ i, (certificate.advanceWeight i *
          cappedClockActualEvaluatedChildGain reward evaluation times deadline i +
        certificate.withdrawalWeight i *
          deadlineSecurityActualEvaluatedChildGainWithRestart reward (restart i)
            evaluation times deadline i)) + evaluation 0 * rowError := by
  have herror : 0 ≤ evaluation 0 * rowError :=
    mul_nonneg (evaluation_nonneg _) hrowError
  cases deadline with
  | none =>
      have h := deadlineSecurity_allEvaluatedGains_zero_of_deadline_noneWithRestart
        reward restart evaluation times
      have hsum : (∑ i, (certificate.advanceWeight i *
            cappedClockActualEvaluatedChildGain reward evaluation times none i +
          certificate.withdrawalWeight i *
            deadlineSecurityActualEvaluatedChildGainWithRestart reward (restart i)
              evaluation times none i)) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [(h.2 i).1, (h.2 i).2]
        ring
      rw [h.1, hsum, zero_add]
      exact herror
  | some time =>
      let first := quittingEarliestStoppingValue times
      by_cases hafter : first < (time : WithTop ℕ)
      · have h := deadlineSecurity_allEvaluatedGains_zero_of_first_ltWithRestart
          reward restart evaluation times time hafter hbefore
        have hsum : (∑ i, (certificate.advanceWeight i *
              cappedClockActualEvaluatedChildGain reward evaluation times (some time) i +
            certificate.withdrawalWeight i *
              deadlineSecurityActualEvaluatedChildGainWithRestart reward (restart i)
                evaluation times (some time) i)) = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          rw [(h.2 i).1, (h.2 i).2]
          ring
        rw [h.1, hsum, zero_add]
        exact herror
      · by_cases htie : first = (time : WithTop ℕ)
        · exact (deadlineSecurity_joinRow_pointwiseWithRestart reward restart certificate
            evaluation evaluation_nonneg evaluation_antitone times time htie
            hbefore hplan).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right
              (evaluation_antitone (show (0 : WithTop ℕ) ≤ (time : WithTop ℕ) by
                exact_mod_cast (Nat.zero_le time))) hrowError))
        · have hearly : (time : WithTop ℕ) < first :=
            lt_of_le_of_ne (le_of_not_gt hafter) (fun h => htie h.symm)
          induction hfirst : first using WithTop.recTopCoe with
          | top =>
              exact (deadlineSecurity_neverRow_pointwiseWithRestart reward restart certificate
                evaluation evaluation_nonneg times time (by simpa [first] using hfirst)).trans
                  (le_add_of_nonneg_right herror)
          | coe firstTime =>
              exact (deadlineSecurity_futureRow_pointwiseWithRestart reward restart certificate
                evaluation evaluation_nonneg evaluation_antitone times time firstTime
                (by simpa [first] using hfirst)
                (by simpa [hfirst] using hearly)).trans (le_add_of_nonneg_right herror)

end GameTheory

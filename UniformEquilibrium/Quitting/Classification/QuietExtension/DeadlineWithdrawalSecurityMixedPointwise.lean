import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalSecurityMixedBehavioral
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalDomination

/-!
# Security restart gains at the outsider deadline

The singleton branch uses the actual reward-table-selected security law.
All other first-coalition branches retain the literal withdrawal rewards.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The improved all-evaluation withdrawal row changes only singleton
coalitions. The correction is zero for every nonsingleton or nonmember. -/
def deadlineSecurityGainFloor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (A : Finset ι) (hA : A.Nonempty) : ℝ :=
  deadlineWithdrawalGainFloor reward i A hA +
    if A = {i} then min (deadlineWithdrawalSecurityFloor reward i) 0 -
      deadlineWithdrawalZeroFloor reward i else 0

omit [Nonempty ι] in
theorem deadlineSecurityGainFloor_singleton
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) (i : ι) :
    deadlineSecurityGainFloor reward i {i} (Finset.singleton_nonempty i) =
      min (deadlineWithdrawalSecurityFloor reward i) 0 -
        reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) := by
  simp [deadlineSecurityGainFloor, deadlineWithdrawalGainFloor_singleton]

omit [Fintype ι] [Nonempty ι] in
private theorem security_privateClocks_base (times : ι → Option ℕ) (i : ι) :
    deadlinePrivateChildClocks times i (times i) = quietParentClocks times := by
  funext player
  cases player with
  | none => rfl
  | some j => by_cases hj : j = i <;> simp [deadlinePrivateChildClocks, quietParentClocks, hj]

theorem deadlineSecurityActualEvaluatedChildGain_none
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ) (times : ι → Option ℕ) (i : ι) :
    deadlineSecurityActualEvaluatedChildGain reward evaluation times none i = 0 := by
  simp [deadlineSecurityActualEvaluatedChildGain, deadlineSecurityAtomRestartLaw,
    security_privateClocks_base]

theorem deadlineSecurityActualEvaluatedChildGain_of_ne
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ) (times : ι → Option ℕ) (time : ℕ) (i : ι)
    (hne : times i ≠ some time) :
    deadlineSecurityActualEvaluatedChildGain reward evaluation times (some time) i = 0 := by
  simp [deadlineSecurityActualEvaluatedChildGain, deadlineSecurityAtomRestartLaw,
    hne, security_privateClocks_base]

/-- Actual averaged singleton gain at a deadline tie. Every remaining
opponent clock is strictly later, so the selected security plan applies. -/
theorem deadlineSecurityActualEvaluatedChildGain_singleton_floor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (hnonneg : ∀ time, 0 ≤ evaluation time) (hantitone : Antitone evaluation)
    (times : ι → Option ℕ) (time : ℕ) (i : ι)
    (hfirst : quittingEarliestStoppingValue times = (time : WithTop ℕ))
    (hcoalition : quittingEarliestStoppingCoalition times = {i}) :
    evaluation time * deadlineSecurityGainFloor reward i {i}
        (Finset.singleton_nonempty i) ≤
      deadlineSecurityActualEvaluatedChildGain reward evaluation times (some time) i := by
  have hclock : times i = some time := by
    have hmem : i ∈ quittingEarliestStoppingCoalition times := by simp [hcoalition]
    have hvalue : quittingStoppingTimeValue (times i) = (time : WithTop ℕ) := by
      simpa [quittingEarliestStoppingCoalition, hfirst] using hmem
    cases h : times i with
    | none => simp [h, quittingStoppingTimeValue] at hvalue
    | some t =>
        have ht : t = time := by simpa [h, quittingStoppingTimeValue] using hvalue
        simp [ht]
  let opponents := Function.update times i none
  have hfuture : ∀ j, (time : WithTop ℕ) < quittingStoppingTimeValue (opponents j) := by
    intro j
    by_cases hj : j = i
    · subst j
      simp [opponents, quittingStoppingTimeValue]
    · have hnot : j ∉ quittingEarliestStoppingCoalition times := by simp [hcoalition, hj]
      have hne : quittingStoppingTimeValue (times j) ≠ (time : WithTop ℕ) := by
        simpa [quittingEarliestStoppingCoalition, hfirst] using hnot
      have hle : (time : WithTop ℕ) ≤ quittingStoppingTimeValue (times j) := by
        rw [← hfirst]
        exact Finset.inf_le (Finset.mem_univ j)
      simpa [opponents, hj] using lt_of_le_of_ne hle hne.symm
  have hplan := deadlineSecurityEvaluatedRestartFamily_floor reward i time evaluation
    hnonneg hantitone opponents (by simp [opponents]) hfuture
  have hclocks (clock : Option ℕ) :
      Function.update (quietParentClocks opponents) (some i) clock =
        deadlinePrivateChildClocks times i clock := by
    funext player
    cases player with
    | none => simp [quietParentClocks, deadlinePrivateChildClocks]
    | some j => by_cases hj : j = i <;>
        simp [quietParentClocks, opponents, deadlinePrivateChildClocks, hj]
  simp_rw [hclocks] at hplan
  have hsingle : cappedClockChildCoalition ({i} : Finset ι) = {some i} := by
    simp [cappedClockChildCoalition]
    rfl
  have hcurrent : quittingPureClockEvaluatedPayoff reward evaluation
      (quietParentClocks times) (some i) = evaluation time *
        reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) := by
    have houtcome := quittingFirstStoppingOutcome_quietParentClocks_of_first_eq
      times time hfirst
    simp [quittingPureClockEvaluatedPayoff, houtcome,
      quittingEarliestStoppingValue_quietParentClocks, hfirst, hcoalition, hsingle]
  rw [deadlineSecurityGainFloor_singleton, deadlineSecurityActualEvaluatedChildGain,
    hcurrent]
  simp only [deadlineSecurityAtomRestartLaw, hclock, ↓reduceIte]
  nlinarith [hplan]

private theorem security_payoff_eq_of_earlier_stopper
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ) (first second : Option ι → Option ℕ)
    (hidden blocker : Option ι)
    (hagree : ∀ other, other ≠ hidden → first other = second other)
    (hfirst : quittingStoppingTimeValue (first blocker) <
      quittingStoppingTimeValue (first hidden))
    (hsecond : quittingStoppingTimeValue (second blocker) <
      quittingStoppingTimeValue (second hidden)) :
    quittingPureClockEvaluatedPayoff reward evaluation first hidden =
      quittingPureClockEvaluatedPayoff reward evaluation second hidden := by
  have hne : blocker ≠ hidden := by intro h; subst blocker; exact (lt_irrefl _) hfirst
  have hmin : quittingEarliestStoppingValue first = quittingEarliestStoppingValue second := by
    apply le_antisymm
    · apply Finset.le_inf
      intro other _
      by_cases hother : other = hidden
      · subst other
        have hle : quittingEarliestStoppingValue first ≤
            quittingStoppingTimeValue (first blocker) := Finset.inf_le (Finset.mem_univ blocker)
        rw [hagree blocker hne] at hle
        exact hle.trans hsecond.le
      · rw [← hagree other hother]
        exact Finset.inf_le (Finset.mem_univ other)
    · apply Finset.le_inf
      intro other _
      by_cases hother : other = hidden
      · subst other
        have hle : quittingEarliestStoppingValue second ≤
            quittingStoppingTimeValue (second blocker) := Finset.inf_le (Finset.mem_univ blocker)
        rw [← hagree blocker hne] at hle
        exact hle.trans hfirst.le
      · rw [hagree other hother]
        exact Finset.inf_le (Finset.mem_univ other)
  have houtcome := quittingFirstStoppingOutcome_eq_of_earlier_stopper
    first second hagree hfirst hsecond
  simp only [quittingPureClockEvaluatedPayoff, houtcome, hmin]

/-- Once another child stops no later than the withdrawal deadline, a fresh
post-deadline restart and literal Never have identical evaluated payoffs. -/
theorem deadlineSecurityActualEvaluatedChildGain_eq_withdrawal_of_blocker
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ) (times : ι → Option ℕ) (time : ℕ) (i blocker : ι)
    (hclock : times i = some time) (hne : blocker ≠ i)
    (hblocker : quittingStoppingTimeValue (times blocker) ≤ (time : WithTop ℕ)) :
    deadlineSecurityActualEvaluatedChildGain reward evaluation times (some time) i =
      deadlineWithdrawalActualEvaluatedChildGain reward evaluation times (some time) i := by
  let law := deadlineSecurityEvaluatedRestartFamily reward i time
  have hcongr : expect law (fun clock => quittingPureClockEvaluatedPayoff reward evaluation
      (deadlinePrivateChildClocks times i clock) (some i)) =
      quittingPureClockEvaluatedPayoff reward evaluation
        (withdrawnChildParentClocks times (some time) i) (some i) := by
    calc
      _ = expect law (fun _ => quittingPureClockEvaluatedPayoff reward evaluation
          (withdrawnChildParentClocks times (some time) i) (some i)) := by
        apply expect_congr_on_support
        intro clock hsupport
        have hlate : (time : WithTop ℕ) < quittingStoppingTimeValue clock := by
          cases clock with
          | none => simp [quittingStoppingTimeValue]
          | some chosen =>
              have hchosen : time < chosen := by
                by_contra h
                have hzero := deadlineSecurityEvaluatedRestartFamily_before
                  reward i time chosen (Nat.le_of_not_gt h)
                have hnezero : law (some chosen) ≠ 0 := by
                  simpa only [PMF.mem_support_iff] using hsupport
                exact hnezero hzero
              simpa [quittingStoppingTimeValue] using hchosen
        apply security_payoff_eq_of_earlier_stopper reward evaluation
          (deadlinePrivateChildClocks times i clock)
          (withdrawnChildParentClocks times (some time) i) (some i) (some blocker)
        · intro other hother
          cases other with
          | none => rfl
          | some j =>
              have hji : j ≠ i := by intro h; exact hother (congrArg some h)
              simp [deadlinePrivateChildClocks, withdrawnChildParentClocks, hji]
        · simpa [deadlinePrivateChildClocks, hne] using hblocker.trans_lt hlate
        · have hfinite : quittingStoppingTimeValue (times blocker) < ⊤ :=
            hblocker.trans_lt (by simp)
          simpa [withdrawnChildParentClocks, hne, deadlineWithdrawnClock, hclock,
            quittingStoppingTimeValue] using hfinite
      _ = _ := expect_const _ _
  simpa only [deadlineSecurityActualEvaluatedChildGain, deadlineSecurityAtomRestartLaw,
    hclock, ↓reduceIte, deadlineWithdrawalActualEvaluatedChildGain, law] using
    congrArg (fun payoff => payoff -
      quittingPureClockEvaluatedPayoff reward evaluation (quietParentClocks times) (some i)) hcongr

/-- Every security withdrawal contribution at a first-date tie dominates
the improved row, including nonmembers and nonsingleton members. -/
theorem deadlineSecurityActualEvaluatedChildGain_tie_floor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (hnonneg : ∀ time, 0 ≤ evaluation time) (hantitone : Antitone evaluation)
    (times : ι → Option ℕ) (time : ℕ) (i : ι)
    (hfirst : quittingEarliestStoppingValue times = (time : WithTop ℕ)) :
    evaluation time * deadlineSecurityGainFloor reward i
        (quittingEarliestStoppingCoalition times)
        (quittingEarliestStoppingCoalition_nonempty times) ≤
      deadlineSecurityActualEvaluatedChildGain reward evaluation times (some time) i := by
  let A := quittingEarliestStoppingCoalition times
  by_cases hsingle : A = {i}
  · simpa [A, hsingle] using deadlineSecurityActualEvaluatedChildGain_singleton_floor
      reward evaluation hnonneg hantitone times time i hfirst hsingle
  have hfloor : deadlineSecurityGainFloor reward i A
      (quittingEarliestStoppingCoalition_nonempty times) =
      deadlineWithdrawalGainFloor reward i A
        (quittingEarliestStoppingCoalition_nonempty times) := by
    simp [deadlineSecurityGainFloor, hsingle]
  have hgain : deadlineSecurityActualEvaluatedChildGain reward evaluation times (some time) i =
      deadlineWithdrawalActualEvaluatedChildGain reward evaluation times (some time) i := by
    by_cases hclock : times i = some time
    · have hrest : (A.erase i).Nonempty := by
        by_contra h
        have hempty := Finset.not_nonempty_iff_eq_empty.mp h
        rcases (Finset.erase_eq_empty_iff A i).mp hempty with hempty | heq
        · have hnonempty := quittingEarliestStoppingCoalition_nonempty times
          exact hnonempty.ne_empty hempty
        · exact hsingle heq
      obtain ⟨blocker, hblocker⟩ := hrest
      have hparts := Finset.mem_erase.mp hblocker
      have hvalue : quittingStoppingTimeValue (times blocker) = (time : WithTop ℕ) := by
        simpa [A, quittingEarliestStoppingCoalition, hfirst] using hparts.2
      exact deadlineSecurityActualEvaluatedChildGain_eq_withdrawal_of_blocker
        reward evaluation times time i blocker hclock hparts.1 hvalue.le
    · rw [deadlineSecurityActualEvaluatedChildGain_of_ne reward evaluation times time i hclock,
        deadlineWithdrawalActualEvaluatedChildGain_some_of_ne
          reward evaluation times time i hclock]
  rw [hgain]
  change evaluation time * deadlineSecurityGainFloor reward i A _ ≤ _
  rw [hfloor]
  exact deadlineWithdrawalActualEvaluatedChildGain_tie_ge_floor
    reward evaluation hnonneg hantitone times time i hfirst

/-- Restarts after an already completed child absorption have zero gain. -/
theorem deadlineSecurityActualEvaluatedChildGain_of_first_lt
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ) (times : ι → Option ℕ) (time : ℕ) (i : ι)
    (hafter : quittingEarliestStoppingValue times < (time : WithTop ℕ)) :
    deadlineSecurityActualEvaluatedChildGain reward evaluation times (some time) i = 0 := by
  by_cases hclock : times i = some time
  · let blocker := (quittingEarliestStoppingCoalition_nonempty times).choose
    have hmem := (quittingEarliestStoppingCoalition_nonempty times).choose_spec
    have hvalue : quittingStoppingTimeValue (times blocker) =
        quittingEarliestStoppingValue times := by
      simpa [quittingEarliestStoppingCoalition, blocker] using hmem
    have hne : blocker ≠ i := by
      intro h
      rw [h, hclock] at hvalue
      have htime : quittingEarliestStoppingValue times = (time : WithTop ℕ) := hvalue.symm
      rw [htime] at hafter
      exact (lt_irrefl _) hafter
    rw [deadlineSecurityActualEvaluatedChildGain_eq_withdrawal_of_blocker
      reward evaluation times time i blocker hclock hne (hvalue.le.trans hafter.le)]
    exact deadlineWithdrawalActualEvaluatedChildGain_of_first_lt
      reward evaluation times time i hafter
  · exact deadlineSecurityActualEvaluatedChildGain_of_ne reward evaluation times time i hclock

end GameTheory

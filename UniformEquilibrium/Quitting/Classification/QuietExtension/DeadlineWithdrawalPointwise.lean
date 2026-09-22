import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalMixedLaw

/-!
# Deterministic deadline-atom withdrawal

Removing a child's exact finite deadline atom is an actual one-coordinate
clock update. The later-outcome estimate below is the source of the
nonpositive singleton floor in the all-evaluation D-J row.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
/-- Evaluated D-N/D-F cancellation when the outsider deadline precedes
finite child absorption: the early-minus-late evaluation gap charges D-N,
and the remaining late weight charges D-F. -/
theorem deadlineWithdrawal_futureRows_evaluated
    (advanceWeight singleton childReward : ι → ℝ)
    (outsideSingleton outsideReward earlyWeight lateWeight : ℝ)
    (hlate : 0 ≤ lateWeight) (hantitone : lateWeight ≤ earlyWeight)
    (hnever : outsideSingleton ≤ ∑ i, advanceWeight i * singleton i)
    (hfuture : outsideSingleton - outsideReward ≤
      ∑ i, advanceWeight i * (singleton i - childReward i)) :
    earlyWeight * outsideSingleton - lateWeight * outsideReward ≤
      ∑ i, advanceWeight i *
        (earlyWeight * singleton i - lateWeight * childReward i) := by
  have hgap := mul_le_mul_of_nonneg_left hnever (sub_nonneg.mpr hantitone)
  have hlateRow := mul_le_mul_of_nonneg_left hfuture hlate
  calc
    earlyWeight * outsideSingleton - lateWeight * outsideReward =
        (earlyWeight - lateWeight) * outsideSingleton +
          lateWeight * (outsideSingleton - outsideReward) := by ring
    _ ≤ (earlyWeight - lateWeight) * (∑ i, advanceWeight i * singleton i) +
          lateWeight * (∑ i, advanceWeight i *
            (singleton i - childReward i)) := add_le_add hgap hlateRow
    _ = ∑ i, advanceWeight i *
          (earlyWeight * singleton i - lateWeight * childReward i) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

omit [Fintype ι] [Nonempty ι] in
/-- Once the queried child has an atom at the finite deadline, withdrawing
it is exactly a quiet parent lift of that child's Never-updated tuple. -/
theorem withdrawnChildParentClocks_eq_quiet_update_none
    (times : ι → Option ℕ) (time : ℕ) (i : ι)
    (hclock : times i = some time) :
    withdrawnChildParentClocks times (some time) i =
      quietParentClocks (Function.update times i none) := by
  funext player
  cases player with
  | none => rfl
  | some j =>
      by_cases h : j = i
      · subst j
        simp [withdrawnChildParentClocks, quietParentClocks,
          deadlineWithdrawnClock, hclock]
      · simp [withdrawnChildParentClocks, quietParentClocks, h]

/-- Withdrawing a member from a nonsingleton first coalition leaves exactly
the other first-date quitters at the same date. -/
theorem quittingFirstStoppingOutcome_withdrawn_of_tie_erase_nonempty
    (times : ι → Option ℕ) (time : ℕ) (i : ι)
    (hfirst : quittingEarliestStoppingValue times = (time : WithTop ℕ))
    (hi : i ∈ quittingEarliestStoppingCoalition times)
    (hrest : (quittingEarliestStoppingCoalition times).erase i |>.Nonempty) :
    quittingFirstStoppingOutcome
        (withdrawnChildParentClocks times (some time) i) =
      some ⟨cappedClockChildCoalition
          ((quittingEarliestStoppingCoalition times).erase i),
        cappedClockChildCoalition_nonempty hrest⟩ := by
  let A := quittingEarliestStoppingCoalition times
  have hclock : times i = some time := by
    have hvalue : quittingStoppingTimeValue (times i) = (time : WithTop ℕ) := by
      simpa [A, quittingEarliestStoppingCoalition, hfirst] using hi
    cases h : times i with
    | none => simp [h, quittingStoppingTimeValue] at hvalue
    | some t =>
        have ht : t = time := WithTop.coe_eq_coe.mp (by
          simpa [h, quittingStoppingTimeValue] using hvalue)
        simp [ht]
  rw [withdrawnChildParentClocks_eq_quiet_update_none times time i hclock]
  apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later
    (time := time)
  · intro player hplayer
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hplayer
    have hne : j ≠ i := (Finset.mem_erase.mp hj).1
    have hjA : j ∈ A := (Finset.mem_erase.mp hj).2
    change (Function.update times i none) j = some time
    rw [Function.update_of_ne hne]
    have hvalue : quittingStoppingTimeValue (times j) = (time : WithTop ℕ) := by
      simpa [A, quittingEarliestStoppingCoalition, hfirst] using hjA
    cases h : times j with
    | none => simp [h, quittingStoppingTimeValue] at hvalue
    | some t =>
        have ht : t = time := WithTop.coe_eq_coe.mp (by
          simpa [h, quittingStoppingTimeValue] using hvalue)
        simp [ht]
  · intro player hplayer
    cases player with
    | none => simp [quietParentClocks, quittingStoppingTimeValue]
    | some j =>
        by_cases hji : j = i
        · subst j
          simp [quietParentClocks, quittingStoppingTimeValue]
        · have hjA : j ∉ A := by
            intro hjA
            apply hplayer
            exact Finset.mem_map.mpr
              ⟨j, Finset.mem_erase.mpr ⟨hji, hjA⟩, rfl⟩
          have hne : quittingStoppingTimeValue (times j) ≠
              (time : WithTop ℕ) := by
            simpa [A, quittingEarliestStoppingCoalition, hfirst] using hjA
          have hle : (time : WithTop ℕ) ≤
              quittingStoppingTimeValue (times j) := by
            rw [← hfirst]
            exact Finset.inf_le (Finset.mem_univ j)
          change (time : WithTop ℕ) <
            quittingStoppingTimeValue ((Function.update times i none) j)
          rw [Function.update_of_ne hji]
          exact lt_of_le_of_ne hle hne.symm

omit [Nonempty ι] in
/-- Withdrawing one atom at the first child date cannot make another
child's first quitting date earlier. -/
theorem quittingEarliestStoppingValue_update_none_ge
    (times : ι → Option ℕ) (time : ℕ) (i : ι)
    (hfirst : quittingEarliestStoppingValue times = (time : WithTop ℕ)) :
    (time : WithTop ℕ) ≤
      quittingEarliestStoppingValue (Function.update times i none) := by
  unfold quittingEarliestStoppingValue
  apply Finset.le_inf
  intro j _
  by_cases h : j = i
  · subst j
    simp [quittingStoppingTimeValue]
  · rw [Function.update_of_ne h]
    rw [← hfirst]
    exact Finset.inf_le (Finset.mem_univ j)

omit [Nonempty ι] in
/-- A remaining first-date quitter keeps the updated child's first date
exactly equal to the original deadline. -/
theorem quittingEarliestStoppingValue_update_none_eq_of_erase_nonempty
    (times : ι → Option ℕ) (time : ℕ) (i : ι)
    (hfirst : quittingEarliestStoppingValue times = (time : WithTop ℕ))
    (hrest : ((quittingEarliestStoppingCoalition times).erase i).Nonempty) :
    quittingEarliestStoppingValue (Function.update times i none) =
      (time : WithTop ℕ) := by
  apply le_antisymm
  · let j := hrest.choose
    have hj := (Finset.mem_erase.mp hrest.choose_spec)
    have hvalue : quittingStoppingTimeValue (times j) = (time : WithTop ℕ) := by
      simpa [j, quittingEarliestStoppingCoalition, hfirst] using hj.2
    have hle := Finset.inf_le
      (f := fun player => quittingStoppingTimeValue
        ((Function.update times i none) player)) (Finset.mem_univ j)
    rw [Function.update_of_ne hj.1, hvalue] at hle
    exact hle
  · exact quittingEarliestStoppingValue_update_none_ge times time i hfirst

/-- For a member of a nonsingleton first coalition, atom withdrawal has
exactly the same-date raw W gain. -/
theorem deadlineWithdrawalActualEvaluatedChildGain_nonsingleton_eq_floor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (times : ι → Option ℕ) (time : ℕ) (i : ι)
    (hfirst : quittingEarliestStoppingValue times = (time : WithTop ℕ))
    (hi : i ∈ quittingEarliestStoppingCoalition times)
    (hrest : ((quittingEarliestStoppingCoalition times).erase i).Nonempty) :
    deadlineWithdrawalActualEvaluatedChildGain reward evaluation times
        (some time) i =
      evaluation time * deadlineWithdrawalGainFloor reward i
        (quittingEarliestStoppingCoalition times)
        (quittingEarliestStoppingCoalition_nonempty times) := by
  let A := quittingEarliestStoppingCoalition times
  have hquiet := quittingFirstStoppingOutcome_quietParentClocks_of_first_eq
    times time hfirst
  have hnew := quittingFirstStoppingOutcome_withdrawn_of_tie_erase_nonempty
    times time i hfirst hi hrest
  have hclock : times i = some time := by
    have hvalue : quittingStoppingTimeValue (times i) = (time : WithTop ℕ) := by
      simpa [A, quittingEarliestStoppingCoalition, hfirst] using hi
    cases h : times i with
    | none => simp [h, quittingStoppingTimeValue] at hvalue
    | some t =>
        have ht : t = time := WithTop.coe_eq_coe.mp (by
          simpa [h, quittingStoppingTimeValue] using hvalue)
        simp [ht]
  have hnewFirst : quittingEarliestStoppingValue
      (withdrawnChildParentClocks times (some time) i) = (time : WithTop ℕ) := by
    rw [withdrawnChildParentClocks_eq_quiet_update_none times time i hclock,
      quittingEarliestStoppingValue_quietParentClocks]
    exact quittingEarliestStoppingValue_update_none_eq_of_erase_nonempty
      times time i hfirst hrest
  have hquietFirst := quittingEarliestStoppingValue_quietParentClocks times
  rw [deadlineWithdrawalActualEvaluatedChildGain]
  simp only [quittingPureClockEvaluatedPayoff, hquiet, hnew,
    hquietFirst, hnewFirst, hfirst]
  rw [deadlineWithdrawalGainFloor_of_erase_nonempty reward i A hi hrest]
  ring

/-- If the queried child was the sole first quitter at a deadline, its
withdrawn clock can expose only Never or a later opponent coalition. The
zero-or-passive floor is a valid evaluated lower bound in either case. -/
theorem deadlineWithdrawal_singleton_future_payoff_floor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (times : ι → Option ℕ) (time : ℕ) (i : ι)
    (hfirst : quittingEarliestStoppingValue times = (time : WithTop ℕ))
    (hclock : times i = some time) :
    evaluation time * deadlineWithdrawalZeroFloor reward i ≤
      quittingPureClockEvaluatedPayoff reward evaluation
        (withdrawnChildParentClocks times (some time) i) (some i) := by
  let updated := Function.update times i none
  have hwithdraw : withdrawnChildParentClocks times (some time) i =
      quietParentClocks updated :=
    withdrawnChildParentClocks_eq_quiet_update_none times time i hclock
  have hnot : updated i = none := by simp [updated]
  have hfuture := quittingEarliestStoppingValue_update_none_ge times time i hfirst
  rw [hwithdraw]
  induction hnew : quittingEarliestStoppingValue updated using WithTop.recTopCoe with
  | top =>
      have houtcome : quittingFirstStoppingOutcome (quietParentClocks updated) = none :=
        quittingFirstStoppingOutcome_quietParentClocks_of_first_eq_top updated hnew
      simp [quittingPureClockEvaluatedPayoff, houtcome]
      exact mul_nonpos_of_nonneg_of_nonpos
        (evaluation_nonneg _) (deadlineWithdrawalZeroFloor_le_zero reward i)
  | coe later =>
      have hnew' : quittingEarliestStoppingValue updated = (later : WithTop ℕ) := hnew
      have hlate : (time : WithTop ℕ) ≤ (later : WithTop ℕ) := by
        change (time : WithTop ℕ) ≤ quittingEarliestStoppingValue updated at hfuture
        rw [hnew] at hfuture
        exact hfuture
      let B := quittingEarliestStoppingCoalition updated
      have hB : B.Nonempty := quittingEarliestStoppingCoalition_nonempty updated
      have hi : i ∉ B := by
        intro hmem
        have heq : quittingStoppingTimeValue (updated i) = (later : WithTop ℕ) := by
          simpa [B, quittingEarliestStoppingCoalition, hnew] using hmem
        simp [hnot, quittingStoppingTimeValue] at heq
      have hfloor := deadlineWithdrawalZeroFloor_le_passiveReward reward i B hB hi
      have hnumerical := deadlineWithdrawal_laterEvaluatedFloor_le
        (evaluation time) (evaluation later) (deadlineWithdrawalZeroFloor reward i)
        (reward ⟨cappedClockChildCoalition B,
          cappedClockChildCoalition_nonempty hB⟩ (some i))
        (evaluation_nonneg _) (evaluation_nonneg _)
        (evaluation_antitone hlate)
        (deadlineWithdrawalZeroFloor_le_zero reward i) hfloor
      have houtcome := quittingFirstStoppingOutcome_quietParentClocks_of_first_eq
        updated later hnew'
      simpa [quittingPureClockEvaluatedPayoff, houtcome,
        quittingEarliestStoppingValue_quietParentClocks, B, hnew] using hnumerical

/-- At a singleton tie, the actual evaluated withdrawal gain is at least
the raw D-J singleton floor multiplied by that date's evaluation. -/
theorem deadlineWithdrawalActualEvaluatedChildGain_singleton_ge_floor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (times : ι → Option ℕ) (time : ℕ) (i : ι)
    (hfirst : quittingEarliestStoppingValue times = (time : WithTop ℕ))
    (hcoalition : quittingEarliestStoppingCoalition times = {i}) :
    evaluation time * deadlineWithdrawalGainFloor reward i {i}
        (Finset.singleton_nonempty i) ≤
      deadlineWithdrawalActualEvaluatedChildGain reward evaluation times
        (some time) i := by
  have hclock : times i = some time := by
    have hi : i ∈ quittingEarliestStoppingCoalition times := by
      rw [hcoalition]
      exact Finset.mem_singleton_self i
    have hvalue : quittingStoppingTimeValue (times i) = (time : WithTop ℕ) := by
      simpa [quittingEarliestStoppingCoalition, hfirst] using hi
    cases h : times i with
    | none => simp [h, quittingStoppingTimeValue] at hvalue
    | some t =>
        have ht : t = time := WithTop.coe_eq_coe.mp (by
          simpa [h, quittingStoppingTimeValue] using hvalue)
        simp [ht]
  have hfloor := deadlineWithdrawal_singleton_future_payoff_floor
    reward evaluation evaluation_nonneg evaluation_antitone times time i hfirst hclock
  have hsingle : cappedClockChildCoalition ({i} : Finset ι) = {some i} := by
    simp [cappedClockChildCoalition]
    rfl
  have hcurrent : quittingPureClockEvaluatedPayoff reward evaluation
      (quietParentClocks times) (some i) =
        evaluation time *
          reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) := by
    have houtcome := quittingFirstStoppingOutcome_quietParentClocks_of_first_eq
      times time hfirst
    simp [quittingPureClockEvaluatedPayoff, houtcome,
      quittingEarliestStoppingValue_quietParentClocks, hfirst, hcoalition, hsingle]
  rw [deadlineWithdrawalActualEvaluatedChildGain, hcurrent,
    deadlineWithdrawalGainFloor_singleton]
  nlinarith [hfloor]

/-- The exact withdrawal contribution needed in D-J, for every original
child player: zero outside the first coalition, exact W for nonsingleton
membership, and a lower bound by W for a singleton member. -/
theorem deadlineWithdrawalActualEvaluatedChildGain_tie_ge_floor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (times : ι → Option ℕ) (time : ℕ) (i : ι)
    (hfirst : quittingEarliestStoppingValue times = (time : WithTop ℕ)) :
    evaluation time * deadlineWithdrawalGainFloor reward i
        (quittingEarliestStoppingCoalition times)
        (quittingEarliestStoppingCoalition_nonempty times) ≤
      deadlineWithdrawalActualEvaluatedChildGain reward evaluation times
        (some time) i := by
  let A := quittingEarliestStoppingCoalition times
  by_cases hi : i ∈ A
  · by_cases hrest : (A.erase i).Nonempty
    · have heq := deadlineWithdrawalActualEvaluatedChildGain_nonsingleton_eq_floor
        reward evaluation times time i hfirst hi hrest
      exact heq.ge
    · have hempty : A.erase i = ∅ := Finset.not_nonempty_iff_eq_empty.mp hrest
      have hsingle : A = {i} := by
        rcases (Finset.erase_eq_empty_iff A i).mp hempty with hA | hA
        · exfalso
          simp [hA] at hi
        · exact hA
      simpa [A, hsingle] using
        (deadlineWithdrawalActualEvaluatedChildGain_singleton_ge_floor
          reward evaluation evaluation_nonneg evaluation_antitone
          times time i hfirst hsingle)
  · have hclock : times i ≠ some time := by
      intro hclock
      apply hi
      simp [A, quittingEarliestStoppingCoalition, hfirst, hclock,
        quittingStoppingTimeValue]
    rw [deadlineWithdrawalGainFloor_of_not_mem reward i A
      (quittingEarliestStoppingCoalition_nonempty times) hi]
    simp [deadlineWithdrawalActualEvaluatedChildGain_some_of_ne
      reward evaluation times time i hclock]

end GameTheory

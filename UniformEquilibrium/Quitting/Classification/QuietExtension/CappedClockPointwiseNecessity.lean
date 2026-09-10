import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockPointwiseDomination

/-! # Deterministic necessity of the capped-clock reward rows -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private def cappedClockCoalitionTimes
    (coalition : Finset ι) (time : ℕ) (who : ι) : Option ℕ :=
  if who ∈ coalition then some time else none

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
private theorem none_not_mem_cappedClockChildCoalition
    (coalition : Finset ι) : none ∉ cappedClockChildCoalition coalition := by
  intro h
  obtain ⟨who, _, hwho⟩ := Finset.mem_map.mp h
  cases hwho

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
private theorem some_mem_cappedClockChildCoalition_iff
    (coalition : Finset ι) (who : ι) :
    some who ∈ cappedClockChildCoalition coalition ↔ who ∈ coalition := by
  constructor
  · intro h
    obtain ⟨other, hother, heq⟩ := Finset.mem_map.mp h
    have : other = who := Option.some.inj heq
    simpa [this] using hother
  · intro h
    exact Finset.mem_map.mpr ⟨who, h, rfl⟩

private theorem quittingFirstStoppingOutcome_coalitionTimes
    (coalition : Finset ι) (hne : coalition.Nonempty) (time : ℕ) :
    quittingFirstStoppingOutcome (cappedClockCoalitionTimes coalition time) =
      some ⟨coalition, hne⟩ := by
  apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later (time := time)
  · intro who hwho
    simp [cappedClockCoalitionTimes, hwho]
  · intro who hwho
    simp [cappedClockCoalitionTimes, hwho, quittingStoppingTimeValue]

omit [Fintype ι] [Nonempty ι] in
private theorem quietParentClocks_coalitionTimes
    (coalition : Finset ι) (time : ℕ) :
    quietParentClocks (cappedClockCoalitionTimes coalition time) =
      cappedClockCoalitionTimes (cappedClockChildCoalition coalition) time := by
  funext player
  cases player with
  | none =>
      simp [quietParentClocks, cappedClockCoalitionTimes,
        none_not_mem_cappedClockChildCoalition]
  | some who =>
      simp [quietParentClocks, cappedClockCoalitionTimes,
        some_mem_cappedClockChildCoalition_iff]

private theorem outsideDeadlineClocks_futureWitness
    (coalition : Finset ι) :
    quittingFirstStoppingOutcome
        (outsideDeadlineClocks (cappedClockCoalitionTimes coalition 1) (some 0)) =
      some ⟨{none}, Finset.singleton_nonempty none⟩ := by
  apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later (time := 0)
  · intro player hplayer
    have : player = none := by simpa using hplayer
    subst player
    rfl
  · intro player hplayer
    cases player with
    | none => simp at hplayer
    | some who =>
        by_cases hwho : who ∈ coalition
        · simp [outsideDeadlineClocks, cappedClockCoalitionTimes, hwho,
            quittingStoppingTimeValue]
        · simp [outsideDeadlineClocks, cappedClockCoalitionTimes, hwho,
            quittingStoppingTimeValue]

private theorem cappedChildParentClocks_futureWitness
    (coalition : Finset ι) (who : ι) :
    quittingFirstStoppingOutcome
        (cappedChildParentClocks
          (cappedClockCoalitionTimes coalition 1) (some 0) who) =
      some ⟨{some who}, Finset.singleton_nonempty (some who)⟩ := by
  apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later (time := 0)
  · intro player hplayer
    simp only [Finset.mem_singleton] at hplayer
    subst player
    by_cases hwho : who ∈ coalition
    · simp [cappedChildParentClocks, cappedStoppingClock,
        cappedClockCoalitionTimes, hwho, quittingStoppingTimeValue]
    · simp [cappedChildParentClocks, cappedStoppingClock,
        cappedClockCoalitionTimes, hwho, quittingStoppingTimeValue]
  · intro player hplayer
    cases player with
    | none => simp [cappedChildParentClocks, quittingStoppingTimeValue]
    | some other =>
        have hne : other ≠ who := by
          intro h
          subst other
          exact hplayer (Finset.mem_singleton_self (some who))
        by_cases hother : other ∈ coalition
        · simp [cappedChildParentClocks, cappedClockCoalitionTimes, hne,
            hother, quittingStoppingTimeValue]
        · simp [cappedChildParentClocks, cappedClockCoalitionTimes, hne,
            hother, quittingStoppingTimeValue]

private theorem outsideDeadlineClocks_joinWitness
    (coalition : Finset ι) :
    quittingFirstStoppingOutcome
        (outsideDeadlineClocks (cappedClockCoalitionTimes coalition 0) (some 0)) =
      some ⟨cappedClockJoinedCoalition coalition,
        cappedClockJoinedCoalition_nonempty coalition⟩ := by
  apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later (time := 0)
  · intro player hplayer
    cases player with
    | none => rfl
    | some who =>
        have hwho : who ∈ coalition := by
          have : some who ∈ cappedClockChildCoalition coalition := by
            simpa [cappedClockJoinedCoalition] using hplayer
          exact (some_mem_cappedClockChildCoalition_iff coalition who).mp this
        simp [outsideDeadlineClocks, cappedClockCoalitionTimes, hwho]
  · intro player hplayer
    cases player with
    | none => exact (hplayer (Finset.mem_insert_self none _)).elim
    | some who =>
        have hwho : who ∉ coalition := by
          intro h
          apply hplayer
          apply Finset.mem_insert_of_mem
          exact (some_mem_cappedClockChildCoalition_iff coalition who).mpr h
        simp [outsideDeadlineClocks, cappedClockCoalitionTimes, hwho,
          quittingStoppingTimeValue]

private theorem cappedChildParentClocks_joinWitness
    (coalition : Finset ι) (who : ι) :
    quittingFirstStoppingOutcome
        (cappedChildParentClocks
          (cappedClockCoalitionTimes coalition 0) (some 0) who) =
      some ⟨cappedClockChildCoalition (insert who coalition),
        cappedClockChildCoalition_nonempty (Finset.insert_nonempty who coalition)⟩ := by
  apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later (time := 0)
  · intro player hplayer
    cases player with
    | none =>
        exact (none_not_mem_cappedClockChildCoalition
          (insert who coalition) hplayer).elim
    | some other =>
      have hother : other ∈ insert who coalition :=
        (some_mem_cappedClockChildCoalition_iff
          (insert who coalition) other).mp hplayer
      rcases Finset.mem_insert.mp hother with hother | hother
      · subst other
        by_cases hwho : who ∈ coalition
        · simp [cappedChildParentClocks, cappedStoppingClock,
            cappedClockCoalitionTimes, hwho, quittingStoppingTimeValue]
        · simp [cappedChildParentClocks, cappedStoppingClock,
            cappedClockCoalitionTimes, hwho, quittingStoppingTimeValue]
      · by_cases heq : other = who
        · subst other
          simp [cappedChildParentClocks, cappedStoppingClock,
            cappedClockCoalitionTimes, hother, quittingStoppingTimeValue]
        · simp [cappedChildParentClocks, cappedClockCoalitionTimes, heq, hother]
  · intro player hplayer
    cases player with
    | none => simp [cappedChildParentClocks, quittingStoppingTimeValue]
    | some other =>
        have hneWho : other ≠ who := by
          intro h
          subst other
          apply hplayer
          exact (some_mem_cappedClockChildCoalition_iff
            (insert who coalition) who).mpr (Finset.mem_insert_self who coalition)
        have hnotMem : other ∉ coalition := by
          intro h
          apply hplayer
          exact (some_mem_cappedClockChildCoalition_iff
            (insert who coalition) other).mpr (Finset.mem_insert_of_mem h)
        simp [cappedChildParentClocks, cappedClockCoalitionTimes, hneWho,
          hnotMem, quittingStoppingTimeValue]

/-- The deterministic child tuple in which every child chooses Never. -/
def cappedClockAllNeverTimes (_ : ι) : Option ℕ := none

/-- The deterministic future-row tuple: precisely `coalition` stops at date
one, after the outsider's test deadline at date zero. -/
def cappedClockFutureTimes (coalition : Finset ι) (who : ι) : Option ℕ :=
  if who ∈ coalition then some 1 else none

/-- The deterministic joining-row tuple: precisely `coalition` stops at date
zero, tied with the outsider's test deadline. -/
def cappedClockJoiningTimes (coalition : Finset ι) (who : ι) : Option ℕ :=
  if who ∈ coalition then some 0 else none

/-- Universal deterministic terminal gain domination reconstructs the exact
Never, future, and joining rows with the same supplied weights. -/
def cappedClockParentRewardCertificateOfActualGainLe
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (weight : ι → ℝ) (weight_nonneg : ∀ who, 0 ≤ weight who)
    (hdom : ∀ times deadline,
      cappedClockActualOutsideGain reward times deadline ≤
        ∑ who, weight who *
          cappedClockActualChildGain reward times deadline who) :
    CappedClockParentRewardCertificate reward where
  weight := weight
  weight_nonneg := weight_nonneg
  never_row := by
    have h := hdom (cappedClockAllNeverTimes : ι → Option ℕ) (some 0)
    have hquiet : quietParentClocks (cappedClockAllNeverTimes : ι → Option ℕ) =
        fun _ : Option ι => none := by
      funext player
      cases player <;> rfl
    have houtside : quittingFirstStoppingOutcome
          (outsideDeadlineClocks (cappedClockAllNeverTimes : ι → Option ℕ)
            (some 0)) =
        some ⟨{none}, Finset.singleton_nonempty none⟩ := by
      have hall : cappedClockCoalitionTimes (∅ : Finset ι) 1 =
          (cappedClockAllNeverTimes : ι → Option ℕ) := by
        funext who
        simp [cappedClockCoalitionTimes, cappedClockAllNeverTimes]
      rw [← hall]
      exact outsideDeadlineClocks_futureWitness (∅ : Finset ι)
    have hchild (who : ι) : quittingFirstStoppingOutcome
          (cappedChildParentClocks (cappedClockAllNeverTimes : ι → Option ℕ)
            (some 0) who) =
        some ⟨{some who}, Finset.singleton_nonempty (some who)⟩ := by
      have hall : cappedClockCoalitionTimes (∅ : Finset ι) 1 =
          (cappedClockAllNeverTimes : ι → Option ℕ) := by
        funext child
        simp [cappedClockCoalitionTimes, cappedClockAllNeverTimes]
      rw [← hall]
      exact cappedChildParentClocks_futureWitness (∅ : Finset ι) who
    simp only [cappedClockActualOutsideGain, cappedClockActualChildGain] at h
    rw [hquiet] at h
    unfold quittingPureClockTerminalPayoff at h
    rw [quittingFirstStoppingOutcome_all_never, houtside] at h
    simp_rw [hchild] at h
    simpa [quittingPureClockTerminalPayoff] using h
  future_row := by
    intro coalition hne
    have h := hdom (cappedClockFutureTimes coalition) (some 0)
    have hquiet := quietParentClocks_coalitionTimes coalition 1
    have hquietOutcome := quittingFirstStoppingOutcome_coalitionTimes
      (cappedClockChildCoalition coalition)
      (cappedClockChildCoalition_nonempty hne) 1
    have houtside := outsideDeadlineClocks_futureWitness coalition
    have hchild (who : ι) :=
      cappedChildParentClocks_futureWitness coalition who
    have htimes : cappedClockFutureTimes coalition =
        cappedClockCoalitionTimes coalition 1 := by
      rfl
    rw [htimes] at h
    simp only [cappedClockActualOutsideGain, cappedClockActualChildGain] at h
    rw [hquiet] at h
    unfold quittingPureClockTerminalPayoff at h
    rw [hquietOutcome, houtside] at h
    simp_rw [hchild] at h
    simpa [quittingPureClockTerminalPayoff] using h
  join_row := by
    intro coalition hne
    have h := hdom (cappedClockJoiningTimes coalition) (some 0)
    have hquiet := quietParentClocks_coalitionTimes coalition 0
    have hquietOutcome := quittingFirstStoppingOutcome_coalitionTimes
      (cappedClockChildCoalition coalition)
      (cappedClockChildCoalition_nonempty hne) 0
    have houtside := outsideDeadlineClocks_joinWitness coalition
    have hchild (who : ι) :=
      cappedChildParentClocks_joinWitness coalition who
    have htimes : cappedClockJoiningTimes coalition =
        cappedClockCoalitionTimes coalition 0 := by
      rfl
    rw [htimes] at h
    simp only [cappedClockActualOutsideGain, cappedClockActualChildGain] at h
    rw [hquiet] at h
    unfold quittingPureClockTerminalPayoff at h
    rw [hquietOutcome, houtside] at h
    simp_rw [hchild] at h
    simpa [quittingPureClockTerminalPayoff] using h

/-- Exact capped-clock rows are equivalent to universal deterministic
terminal gain domination for fixed nonnegative weights. -/
theorem cappedClockActualGain_le_iff_rewardRows
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (weight : ι → ℝ) (weight_nonneg : ∀ who, 0 ≤ weight who) :
    (∀ times deadline,
      cappedClockActualOutsideGain reward times deadline ≤
        ∑ who, weight who *
          cappedClockActualChildGain reward times deadline who) ↔
      (reward ⟨{none}, Finset.singleton_nonempty none⟩ none ≤
        ∑ who, weight who *
          reward ⟨{some who}, Finset.singleton_nonempty (some who)⟩ (some who)) ∧
      (∀ coalition (hne : coalition.Nonempty),
        reward ⟨{none}, Finset.singleton_nonempty none⟩ none -
            reward ⟨cappedClockChildCoalition coalition,
              cappedClockChildCoalition_nonempty hne⟩ none ≤
          ∑ who, weight who *
            (reward ⟨{some who}, Finset.singleton_nonempty (some who)⟩
                (some who) -
              reward ⟨cappedClockChildCoalition coalition,
                cappedClockChildCoalition_nonempty hne⟩ (some who))) ∧
      ∀ coalition (hne : coalition.Nonempty),
        reward ⟨cappedClockJoinedCoalition coalition,
              cappedClockJoinedCoalition_nonempty coalition⟩ none -
            reward ⟨cappedClockChildCoalition coalition,
              cappedClockChildCoalition_nonempty hne⟩ none ≤
          ∑ who, weight who *
            (reward ⟨cappedClockChildCoalition (insert who coalition),
                cappedClockChildCoalition_nonempty
                  (Finset.insert_nonempty who coalition)⟩ (some who) -
              reward ⟨cappedClockChildCoalition coalition,
                cappedClockChildCoalition_nonempty hne⟩ (some who)) := by
  constructor
  · intro hdom
    let certificate := cappedClockParentRewardCertificateOfActualGainLe
      reward weight weight_nonneg hdom
    exact ⟨certificate.never_row, certificate.future_row, certificate.join_row⟩
  · rintro ⟨hnever, hfuture, hjoin⟩
    let certificate : CappedClockParentRewardCertificate reward :=
      { weight := weight
        weight_nonneg := weight_nonneg
        never_row := hnever
        future_row := hfuture
        join_row := hjoin }
    intro times deadline
    exact cappedClockActualOutsideGain_le_weighted_actualChildGain
      reward certificate times deadline

end GameTheory

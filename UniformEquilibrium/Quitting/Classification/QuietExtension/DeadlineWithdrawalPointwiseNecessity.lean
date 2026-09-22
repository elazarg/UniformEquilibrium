import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalFamilyDebtBounds
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockPointwiseNecessity

/-!
# Raw-row necessity from deterministic deadline witnesses

The packet's converse tests the universal terminal pathwise comparison on
specific deterministic tuples. The joint-Never witness below reconstructs
the literal D-N row without assuming any favorable strategy.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Universal terminal advance-plus-withdrawal domination forces D-N:
all children use Never and the outsider tests deadline zero. -/
theorem deadlineWithdrawal_neverRow_of_terminalPointwise
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (advanceWeight withdrawalWeight : ι → ℝ)
    (hdom : ∀ times deadline,
      cappedClockActualEvaluatedOutsideGain reward quittingTerminalEvaluation
          times deadline ≤
        ∑ i, (advanceWeight i *
            cappedClockActualEvaluatedChildGain reward quittingTerminalEvaluation
              times deadline i +
          withdrawalWeight i *
            deadlineWithdrawalActualEvaluatedChildGain reward
              quittingTerminalEvaluation times deadline i)) :
    reward ⟨{none}, Finset.singleton_nonempty none⟩ none ≤
      ∑ i, advanceWeight i *
        reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) := by
  let times : ι → Option ℕ := cappedClockAllNeverTimes
  have h := hdom times (some 0)
  have hquiet : quietParentClocks times = fun _ : Option ι => none := by
    funext player
    cases player <;> rfl
  have houtside : quittingFirstStoppingOutcome
      (outsideDeadlineClocks times (some 0)) =
      some ⟨{none}, Finset.singleton_nonempty none⟩ := by
    apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later
      (time := 0)
    · intro player hplayer
      have hp : player = none := by simpa using hplayer
      subst player
      rfl
    · intro player hplayer
      cases player with
      | none => simp at hplayer
      | some i =>
          simp [outsideDeadlineClocks, times, cappedClockAllNeverTimes,
            quittingStoppingTimeValue]
  have hchild (i : ι) : quittingFirstStoppingOutcome
      (cappedChildParentClocks times (some 0) i) =
      some ⟨{some i}, Finset.singleton_nonempty (some i)⟩ := by
    apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later
      (time := 0)
    · intro player hplayer
      have hp : player = some i := by simpa using hplayer
      subst player
      simp [cappedChildParentClocks, cappedStoppingClock,
        times, cappedClockAllNeverTimes, quittingStoppingTimeValue]
    · intro player hplayer
      cases player with
      | none => simp [cappedChildParentClocks, quittingStoppingTimeValue]
      | some j =>
          have hne : j ≠ i := by
            intro heq
            subst j
            exact hplayer (Finset.mem_singleton_self (some i))
          simp [cappedChildParentClocks, times, cappedClockAllNeverTimes,
            hne, quittingStoppingTimeValue]
  have hwithdraw (i : ι) :
      deadlineWithdrawalActualEvaluatedChildGain reward
        quittingTerminalEvaluation times (some 0) i = 0 := by
    apply deadlineWithdrawalActualEvaluatedChildGain_some_of_ne
    simp [times, cappedClockAllNeverTimes]
  simp only [cappedClockActualEvaluatedOutsideGain,
    cappedClockActualEvaluatedChildGain] at h
  simp_rw [hwithdraw] at h
  rw [hquiet] at h
  unfold quittingPureClockEvaluatedPayoff at h
  rw [quittingFirstStoppingOutcome_all_never, houtside] at h
  simp_rw [hchild] at h
  have houtsideFinite :
      quittingEarliestStoppingValue (outsideDeadlineClocks times (some 0)) ≠
        ⊤ := by
    intro htop
    rw [quittingFirstStoppingOutcome, ite_eq_left htop] at houtside
    contradiction
  have hchildFinite (i : ι) :
      quittingEarliestStoppingValue
        (cappedChildParentClocks times (some 0) i) ≠ ⊤ := by
    intro htop
    have hci := hchild i
    rw [quittingFirstStoppingOutcome, ite_eq_left htop] at hci
    contradiction
  simp only [quittingTerminalEvaluation, houtsideFinite,
    hchildFinite, ↓reduceIte, one_mul, sub_zero] at h
  simpa using h

omit [Nonempty ι] in
/-- The public future-row witness has first child date one and precisely the
specified first coalition. -/
private theorem deadlineWithdrawal_futureWitness_first
    (A : Finset ι) (hA : A.Nonempty) :
    quittingEarliestStoppingValue (cappedClockFutureTimes A) =
      (1 : WithTop ℕ) := by
  apply le_antisymm
  · obtain ⟨i, hi⟩ := hA
    have hle := Finset.inf_le (f := fun j =>
      quittingStoppingTimeValue (cappedClockFutureTimes A j))
      (Finset.mem_univ i)
    simpa [quittingEarliestStoppingValue, cappedClockFutureTimes, hi,
      quittingStoppingTimeValue] using hle
  · unfold quittingEarliestStoppingValue
    apply Finset.le_inf
    intro i _
    by_cases hi : i ∈ A <;>
      simp [cappedClockFutureTimes, hi, quittingStoppingTimeValue]

omit [Nonempty ι] in
private theorem deadlineWithdrawal_futureWitness_coalition
    (A : Finset ι) (hA : A.Nonempty) :
    quittingEarliestStoppingCoalition (cappedClockFutureTimes A) = A := by
  ext i
  by_cases hi : i ∈ A
  · simp [quittingEarliestStoppingCoalition,
      deadlineWithdrawal_futureWitness_first A hA,
      cappedClockFutureTimes, quittingStoppingTimeValue, hi]
  · simp [quittingEarliestStoppingCoalition,
      deadlineWithdrawal_futureWitness_first A hA,
      cappedClockFutureTimes, quittingStoppingTimeValue, hi]

/-- Universal terminal pathwise comparison forces D-F for every nonempty
child coalition: at date zero the outsider precedes its date-one stop. -/
theorem deadlineWithdrawal_futureRow_of_terminalPointwise
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (advanceWeight withdrawalWeight : ι → ℝ)
    (hdom : ∀ times deadline,
      cappedClockActualEvaluatedOutsideGain reward quittingTerminalEvaluation
          times deadline ≤
        ∑ i, (advanceWeight i *
            cappedClockActualEvaluatedChildGain reward quittingTerminalEvaluation
              times deadline i +
          withdrawalWeight i *
            deadlineWithdrawalActualEvaluatedChildGain reward
              quittingTerminalEvaluation times deadline i))
    (A : Finset ι) (hA : A.Nonempty) :
    reward ⟨{none}, Finset.singleton_nonempty none⟩ none -
        reward ⟨cappedClockChildCoalition A,
          cappedClockChildCoalition_nonempty hA⟩ none ≤
      ∑ i, advanceWeight i *
        (reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) -
          reward ⟨cappedClockChildCoalition A,
            cappedClockChildCoalition_nonempty hA⟩ (some i)) := by
  let times := cappedClockFutureTimes A
  have h := hdom times (some 0)
  have hfirst := deadlineWithdrawal_futureWitness_first A hA
  have hcoalition := deadlineWithdrawal_futureWitness_coalition A hA
  have hquiet : quittingFirstStoppingOutcome (quietParentClocks times) =
      some ⟨cappedClockChildCoalition A,
        cappedClockChildCoalition_nonempty hA⟩ := by
    have hsubtype :
        (⟨cappedClockChildCoalition (quittingEarliestStoppingCoalition times),
          cappedClockChildCoalition_nonempty
            (quittingEarliestStoppingCoalition_nonempty times)⟩ :
            {S : Finset (Option ι) // S.Nonempty}) =
          ⟨cappedClockChildCoalition A,
            cappedClockChildCoalition_nonempty hA⟩ := by
      apply Subtype.ext
      exact congrArg cappedClockChildCoalition hcoalition
    exact (quittingFirstStoppingOutcome_quietParentClocks_of_first_eq
      times 1 hfirst).trans (congrArg Option.some hsubtype)
  have hbefore : (0 : WithTop ℕ) < quittingEarliestStoppingValue times := by
    rw [hfirst]
    norm_num
  have houtside := quittingFirstStoppingOutcome_outsideDeadlineClocks_of_lt_first
    times 0 hbefore
  have hchild (i : ι) :=
    quittingFirstStoppingOutcome_cappedChildParentClocks_of_lt_first
      times 0 i hbefore
  have hwithdraw (i : ι) :
      deadlineWithdrawalActualEvaluatedChildGain reward
        quittingTerminalEvaluation times (some 0) i = 0 := by
    apply deadlineWithdrawalActualEvaluatedChildGain_some_of_ne
    simp [times, cappedClockFutureTimes]
  simp only [cappedClockActualEvaluatedOutsideGain,
    cappedClockActualEvaluatedChildGain] at h
  simp_rw [hwithdraw] at h
  simp_rw [quittingPureClockEvaluatedPayoff_terminalEvaluation] at h
  unfold quittingPureClockTerminalPayoff at h
  rw [hquiet, houtside] at h
  simp_rw [hchild] at h
  simpa [quittingPureClockTerminalPayoff] using h

omit [Nonempty ι] in
private theorem deadlineWithdrawal_joinWitness_first
    (A : Finset ι) (hA : A.Nonempty) :
    quittingEarliestStoppingValue (cappedClockJoiningTimes A) =
      (0 : WithTop ℕ) := by
  apply le_antisymm
  · obtain ⟨i, hi⟩ := hA
    have hle := Finset.inf_le (f := fun j =>
      quittingStoppingTimeValue (cappedClockJoiningTimes A j))
      (Finset.mem_univ i)
    simpa [quittingEarliestStoppingValue, cappedClockJoiningTimes, hi,
      quittingStoppingTimeValue] using hle
  · unfold quittingEarliestStoppingValue
    apply Finset.le_inf
    intro i _
    by_cases hi : i ∈ A <;>
      simp [cappedClockJoiningTimes, hi, quittingStoppingTimeValue]

omit [Nonempty ι] in
private theorem deadlineWithdrawal_joinWitness_coalition
    (A : Finset ι) (hA : A.Nonempty) :
    quittingEarliestStoppingCoalition (cappedClockJoiningTimes A) = A := by
  ext i
  by_cases hi : i ∈ A
  · simp [quittingEarliestStoppingCoalition,
      deadlineWithdrawal_joinWitness_first A hA,
      cappedClockJoiningTimes, quittingStoppingTimeValue, hi]
  · simp [quittingEarliestStoppingCoalition,
      deadlineWithdrawal_joinWitness_first A hA,
      cappedClockJoiningTimes, quittingStoppingTimeValue, hi]

/-- D-J is forced on every nonsingleton first coalition by the date-zero
joining witness: every withdrawal gain equals its raw erased-coalition row. -/
theorem deadlineWithdrawal_joinRow_of_terminalPointwise_of_erase_nonempty
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (advanceWeight withdrawalWeight : ι → ℝ)
    (hdom : ∀ times deadline,
      cappedClockActualEvaluatedOutsideGain reward quittingTerminalEvaluation
          times deadline ≤
        ∑ i, (advanceWeight i *
            cappedClockActualEvaluatedChildGain reward quittingTerminalEvaluation
              times deadline i +
          withdrawalWeight i *
            deadlineWithdrawalActualEvaluatedChildGain reward
              quittingTerminalEvaluation times deadline i))
    (A : Finset ι) (hA : A.Nonempty)
    (herase : ∀ i ∈ A, (A.erase i).Nonempty) :
    reward ⟨cappedClockJoinedCoalition A,
          cappedClockJoinedCoalition_nonempty A⟩ none -
        reward ⟨cappedClockChildCoalition A,
          cappedClockChildCoalition_nonempty hA⟩ none ≤
      ∑ i, (advanceWeight i *
          (reward ⟨cappedClockChildCoalition (insert i A),
              cappedClockChildCoalition_nonempty (Finset.insert_nonempty i A)⟩
              (some i) -
            reward ⟨cappedClockChildCoalition A,
              cappedClockChildCoalition_nonempty hA⟩ (some i)) +
        withdrawalWeight i * deadlineWithdrawalGainFloor reward i A hA) := by
  let times := cappedClockJoiningTimes A
  have h := hdom times (some 0)
  have hfirst := deadlineWithdrawal_joinWitness_first A hA
  have hcoalition := deadlineWithdrawal_joinWitness_coalition A hA
  have hquiet : quittingFirstStoppingOutcome (quietParentClocks times) =
      some ⟨cappedClockChildCoalition A,
        cappedClockChildCoalition_nonempty hA⟩ := by
    have hsubtype :
        (⟨cappedClockChildCoalition (quittingEarliestStoppingCoalition times),
          cappedClockChildCoalition_nonempty
            (quittingEarliestStoppingCoalition_nonempty times)⟩ :
            {S : Finset (Option ι) // S.Nonempty}) =
          ⟨cappedClockChildCoalition A,
            cappedClockChildCoalition_nonempty hA⟩ := by
      apply Subtype.ext
      exact congrArg cappedClockChildCoalition hcoalition
    exact (quittingFirstStoppingOutcome_quietParentClocks_of_first_eq
      times 0 hfirst).trans (congrArg Option.some hsubtype)
  have houtside :
      quittingFirstStoppingOutcome (outsideDeadlineClocks times (some 0)) =
        some ⟨cappedClockJoinedCoalition A,
          cappedClockJoinedCoalition_nonempty A⟩ := by
    have hsubtype :
        (⟨cappedClockJoinedCoalition (quittingEarliestStoppingCoalition times),
          cappedClockJoinedCoalition_nonempty _⟩ :
            {S : Finset (Option ι) // S.Nonempty}) =
          ⟨cappedClockJoinedCoalition A,
            cappedClockJoinedCoalition_nonempty A⟩ := by
      apply Subtype.ext
      exact congrArg cappedClockJoinedCoalition hcoalition
    exact (quittingFirstStoppingOutcome_outsideDeadlineClocks_of_eq_first
      times 0 hfirst).trans (congrArg Option.some hsubtype)
  have hchild (i : ι) :
      quittingFirstStoppingOutcome (cappedChildParentClocks times (some 0) i) =
        some ⟨cappedClockChildCoalition (insert i A),
          cappedClockChildCoalition_nonempty (Finset.insert_nonempty i A)⟩ := by
    have hsubtype :
        (⟨cappedClockChildCoalition
            (insert i (quittingEarliestStoppingCoalition times)),
          cappedClockChildCoalition_nonempty (Finset.insert_nonempty _ _)⟩ :
            {S : Finset (Option ι) // S.Nonempty}) =
          ⟨cappedClockChildCoalition (insert i A),
            cappedClockChildCoalition_nonempty
              (Finset.insert_nonempty i A)⟩ := by
      apply Subtype.ext
      exact congrArg (fun S => cappedClockChildCoalition (insert i S)) hcoalition
    exact (quittingFirstStoppingOutcome_cappedChildParentClocks_of_eq_first
      times 0 i hfirst).trans (congrArg Option.some hsubtype)
  have hwithdraw (i : ι) :
      deadlineWithdrawalActualEvaluatedChildGain reward
          quittingTerminalEvaluation times (some 0) i =
        deadlineWithdrawalGainFloor reward i A hA := by
    by_cases hi : i ∈ A
    · have hi' : i ∈ quittingEarliestStoppingCoalition times := by
        rw [hcoalition]
        exact hi
      have hrest' :
          ((quittingEarliestStoppingCoalition times).erase i).Nonempty := by
        rw [hcoalition]
        exact herase i hi
      have hraw := deadlineWithdrawalActualEvaluatedChildGain_nonsingleton_eq_floor
        reward quittingTerminalEvaluation times 0 i hfirst hi' hrest'
      have hsubtype :
          (⟨quittingEarliestStoppingCoalition times,
            quittingEarliestStoppingCoalition_nonempty times⟩ :
              {S : Finset ι // S.Nonempty}) = ⟨A, hA⟩ :=
        Subtype.ext hcoalition
      have hfloorEq := congrArg
        (fun S : {S : Finset ι // S.Nonempty} =>
          deadlineWithdrawalGainFloor reward i S.1 S.2) hsubtype
      simp [quittingTerminalEvaluation] at hraw
      rw [hfloorEq] at hraw
      exact hraw
    · have hclock : times i ≠ some 0 := by
        simp [times, cappedClockJoiningTimes, hi]
      rw [deadlineWithdrawalActualEvaluatedChildGain_some_of_ne
        reward quittingTerminalEvaluation times 0 i hclock]
      exact (deadlineWithdrawalGainFloor_of_not_mem reward i A hA hi).symm
  simp only [cappedClockActualEvaluatedOutsideGain,
    cappedClockActualEvaluatedChildGain] at h
  simp_rw [hwithdraw] at h
  simp_rw [quittingPureClockEvaluatedPayoff_terminalEvaluation] at h
  unfold quittingPureClockTerminalPayoff at h
  rw [hquiet, houtside] at h
  simp_rw [hchild] at h
  simpa [quittingPureClockTerminalPayoff] using h

omit [Nonempty ι] in
/-- The finite zero-or-passive floor has an attained witness: either Never
gives zero, or a nonempty later coalition excluding the queried child gives
exactly its reward. -/
private theorem deadlineWithdrawalZeroFloor_attained
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) :
    deadlineWithdrawalZeroFloor reward i = 0 ∨
      ∃ (B : Finset ι) (hB : B.Nonempty), i ∉ B ∧
        deadlineWithdrawalZeroFloor reward i =
          reward ⟨cappedClockChildCoalition B,
            cappedClockChildCoalition_nonempty hB⟩ (some i) := by
  classical
  let passive : Finset ℝ :=
    Finset.univ.image fun B : {A : Finset ι // A.Nonempty ∧ i ∉ A} =>
      reward ⟨cappedClockChildCoalition B.1,
        cappedClockChildCoalition_nonempty B.2.1⟩ (some i)
  have hfloor : deadlineWithdrawalZeroFloor reward i =
      (insert 0 passive).min' (Finset.insert_nonempty 0 passive) := rfl
  have hmem := Finset.min'_mem (insert 0 passive)
    (Finset.insert_nonempty 0 passive)
  rcases Finset.mem_insert.mp hmem with hzero | hpassive
  · exact Or.inl (hfloor.trans hzero)
  · obtain ⟨B, _, hvalue⟩ := Finset.mem_image.mp hpassive
    exact Or.inr ⟨B.1, B.2.1, B.2.2, hfloor.trans hvalue.symm⟩

/-- A singleton first quitter at date zero with a possible later passive
coalition at date one. -/
private def deadlineWithdrawalSingletonTimes
    (i : ι) (B : Finset ι) (j : ι) : Option ℕ :=
  if j = i then some 0 else if j ∈ B then some 1 else none

omit [Nonempty ι] in
private theorem deadlineWithdrawal_singletonWitness_first
    (i : ι) (B : Finset ι) :
    quittingEarliestStoppingValue (deadlineWithdrawalSingletonTimes i B) =
      (0 : WithTop ℕ) := by
  apply le_antisymm
  · have hle := Finset.inf_le (f := fun j =>
      quittingStoppingTimeValue (deadlineWithdrawalSingletonTimes i B j))
      (Finset.mem_univ i)
    simpa [quittingEarliestStoppingValue,
      deadlineWithdrawalSingletonTimes, quittingStoppingTimeValue] using hle
  · unfold quittingEarliestStoppingValue
    apply Finset.le_inf
    intro j _
    by_cases hj : j = i <;>
      simp [deadlineWithdrawalSingletonTimes, hj, quittingStoppingTimeValue]

omit [Nonempty ι] in
private theorem deadlineWithdrawal_singletonWitness_coalition
    (i : ι) (B : Finset ι) :
    quittingEarliestStoppingCoalition
        (deadlineWithdrawalSingletonTimes i B) = {i} := by
  ext j
  by_cases hj : j = i
  · subst j
    simp [quittingEarliestStoppingCoalition,
      deadlineWithdrawal_singletonWitness_first,
      deadlineWithdrawalSingletonTimes, quittingStoppingTimeValue]
  · by_cases hB : j ∈ B <;>
      simp [quittingEarliestStoppingCoalition,
        deadlineWithdrawal_singletonWitness_first,
        deadlineWithdrawalSingletonTimes, quittingStoppingTimeValue, hj, hB]

omit [Fintype ι] [Nonempty ι] in
private theorem deadlineWithdrawal_singletonWitness_update
    (i : ι) (B : Finset ι) (hiB : i ∉ B) :
    Function.update (deadlineWithdrawalSingletonTimes i B) i none =
      cappedClockFutureTimes B := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [cappedClockFutureTimes, hiB]
  · simp [deadlineWithdrawalSingletonTimes, cappedClockFutureTimes, hj]

private theorem deadlineWithdrawal_singletonWitness_withdrawn_of_nonempty
    (i : ι) (B : Finset ι) (hB : B.Nonempty) (hiB : i ∉ B) :
    quittingFirstStoppingOutcome
        (withdrawnChildParentClocks
          (deadlineWithdrawalSingletonTimes i B) (some 0) i) =
      some ⟨cappedClockChildCoalition B,
        cappedClockChildCoalition_nonempty hB⟩ := by
  have hclock : deadlineWithdrawalSingletonTimes i B i = some 0 := by
    simp [deadlineWithdrawalSingletonTimes]
  rw [withdrawnChildParentClocks_eq_quiet_update_none
      (deadlineWithdrawalSingletonTimes i B) 0 i hclock,
    deadlineWithdrawal_singletonWitness_update i B hiB]
  have hfirst := deadlineWithdrawal_futureWitness_first B hB
  have hcoalition := deadlineWithdrawal_futureWitness_coalition B hB
  have hsubtype :
      (⟨cappedClockChildCoalition
          (quittingEarliestStoppingCoalition (cappedClockFutureTimes B)),
        cappedClockChildCoalition_nonempty
          (quittingEarliestStoppingCoalition_nonempty
            (cappedClockFutureTimes B))⟩ :
          {S : Finset (Option ι) // S.Nonempty}) =
        ⟨cappedClockChildCoalition B,
          cappedClockChildCoalition_nonempty hB⟩ := by
    apply Subtype.ext
    exact congrArg cappedClockChildCoalition hcoalition
  exact (quittingFirstStoppingOutcome_quietParentClocks_of_first_eq
    (cappedClockFutureTimes B) 1 hfirst).trans (congrArg Option.some hsubtype)

private theorem deadlineWithdrawal_singletonWitness_withdrawn_of_empty
    (i : ι) :
    quittingFirstStoppingOutcome
        (withdrawnChildParentClocks
          (deadlineWithdrawalSingletonTimes i ∅) (some 0) i) = none := by
  have hclock : deadlineWithdrawalSingletonTimes i ∅ i = some 0 := by
    simp [deadlineWithdrawalSingletonTimes]
  rw [withdrawnChildParentClocks_eq_quiet_update_none
      (deadlineWithdrawalSingletonTimes i ∅) 0 i hclock,
    deadlineWithdrawal_singletonWitness_update i ∅ (by simp)]
  have hall : quietParentClocks (cappedClockFutureTimes (∅ : Finset ι)) =
      fun _ : Option ι => none := by
    funext player
    cases player <;>
      simp [quietParentClocks, cappedClockFutureTimes]
  rw [hall]
  exact quittingFirstStoppingOutcome_all_never

/-- The floor-attaining later coalition makes the singleton withdrawal gain
equal, not merely bounded below by, the raw D-J singleton floor. -/
theorem deadlineWithdrawal_joinRow_singleton_of_terminalPointwise
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (advanceWeight withdrawalWeight : ι → ℝ)
    (hdom : ∀ times deadline,
      cappedClockActualEvaluatedOutsideGain reward quittingTerminalEvaluation
          times deadline ≤
        ∑ j, (advanceWeight j *
            cappedClockActualEvaluatedChildGain reward quittingTerminalEvaluation
              times deadline j +
          withdrawalWeight j *
            deadlineWithdrawalActualEvaluatedChildGain reward
              quittingTerminalEvaluation times deadline j))
    (i : ι) :
    reward ⟨cappedClockJoinedCoalition {i},
          cappedClockJoinedCoalition_nonempty {i}⟩ none -
        reward ⟨cappedClockChildCoalition {i},
          cappedClockChildCoalition_nonempty (Finset.singleton_nonempty i)⟩ none ≤
      ∑ j, (advanceWeight j *
          (reward ⟨cappedClockChildCoalition (insert j {i}),
              cappedClockChildCoalition_nonempty (Finset.insert_nonempty j {i})⟩
              (some j) -
            reward ⟨cappedClockChildCoalition {i},
              cappedClockChildCoalition_nonempty (Finset.singleton_nonempty i)⟩
              (some j)) +
        withdrawalWeight j * deadlineWithdrawalGainFloor reward j {i}
          (Finset.singleton_nonempty i)) := by
  obtain ⟨B, hiB, hafter⟩ : ∃ B : Finset ι, i ∉ B ∧
      quittingPureClockTerminalPayoff reward
          (withdrawnChildParentClocks
            (deadlineWithdrawalSingletonTimes i B) (some 0) i) (some i) =
        deadlineWithdrawalZeroFloor reward i := by
    rcases deadlineWithdrawalZeroFloor_attained reward i with hzero |
      ⟨B, hB, hiB, hfloor⟩
    · refine ⟨∅, by simp, ?_⟩
      simp [quittingPureClockTerminalPayoff,
        deadlineWithdrawal_singletonWitness_withdrawn_of_empty i, hzero]
    · refine ⟨B, hiB, ?_⟩
      simp [quittingPureClockTerminalPayoff,
        deadlineWithdrawal_singletonWitness_withdrawn_of_nonempty
          i B hB hiB, hfloor]
  let times := deadlineWithdrawalSingletonTimes i B
  have h := hdom times (some 0)
  have hfirst := deadlineWithdrawal_singletonWitness_first i B
  have hcoalition := deadlineWithdrawal_singletonWitness_coalition i B
  have hquiet : quittingFirstStoppingOutcome (quietParentClocks times) =
      some ⟨cappedClockChildCoalition {i},
        cappedClockChildCoalition_nonempty (Finset.singleton_nonempty i)⟩ := by
    have hsubtype :
        (⟨cappedClockChildCoalition (quittingEarliestStoppingCoalition times),
          cappedClockChildCoalition_nonempty
            (quittingEarliestStoppingCoalition_nonempty times)⟩ :
            {S : Finset (Option ι) // S.Nonempty}) =
          ⟨cappedClockChildCoalition {i},
            cappedClockChildCoalition_nonempty
              (Finset.singleton_nonempty i)⟩ := by
      apply Subtype.ext
      exact congrArg cappedClockChildCoalition hcoalition
    exact (quittingFirstStoppingOutcome_quietParentClocks_of_first_eq
      times 0 hfirst).trans (congrArg Option.some hsubtype)
  have houtside :
      quittingFirstStoppingOutcome (outsideDeadlineClocks times (some 0)) =
        some ⟨cappedClockJoinedCoalition {i},
          cappedClockJoinedCoalition_nonempty {i}⟩ := by
    have hsubtype :
        (⟨cappedClockJoinedCoalition (quittingEarliestStoppingCoalition times),
          cappedClockJoinedCoalition_nonempty _⟩ :
            {S : Finset (Option ι) // S.Nonempty}) =
          ⟨cappedClockJoinedCoalition {i},
            cappedClockJoinedCoalition_nonempty {i}⟩ := by
      apply Subtype.ext
      exact congrArg cappedClockJoinedCoalition hcoalition
    exact (quittingFirstStoppingOutcome_outsideDeadlineClocks_of_eq_first
      times 0 hfirst).trans (congrArg Option.some hsubtype)
  have hchild (j : ι) :
      quittingFirstStoppingOutcome (cappedChildParentClocks times (some 0) j) =
        some ⟨cappedClockChildCoalition (insert j {i}),
          cappedClockChildCoalition_nonempty (Finset.insert_nonempty j {i})⟩ := by
    have hsubtype :
        (⟨cappedClockChildCoalition
            (insert j (quittingEarliestStoppingCoalition times)),
          cappedClockChildCoalition_nonempty (Finset.insert_nonempty _ _)⟩ :
            {S : Finset (Option ι) // S.Nonempty}) =
          ⟨cappedClockChildCoalition (insert j {i}),
            cappedClockChildCoalition_nonempty
              (Finset.insert_nonempty j {i})⟩ := by
      apply Subtype.ext
      exact congrArg (fun S => cappedClockChildCoalition (insert j S)) hcoalition
    exact (quittingFirstStoppingOutcome_cappedChildParentClocks_of_eq_first
      times 0 j hfirst).trans (congrArg Option.some hsubtype)
  have hwithdraw (j : ι) :
      deadlineWithdrawalActualEvaluatedChildGain reward
          quittingTerminalEvaluation times (some 0) j =
        deadlineWithdrawalGainFloor reward j {i}
          (Finset.singleton_nonempty i) := by
    by_cases hji : j = i
    · subst j
      rw [deadlineWithdrawalActualEvaluatedChildGain,
        quittingPureClockEvaluatedPayoff_terminalEvaluation,
        quittingPureClockEvaluatedPayoff_terminalEvaluation]
      rw [hafter]
      rw [quittingPureClockTerminalPayoff, hquiet]
      have hsingleton :
          (⟨cappedClockChildCoalition {i},
            cappedClockChildCoalition_nonempty
              (Finset.singleton_nonempty i)⟩ :
              {S : Finset (Option ι) // S.Nonempty}) =
            ⟨{some i}, Finset.singleton_nonempty (some i)⟩ := by
        apply Subtype.ext
        simp [cappedClockChildCoalition]
        rfl
      rw [hsingleton, deadlineWithdrawalGainFloor_singleton]
    · have hclock : times j ≠ some 0 := by
        simp [times, deadlineWithdrawalSingletonTimes, hji]
      rw [deadlineWithdrawalActualEvaluatedChildGain_some_of_ne
        reward quittingTerminalEvaluation times 0 j hclock]
      have hj : j ∉ ({i} : Finset ι) := by simpa using hji
      exact (deadlineWithdrawalGainFloor_of_not_mem reward j {i}
        (Finset.singleton_nonempty i) hj).symm
  simp only [cappedClockActualEvaluatedOutsideGain,
    cappedClockActualEvaluatedChildGain] at h
  simp_rw [hwithdraw] at h
  simp_rw [quittingPureClockEvaluatedPayoff_terminalEvaluation] at h
  unfold quittingPureClockTerminalPayoff at h
  rw [hquiet, houtside] at h
  simp_rw [hchild] at h
  simpa [quittingPureClockTerminalPayoff] using h

/-- Universal deterministic terminal domination reconstructs the literal
D-N, D-F, and D-J raw rows with the *same* two nonnegative weight arrays.
The singleton D-J row uses an attained finite zero-or-passive floor. -/
def deadlineWithdrawalRewardCertificateOfTerminalPointwise
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (advanceWeight withdrawalWeight : ι → ℝ)
    (hadvance : ∀ i, 0 ≤ advanceWeight i)
    (hwithdrawal : ∀ i, 0 ≤ withdrawalWeight i)
    (hdom : ∀ times deadline,
      cappedClockActualEvaluatedOutsideGain reward quittingTerminalEvaluation
          times deadline ≤
        ∑ i, (advanceWeight i *
            cappedClockActualEvaluatedChildGain reward quittingTerminalEvaluation
              times deadline i +
          withdrawalWeight i *
            deadlineWithdrawalActualEvaluatedChildGain reward
              quittingTerminalEvaluation times deadline i)) :
    DeadlineWithdrawalRewardCertificate reward where
  advanceWeight := advanceWeight
  withdrawalWeight := withdrawalWeight
  advanceWeight_nonneg := hadvance
  withdrawalWeight_nonneg := hwithdrawal
  never_row := deadlineWithdrawal_neverRow_of_terminalPointwise
    reward advanceWeight withdrawalWeight hdom
  future_row := deadlineWithdrawal_futureRow_of_terminalPointwise
    reward advanceWeight withdrawalWeight hdom
  join_row := by
    intro A hA
    by_cases hcard : A.card = 1
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
      simpa using deadlineWithdrawal_joinRow_singleton_of_terminalPointwise
        reward advanceWeight withdrawalWeight hdom i
    · have herase : ∀ i ∈ A, (A.erase i).Nonempty := by
        intro i hi
        by_contra hrest
        have hempty : A.erase i = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hrest
        rcases (Finset.erase_eq_empty_iff A i).mp hempty with hAempty | hAsingle
        · obtain ⟨j, hj⟩ := hA
          simp [hAempty] at hj
        · apply hcard
          rw [hAsingle]
          simp
      exact deadlineWithdrawal_joinRow_of_terminalPointwise_of_erase_nonempty
        reward advanceWeight withdrawalWeight hdom A hA herase

/-- Raw D certificates are exactly universal terminal pathwise
advance-plus-atom-withdrawal domination at fixed nonnegative arrays. -/
theorem deadlineWithdrawal_terminalPointwise_iff_certificate
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (advanceWeight withdrawalWeight : ι → ℝ)
    (hadvance : ∀ i, 0 ≤ advanceWeight i)
    (hwithdrawal : ∀ i, 0 ≤ withdrawalWeight i) :
    (∀ times deadline,
      cappedClockActualEvaluatedOutsideGain reward quittingTerminalEvaluation
          times deadline ≤
        ∑ i, (advanceWeight i *
            cappedClockActualEvaluatedChildGain reward quittingTerminalEvaluation
              times deadline i +
          withdrawalWeight i *
            deadlineWithdrawalActualEvaluatedChildGain reward
              quittingTerminalEvaluation times deadline i)) ↔
      ∃ certificate : DeadlineWithdrawalRewardCertificate reward,
        certificate.advanceWeight = advanceWeight ∧
          certificate.withdrawalWeight = withdrawalWeight := by
  constructor
  · intro hdom
    exact ⟨deadlineWithdrawalRewardCertificateOfTerminalPointwise reward
      advanceWeight withdrawalWeight hadvance hwithdrawal hdom, rfl, rfl⟩
  · rintro ⟨certificate, ha, hb⟩ times deadline
    have h := deadlineWithdrawalActualEvaluatedOutsideGain_le_weighted_childGains
      reward certificate quittingTerminalEvaluation
      quittingTerminalEvaluation_nonneg quittingTerminalEvaluation_antitone
      times deadline
    simpa only [ha, hb] using h

end GameTheory

import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalFamilyDebtBounds
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockPointwiseNecessity
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeterministicResponseWitnesses

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
  let times : ι → Option ℕ := fun _ => none
  have h := hdom times (some 0)
  have hgains := quietExtension_allNeverGains (ι := ι) reward 0
  have hwithdraw (i : ι) :
      deadlineWithdrawalActualEvaluatedChildGain reward
        quittingTerminalEvaluation times (some 0) i = 0 := by
    apply deadlineWithdrawalActualEvaluatedChildGain_some_of_ne
    simp [times]
  simp only [cappedClockActualEvaluatedOutsideGain,
    cappedClockActualEvaluatedChildGain,
    quittingPureClockEvaluatedPayoff_terminalEvaluation] at h
  change cappedClockActualOutsideGain reward (fun _ : ι => none) (some 0) ≤
    ∑ i, (advanceWeight i *
        cappedClockActualChildGain reward (fun _ : ι => none) (some 0) i +
      withdrawalWeight i * deadlineWithdrawalActualEvaluatedChildGain reward
        quittingTerminalEvaluation (fun _ : ι => none) (some 0) i) at h
  change ∀ i, deadlineWithdrawalActualEvaluatedChildGain reward
    quittingTerminalEvaluation (fun _ : ι => none) (some 0) i = 0 at hwithdraw
  rw [hgains.1] at h
  simp_rw [hgains.2, hwithdraw] at h
  simpa using h

omit [Nonempty ι] in
/-- The public future-row witness has first child date one and precisely the
specified first coalition. -/
private theorem deadlineWithdrawal_futureWitness_first
    (A : Finset ι) (hA : A.Nonempty) :
    quittingEarliestStoppingValue (cappedClockFutureTimes A) =
      (1 : WithTop ℕ) :=
  quietExtensionCoalitionTimes_first A hA 1

omit [Nonempty ι] in
private theorem deadlineWithdrawal_futureWitness_coalition
    (A : Finset ι) (hA : A.Nonempty) :
    quittingEarliestStoppingCoalition (cappedClockFutureTimes A) = A :=
  quietExtensionCoalitionTimes_coalition A hA 1

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
  have hwithdraw (i : ι) :
      deadlineWithdrawalActualEvaluatedChildGain reward
        quittingTerminalEvaluation times (some 0) i = 0 := by
    apply deadlineWithdrawalActualEvaluatedChildGain_some_of_ne
    simp [times, cappedClockFutureTimes]
  simp only [cappedClockActualEvaluatedOutsideGain,
    cappedClockActualEvaluatedChildGain,
    quittingPureClockEvaluatedPayoff_terminalEvaluation] at h
  change cappedClockActualOutsideGain reward times (some 0) ≤
    ∑ i, (advanceWeight i * cappedClockActualChildGain reward times (some 0) i +
      withdrawalWeight i * deadlineWithdrawalActualEvaluatedChildGain reward
        quittingTerminalEvaluation times (some 0) i) at h
  rw [quietExtension_outsideGain_of_before reward times 0 1 A hA hfirst hcoalition
    (by omega)] at h
  simp_rw [quietExtension_childGain_of_before reward times 0 1 A hA hfirst hcoalition
    (by omega), hwithdraw] at h
  simpa using h

omit [Nonempty ι] in
private theorem deadlineWithdrawal_joinWitness_first
    (A : Finset ι) (hA : A.Nonempty) :
    quittingEarliestStoppingValue (cappedClockJoiningTimes A) =
      (0 : WithTop ℕ) :=
  quietExtensionCoalitionTimes_first A hA 0

omit [Nonempty ι] in
private theorem deadlineWithdrawal_joinWitness_coalition
    (A : Finset ι) (hA : A.Nonempty) :
    quittingEarliestStoppingCoalition (cappedClockJoiningTimes A) = A :=
  quietExtensionCoalitionTimes_coalition A hA 0

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
    cappedClockActualEvaluatedChildGain,
    quittingPureClockEvaluatedPayoff_terminalEvaluation] at h
  change cappedClockActualOutsideGain reward times (some 0) ≤
    ∑ i, (advanceWeight i * cappedClockActualChildGain reward times (some 0) i +
      withdrawalWeight i * deadlineWithdrawalActualEvaluatedChildGain reward
        quittingTerminalEvaluation times (some 0) i) at h
  rw [quietExtension_outsideGain_of_tie reward times 0 A hA hfirst hcoalition] at h
  simp_rw [quietExtension_childGain_of_tie reward times 0 A hA hfirst hcoalition,
    hwithdraw] at h
  exact h

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
  quietExtensionSingletonTimes i B 0 j

omit [Nonempty ι] in
private theorem deadlineWithdrawal_singletonWitness_first
    (i : ι) (B : Finset ι) :
    quittingEarliestStoppingValue (deadlineWithdrawalSingletonTimes i B) =
      (0 : WithTop ℕ) :=
  quietExtensionSingletonTimes_first i B 0

omit [Nonempty ι] in
private theorem deadlineWithdrawal_singletonWitness_coalition
    (i : ι) (B : Finset ι) :
    quittingEarliestStoppingCoalition
        (deadlineWithdrawalSingletonTimes i B) = {i} :=
  quietExtensionSingletonTimes_coalition i B 0

omit [Fintype ι] [Nonempty ι] in
private theorem deadlineWithdrawal_singletonWitness_update
    (i : ι) (B : Finset ι) (hiB : i ∉ B) :
    Function.update (deadlineWithdrawalSingletonTimes i B) i none =
      cappedClockFutureTimes B :=
  quietExtensionSingletonTimes_update i B 0 hiB

private theorem deadlineWithdrawal_singletonWitness_withdrawn_of_nonempty
    (i : ι) (B : Finset ι) (hB : B.Nonempty) (hiB : i ∉ B) :
    quittingFirstStoppingOutcome
        (withdrawnChildParentClocks
          (deadlineWithdrawalSingletonTimes i B) (some 0) i) =
      some ⟨cappedClockChildCoalition B,
        cappedClockChildCoalition_nonempty hB⟩ := by
  have hclock : deadlineWithdrawalSingletonTimes i B i = some 0 := by
    simp [deadlineWithdrawalSingletonTimes, quietExtensionSingletonTimes]
  rw [withdrawnChildParentClocks_eq_quiet_update_none
      (deadlineWithdrawalSingletonTimes i B) 0 i hclock,
    deadlineWithdrawal_singletonWitness_update i B hiB]
  exact quietExtension_outcome_of_first (cappedClockFutureTimes B) 1 B hB
    (deadlineWithdrawal_futureWitness_first B hB)
    (deadlineWithdrawal_futureWitness_coalition B hB)

private theorem deadlineWithdrawal_singletonWitness_withdrawn_of_empty
    (i : ι) :
    quittingFirstStoppingOutcome
        (withdrawnChildParentClocks
          (deadlineWithdrawalSingletonTimes i ∅) (some 0) i) = none := by
  have hclock : deadlineWithdrawalSingletonTimes i ∅ i = some 0 := by
    simp [deadlineWithdrawalSingletonTimes, quietExtensionSingletonTimes]
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
  obtain ⟨B, _, hafter⟩ : ∃ B : Finset ι, i ∉ B ∧
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
  have hquiet := quietExtension_outcome_of_first times 0 {i}
    (Finset.singleton_nonempty i) hfirst hcoalition
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
      rw [quittingPureClockTerminalPayoff, hquiet, deadlineWithdrawalGainFloor_singleton]
      simp only [quietExtension_childCoalition_singleton]
    · have hclock : times j ≠ some 0 := by
        simp [times, deadlineWithdrawalSingletonTimes, quietExtensionSingletonTimes, hji]
      rw [deadlineWithdrawalActualEvaluatedChildGain_some_of_ne
        reward quittingTerminalEvaluation times 0 j hclock]
      have hj : j ∉ ({i} : Finset ι) := by simpa using hji
      exact (deadlineWithdrawalGainFloor_of_not_mem reward j {i}
        (Finset.singleton_nonempty i) hj).symm
  simp only [cappedClockActualEvaluatedOutsideGain,
    cappedClockActualEvaluatedChildGain,
    quittingPureClockEvaluatedPayoff_terminalEvaluation] at h
  change cappedClockActualOutsideGain reward times (some 0) ≤
    ∑ j, (advanceWeight j * cappedClockActualChildGain reward times (some 0) j +
      withdrawalWeight j * deadlineWithdrawalActualEvaluatedChildGain reward
        quittingTerminalEvaluation times (some 0) j) at h
  rw [quietExtension_outsideGain_of_tie reward times 0 {i}
    (Finset.singleton_nonempty i) hfirst hcoalition] at h
  simp_rw [quietExtension_childGain_of_tie reward times 0 {i}
    (Finset.singleton_nonempty i) hfirst hcoalition, hwithdraw] at h
  exact h

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

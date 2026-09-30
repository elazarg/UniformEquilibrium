import UniformEquilibrium.Quitting.Classification.QuietExtension.PatientWithdrawalCoalitionGain
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeterministicResponseWitnesses

/-!
# Exact terminal patient-withdrawal witnesses

The patient floor is attained either by the actual late-own-quit-or-Never
alternative or by a passive nonempty coalition. A hidden later coalition
realizes that floor at a singleton first quit; nonsingleton first coalitions
reuse the existing atom-withdrawal payoff calculation.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
/-- The finite patient floor has an attained alternative, even when there
is no nonempty passive coalition. -/
theorem patientWithdrawalFloor_attained
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) (i : ι) :
    patientWithdrawalFloor reward i = patientWithdrawalOwnNeverAlternative reward i ∨
      ∃ (B : Finset ι) (hB : B.Nonempty), i ∉ B ∧
        patientWithdrawalFloor reward i =
          reward ⟨cappedClockChildCoalition B, cappedClockChildCoalition_nonempty hB⟩
            (some i) := by
  classical
  let passive : Finset ℝ :=
    Finset.univ.image fun B : {A : Finset ι // A.Nonempty ∧ i ∉ A} =>
      reward ⟨cappedClockChildCoalition B.1, cappedClockChildCoalition_nonempty B.2.1⟩
        (some i)
  have hfloor : patientWithdrawalFloor reward i =
      (insert (patientWithdrawalOwnNeverAlternative reward i) passive).min'
        (Finset.insert_nonempty _ passive) := rfl
  have hmem := Finset.min'_mem (insert (patientWithdrawalOwnNeverAlternative reward i) passive)
    (Finset.insert_nonempty _ passive)
  rcases Finset.mem_insert.mp hmem with hown | hpassive
  · exact Or.inl (hfloor.trans hown)
  · obtain ⟨B, _, hvalue⟩ := Finset.mem_image.mp hpassive
    exact Or.inr ⟨B.1, B.2.1, B.2.2, hfloor.trans hvalue.symm⟩

/-- A single hidden passive coalition realizes the patient payoff floor
for every finite first date and every earlier or tied outsider deadline. -/
theorem patientWithdrawalFloor_attainingSingletonWitness
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) (i : ι) :
    ∃ B : Finset ι, i ∉ B ∧ ∀ first time : ℕ, time ≤ first →
      patientWithdrawalTerminalPayoffLimit reward
          (quietExtensionSingletonTimes i B first) (some time) i =
        patientWithdrawalFloor reward i := by
  rcases patientWithdrawalFloor_attained reward i with hown | ⟨B, hB, hiB, hfloor⟩
  · refine ⟨∅, by simp, ?_⟩
    intro first time htime
    have hbefore : ¬ quittingStoppingTimeValue
        (quietExtensionSingletonTimes i ∅ first i) < (time : WithTop ℕ) := by
      simpa [quietExtensionSingletonTimes, quittingStoppingTimeValue] using
        not_lt_of_ge (WithTop.coe_le_coe.mpr htime)
    have hall : ∀ j, j ≠ i → quietExtensionSingletonTimes i ∅ first j = none := by
      intro j hj
      simp [quietExtensionSingletonTimes, hj]
    rw [patientWithdrawalTerminalPayoffLimit, ite_eq_right hbefore, ite_eq_left hall]
    exact hown.symm
  · refine ⟨B, hiB, ?_⟩
    intro first time htime
    have hbefore : ¬ quittingStoppingTimeValue
        (quietExtensionSingletonTimes i B first i) < (time : WithTop ℕ) := by
      simpa [quietExtensionSingletonTimes, quittingStoppingTimeValue] using
        not_lt_of_ge (WithTop.coe_le_coe.mpr htime)
    have hall : ¬ ∀ j, j ≠ i → quietExtensionSingletonTimes i B first j = none := by
      obtain ⟨j, hj⟩ := hB
      have hji : j ≠ i := by
        intro heq
        subst j
        exact hiB hj
      intro h
      have hjclock := h j hji
      simp [quietExtensionSingletonTimes, hji, hj] at hjclock
    rw [patientWithdrawalTerminalPayoffLimit, ite_eq_right hbefore, ite_eq_right hall,
      quietExtensionPrivateClocks_cancel, quietExtensionSingletonTimes_update i B first hiB]
    rw [quietExtension_terminalPayoff_of_first reward
      (quietExtensionCoalitionTimes B (first + 1)) (first + 1) B hB
      (quietExtensionCoalitionTimes_first B hB (first + 1))
      (quietExtensionCoalitionTimes_coalition B hB (first + 1)) (some i)]
    exact hfloor.symm

/-- Outside the owner's singleton branch, patient withdrawal attains the
raw W coefficient exactly for every earlier or tied deadline. -/
theorem patientWithdrawalTerminalGain_eq_floor_of_not_singleton
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (times : ι → Option ℕ) (time first : ℕ) (A : Finset ι) (hA : A.Nonempty)
    (hfirst : quittingEarliestStoppingValue times = (first : WithTop ℕ))
    (hcoalition : quittingEarliestStoppingCoalition times = A) (htime : time ≤ first)
    (i : ι) (hsingleton : A ≠ {i}) :
    patientWithdrawalTerminalGain reward times (some time) i =
      patientWithdrawalGainFloor reward i A hA := by
  have hsingleton' : quittingEarliestStoppingCoalition times ≠ {i} := by
    rwa [hcoalition]
  rw [patientWithdrawalTerminalGain_eq_atomWithdrawal_of_nonsingletonFirst
    reward times time first i hfirst htime hsingleton']
  have hfloor : patientWithdrawalGainFloor reward i A hA =
      deadlineWithdrawalGainFloor reward i A hA := by
    simp [patientWithdrawalGainFloor, deadlineSecurityGainFloorWithRestart, hsingleton]
  rw [hfloor]
  by_cases hi : i ∈ A
  · have hrest : (A.erase i).Nonempty := by
      by_contra h
      rcases (Finset.erase_eq_empty_iff A i).mp
        (Finset.not_nonempty_iff_eq_empty.mp h) with hempty | heq
      · exact hA.ne_empty hempty
      · exact hsingleton heq
    have hi' : i ∈ quittingEarliestStoppingCoalition times := by rwa [hcoalition]
    have hrest' : ((quittingEarliestStoppingCoalition times).erase i).Nonempty := by
      rwa [hcoalition]
    have h := deadlineWithdrawalActualEvaluatedChildGain_nonsingleton_eq_floor
      reward quittingTerminalEvaluation times first i hfirst hi' hrest'
    simpa only [quittingTerminalEvaluation_coe, one_mul, hcoalition] using h
  · have hclock : times i ≠ some first := by
      intro hclock
      apply hi
      rw [← hcoalition]
      simp [quittingEarliestStoppingCoalition, hfirst, hclock, quittingStoppingTimeValue]
    rw [deadlineWithdrawalActualEvaluatedChildGain_some_of_ne
      reward quittingTerminalEvaluation times first i hclock,
      deadlineWithdrawalGainFloor_of_not_mem reward i A hA hi]

/-- Every nonempty coalition has deterministic clocks attaining all its
patient W coefficients simultaneously, at any chosen finite first date. -/
theorem patientWithdrawal_exists_exactCoalitionWitness
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (A : Finset ι) (hA : A.Nonempty) (first : ℕ) :
    ∃ times : ι → Option ℕ,
      quittingEarliestStoppingValue times = (first : WithTop ℕ) ∧
      quittingEarliestStoppingCoalition times = A ∧
      ∀ time : ℕ, time ≤ first → ∀ i,
        patientWithdrawalTerminalGain reward times (some time) i =
          patientWithdrawalGainFloor reward i A hA := by
  by_cases hcard : A.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
    obtain ⟨B, _, hlimit⟩ := patientWithdrawalFloor_attainingSingletonWitness reward i
    let times := quietExtensionSingletonTimes i B first
    have hfirst := quietExtensionSingletonTimes_first i B first
    have hcoalition := quietExtensionSingletonTimes_coalition i B first
    refine ⟨times, hfirst, hcoalition, ?_⟩
    intro time htime j
    by_cases hji : j = i
    · subst j
      rw [patientWithdrawalTerminalGain, hlimit first time htime,
        quietExtension_terminalPayoff_of_first reward times first {i}
          (Finset.singleton_nonempty i) hfirst hcoalition (some i),
        patientWithdrawalGainFloor, deadlineSecurityGainFloor_singletonWithRestart]
      simp only [quietExtension_childCoalition_singleton]
    · apply patientWithdrawalTerminalGain_eq_floor_of_not_singleton
        reward times time first {i} (Finset.singleton_nonempty i)
        hfirst hcoalition htime j
      intro heq
      have hmem : i ∈ ({j} : Finset ι) := by rw [← heq]; simp
      exact hji (Finset.mem_singleton.mp hmem).symm
  · let times := quietExtensionCoalitionTimes A first
    have hfirst := quietExtensionCoalitionTimes_first A hA first
    have hcoalition := quietExtensionCoalitionTimes_coalition A hA first
    refine ⟨times, hfirst, hcoalition, ?_⟩
    intro time htime i
    apply patientWithdrawalTerminalGain_eq_floor_of_not_singleton
      reward times time first A hA hfirst hcoalition htime i
    intro heq
    apply hcard
    simp [heq]

end GameTheory

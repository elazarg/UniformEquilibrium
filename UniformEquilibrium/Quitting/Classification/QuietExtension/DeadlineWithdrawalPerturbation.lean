import UniformEquilibrium.Quitting.Classification.QuietExtension.PatientWithdrawalPerturbation

/-! # Fresh zero-or-passive deadline floors under raw reward perturbations

The deadline floor is the zero truncation of the canonical patient floor.
Its stability and every nonsingleton gain delegate to the existing patient
minimum and gain estimates. No positive patient floor is promoted to an
all-evaluation guarantee.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem le_deadlineWithdrawalZeroFloor_iff
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (who : ι) (value : ℝ) :
    value ≤ deadlineWithdrawalZeroFloor reward who ↔
      value ≤ 0 ∧ ∀ B (hB : B.Nonempty), who ∉ B →
        value ≤ reward ⟨cappedClockChildCoalition B,
          cappedClockChildCoalition_nonempty hB⟩ (some who) := by
  classical
  constructor
  · intro h
    exact ⟨h.trans (deadlineWithdrawalZeroFloor_le_zero reward who),
      fun B hB hnot => h.trans
        (deadlineWithdrawalZeroFloor_le_passiveReward reward who B hB hnot)⟩
  · rintro ⟨hzero, hpassive⟩
    unfold deadlineWithdrawalZeroFloor
    apply (Finset.le_min'_iff _ _).mpr
    intro entry hentry
    rcases Finset.mem_insert.mp hentry with rfl | hentry
    · exact hzero
    · obtain ⟨B, _, rfl⟩ := Finset.mem_image.mp hentry
      exact hpassive B.1 B.2.1 B.2.2

/-- The actual zero floor depends only on its player's reward recipient slice. -/
theorem deadlineWithdrawalZeroFloor_congr_recipient
    (reward other : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) (who : ι)
    (hagrees : ∀ terminal, reward terminal (some who) = other terminal (some who)) :
    deadlineWithdrawalZeroFloor reward who = deadlineWithdrawalZeroFloor other who := by
  apply le_antisymm
  · apply (le_deadlineWithdrawalZeroFloor_iff other who _).mpr
    exact ⟨deadlineWithdrawalZeroFloor_le_zero reward who, fun B hB hnot => by
      rw [← hagrees]
      exact deadlineWithdrawalZeroFloor_le_passiveReward reward who B hB hnot⟩
  · apply (le_deadlineWithdrawalZeroFloor_iff reward who _).mpr
    exact ⟨deadlineWithdrawalZeroFloor_le_zero other who, fun B hB hnot => by
      rw [hagrees]
      exact deadlineWithdrawalZeroFloor_le_passiveReward other who B hB hnot⟩

/-- Withdrawal gains retain the same literal values when that recipient slice agrees. -/
theorem deadlineWithdrawalGainFloor_congr_recipient
    (reward other : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) (who : ι)
    (hagrees : ∀ terminal, reward terminal (some who) = other terminal (some who))
    (A : Finset ι) (hA : A.Nonempty) :
    deadlineWithdrawalGainFloor reward who A hA =
      deadlineWithdrawalGainFloor other who A hA := by
  unfold deadlineWithdrawalGainFloor
  split_ifs
  · rw [hagrees, hagrees]
  · rw [deadlineWithdrawalZeroFloor_congr_recipient reward other who hagrees, hagrees]
  · rfl

/-- Truncation is a literal equality of the two actual finite passive minima. -/
theorem deadlineWithdrawalZeroFloor_eq_min_patientWithdrawalFloor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) (who : ι) :
    deadlineWithdrawalZeroFloor reward who = min 0 (patientWithdrawalFloor reward who) := by
  apply le_antisymm
  · apply le_min (deadlineWithdrawalZeroFloor_le_zero reward who)
    apply (le_patientWithdrawalFloor_iff reward who _).mpr
    constructor
    · exact (deadlineWithdrawalZeroFloor_le_zero reward who).trans
        (le_max_right _ _)
    · exact fun B hB hnot =>
        deadlineWithdrawalZeroFloor_le_passiveReward reward who B hB hnot
  · apply (le_deadlineWithdrawalZeroFloor_iff reward who _).mpr
    exact ⟨min_le_left _ _, fun B hB hnot => (min_le_right _ _).trans
      (patientWithdrawalFloor_le_passiveReward reward who B hB hnot)⟩

/-- Fresh canonical deadline floors are 1-Lipschitz, including zero and ties. -/
theorem abs_deadlineWithdrawalZeroFloor_sub_le
    (reward other : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (error : ℝ) (hclose : ∀ terminal who, |other terminal who - reward terminal who| ≤ error)
    (who : ι) :
    |deadlineWithdrawalZeroFloor other who - deadlineWithdrawalZeroFloor reward who| ≤
      error := by
  rw [deadlineWithdrawalZeroFloor_eq_min_patientWithdrawalFloor,
    deadlineWithdrawalZeroFloor_eq_min_patientWithdrawalFloor]
  have hmin := abs_min_sub_min_le_max (0 : ℝ) (patientWithdrawalFloor other who)
    0 (patientWithdrawalFloor reward who)
  have hbound : |min 0 (patientWithdrawalFloor other who) -
      min 0 (patientWithdrawalFloor reward who)| ≤
      |patientWithdrawalFloor other who - patientWithdrawalFloor reward who| := by
    simpa only [sub_self, abs_zero,
      max_eq_right (abs_nonneg
        (patientWithdrawalFloor other who - patientWithdrawalFloor reward who))] using hmin
  exact hbound.trans (abs_patientWithdrawalFloor_sub_le reward other error hclose who)

/-- Deadline gains change by at most twice the raw-coordinate error. -/
theorem abs_deadlineWithdrawalGainFloor_sub_le
    (reward other : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (error : ℝ) (hclose : ∀ terminal who, |other terminal who - reward terminal who| ≤ error)
    (who : ι) (A : Finset ι) (hA : A.Nonempty) :
    |deadlineWithdrawalGainFloor other who A hA -
      deadlineWithdrawalGainFloor reward who A hA| ≤ 2 * error := by
  by_cases hsingle : A = {who}
  · subst A
    simp only [deadlineWithdrawalGainFloor_singleton]
    exact Maths.FiniteInequality.abs_sub_differences_le _ _ _ _ error
      (abs_deadlineWithdrawalZeroFloor_sub_le reward other error hclose who) (hclose _ _)
  · have h := abs_patientWithdrawalGainFloor_sub_le reward other error hclose who A hA
    simpa only [patientWithdrawalGainFloor, deadlineSecurityGainFloorWithRestart,
      ite_eq_right hsingle, add_zero] using h

end GameTheory

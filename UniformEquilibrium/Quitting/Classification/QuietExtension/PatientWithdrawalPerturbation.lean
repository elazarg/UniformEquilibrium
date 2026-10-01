import UniformEquilibrium.Quitting.Classification.QuietExtension.PatientWithdrawalRaw
import MathUE.DirectedTransport.FiniteInequality.Perturbation
import Mathlib.Algebra.Order.Group.MinMax

/-! # Raw-coordinate perturbations of the canonical patient floors

The floor is recomputed from the changed actual reward table. This is a
finite-row stability result, not an evaluation-by-evaluation patient bound.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem le_patientWithdrawalFloor_iff
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (who : ι) (value : ℝ) :
    value ≤ patientWithdrawalFloor reward who ↔
      value ≤ patientWithdrawalOwnNeverAlternative reward who ∧
        ∀ B (hB : B.Nonempty), who ∉ B →
          value ≤ reward ⟨cappedClockChildCoalition B,
            cappedClockChildCoalition_nonempty hB⟩ (some who) := by
  classical
  constructor
  · intro h
    exact ⟨h.trans (patientWithdrawalFloor_le_ownNeverAlternative reward who),
      fun B hB hnot => h.trans (patientWithdrawalFloor_le_passiveReward reward who B hB hnot)⟩
  · rintro ⟨hown, hpassive⟩
    unfold patientWithdrawalFloor
    apply (Finset.le_min'_iff _ _).mpr
    intro entry hentry
    rcases Finset.mem_insert.mp hentry with rfl | hentry
    · exact hown
    · obtain ⟨B, _, rfl⟩ := Finset.mem_image.mp hentry
      exact hpassive B.1 B.2.1 B.2.2

omit [Fintype ι] [DecidableEq ι] in
theorem abs_patientWithdrawalOwnNeverAlternative_sub_le
    (reward other : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (error : ℝ) (hclose : ∀ terminal who, |other terminal who - reward terminal who| ≤ error)
    (who : ι) :
    |patientWithdrawalOwnNeverAlternative other who -
      patientWithdrawalOwnNeverAlternative reward who| ≤ error :=
  (abs_max_sub_max_le_abs _ _ _).trans (hclose _ _)

private theorem patientFloor_sub_error_le
    (reward other : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (error : ℝ) (hclose : ∀ terminal who, |other terminal who - reward terminal who| ≤ error)
    (who : ι) :
    patientWithdrawalFloor reward who - error ≤ patientWithdrawalFloor other who := by
  apply (le_patientWithdrawalFloor_iff other who _).mpr
  constructor
  · have hfloor := patientWithdrawalFloor_le_ownNeverAlternative reward who
    have h := (abs_le.mp
      (abs_patientWithdrawalOwnNeverAlternative_sub_le reward other error hclose who)).1
    linarith
  · intro B hB hnot
    have hfloor := patientWithdrawalFloor_le_passiveReward reward who B hB hnot
    have h := (abs_le.mp (hclose ⟨cappedClockChildCoalition B,
      cappedClockChildCoalition_nonempty hB⟩ (some who))).1
    linarith

/-- The actual minimum of all passive alternatives and the late-own-quit alternative
is 1-Lipschitz in all raw reward entries, including at ties and zero singleton. -/
theorem abs_patientWithdrawalFloor_sub_le
    (reward other : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (error : ℝ) (hclose : ∀ terminal who, |other terminal who - reward terminal who| ≤ error)
    (who : ι) :
    |patientWithdrawalFloor other who - patientWithdrawalFloor reward who| ≤ error := by
  have hforward := patientFloor_sub_error_le reward other error hclose who
  have hbackward := patientFloor_sub_error_le other reward error
    (fun terminal who => by simpa only [abs_sub_comm] using hclose terminal who) who
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The actual patient withdrawal gain, with its fresh floor, changes by at most 2δ. -/
theorem abs_patientWithdrawalGainFloor_sub_le
    (reward other : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (error : ℝ) (hclose : ∀ terminal who, |other terminal who - reward terminal who| ≤ error)
    (who : ι) (A : Finset ι) (hA : A.Nonempty) :
    |patientWithdrawalGainFloor other who A hA -
      patientWithdrawalGainFloor reward who A hA| ≤ 2 * error := by
  have herror : 0 ≤ error := (abs_nonneg _).trans
    (hclose ⟨{some who}, Finset.singleton_nonempty (some who)⟩ (some who))
  by_cases hsingle : A = {who}
  · subst A
    simp only [patientWithdrawalGainFloor, deadlineSecurityGainFloor_singletonWithRestart]
    exact Maths.FiniteInequality.abs_sub_differences_le _ _ _ _ error
      (abs_patientWithdrawalFloor_sub_le reward other error hclose who) (hclose _ _)
  by_cases hwho : who ∈ A
  · have hrest : (A.erase who).Nonempty := by
      by_contra hrest
      have hempty := Finset.not_nonempty_iff_eq_empty.mp hrest
      rcases (Finset.erase_eq_empty_iff A who).mp hempty with hempty | hsingle'
      · exact hA.ne_empty hempty
      · exact hsingle hsingle'
    simp only [patientWithdrawalGainFloor, deadlineSecurityGainFloorWithRestart,
      ite_eq_right hsingle, add_zero,
      deadlineWithdrawalGainFloor_of_erase_nonempty other who A hwho hrest,
      deadlineWithdrawalGainFloor_of_erase_nonempty reward who A hwho hrest]
    exact Maths.FiniteInequality.abs_sub_differences_le _ _ _ _ error
      (hclose _ _) (hclose _ _)
  · simp only [patientWithdrawalGainFloor, deadlineSecurityGainFloorWithRestart,
      ite_eq_right hsingle, add_zero,
      deadlineWithdrawalGainFloor_of_not_mem other who A hA hwho,
      deadlineWithdrawalGainFloor_of_not_mem reward who A hA hwho,
      sub_self, abs_zero]
    positivity

end GameTheory

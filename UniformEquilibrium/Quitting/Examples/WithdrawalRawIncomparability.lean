import UniformEquilibrium.Quitting.Classification.QuietExtension.PatientWithdrawalRaw
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalSecurityMixedRaw
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalSecurityTerminalDebt
import Mathlib.Tactic.FinCases

/-! # Incomparable patient and deadline raw criteria

Both literal finite tables retain Never payoff zero. Certificate infeasibility
excludes the named raw compiler, not uniform-equilibrium existence.
-/

noncomputable section

namespace GameTheory.WithdrawalBoundaryExamples

open scoped BigOperators

private theorem childCoalition_image {ι : Type} [DecidableEq ι] (A : Finset ι) :
    cappedClockChildCoalition A = A.image some := by
  classical
  unfold cappedClockChildCoalition
  exact Finset.map_eq_image _ _

private theorem finOne_nonempty_eq_singleton
    (A : Finset (Fin 1)) (hA : A.Nonempty) : A = {0} := by
  obtain ⟨i, hi⟩ := hA
  apply Finset.eq_singleton_iff_unique_mem.mpr
  exact ⟨(Subsingleton.elim i (0 : Fin 1)) ▸ hi,
    fun j _ => Subsingleton.elim j 0⟩

private theorem patientFloor_finOne
    (reward : {A : Finset (Option (Fin 1)) // A.Nonempty} → Option (Fin 1) → ℝ) :
    patientWithdrawalFloor reward 0 = patientWithdrawalOwnNeverAlternative reward 0 := by
  let : IsEmpty {A : Finset (Fin 1) // A.Nonempty ∧ (0 : Fin 1) ∉ A} :=
    ⟨fun A => A.2.2 (by rw [finOne_nonempty_eq_singleton A.1 A.2.1]; simp)⟩
  simp [patientWithdrawalFloor]

/-- Child zero receives minus one on its solo exit; so does the outsider.
The outsider's solo exit and the joint exit pay zero to both players. -/
def patientOnlyReward
    (terminal : {A : Finset (Option (Fin 1)) // A.Nonempty})
    (_who : Option (Fin 1)) : ℝ :=
  if terminal.1 = {some 0} then -1 else 0

private theorem patientOnly_floor :
    patientWithdrawalFloor patientOnlyReward 0 = 0 := by
  rw [patientFloor_finOne]
  norm_num [patientWithdrawalOwnNeverAlternative, patientOnlyReward]

private theorem patientOnly_gain :
    patientWithdrawalGainFloor patientOnlyReward 0 {0} (Finset.singleton_nonempty 0) = 1 := by
  unfold patientWithdrawalGainFloor
  rw [deadlineSecurityGainFloor_singletonWithRestart, patientOnly_floor]
  norm_num [patientOnlyReward]

/-- Literal patient weights lambda=0, mu=1 pass the original full N/F/J rows. -/
def patientOnlyCertificate : PatientWithdrawalRewardCertificate patientOnlyReward where
  advanceWeight := 0
  withdrawalWeight := 1
  advanceWeight_nonneg := by simp
  withdrawalWeight_nonneg := by simp
  never_row := by
    norm_num [patientOnlyReward, patientWithdrawalOwnNeverAlternative, Fin.sum_univ_one]
  future_row := by
    intro A hA
    have hsingleton := finOne_nonempty_eq_singleton A hA
    subst A
    norm_num [patientOnlyReward, childCoalition_image,
      patientOnly_gain, Fin.sum_univ_one]
  join_row := by
    intro A hA
    have hsingleton := finOne_nonempty_eq_singleton A hA
    subst A
    norm_num [patientOnlyReward, childCoalition_image, cappedClockJoinedCoalition,
      patientOnly_gain, Fin.sum_univ_one]

private theorem patientOnly_future_impossible (weight : Fin 1 → ℝ)
    (hfuture :
      patientOnlyReward ⟨{none}, Finset.singleton_nonempty none⟩ none -
          patientOnlyReward ⟨cappedClockChildCoalition {0},
            cappedClockChildCoalition_nonempty (Finset.singleton_nonempty 0)⟩ none ≤
        ∑ i, weight i *
          (patientOnlyReward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) -
            patientOnlyReward ⟨cappedClockChildCoalition {0},
              cappedClockChildCoalition_nonempty (Finset.singleton_nonempty 0)⟩
              (some i))) : False := by
  norm_num [patientOnlyReward, childCoalition_image, Fin.sum_univ_one] at hfuture

/-- The unchanged deadline future row is the impossible inequality one<=zero. -/
theorem patientOnly_no_deadlineCertificate :
    ¬ Nonempty (DeadlineWithdrawalRewardCertificate patientOnlyReward) := by
  rintro ⟨certificate⟩
  exact patientOnly_future_impossible certificate.advanceWeight
    (certificate.future_row {0} (Finset.singleton_nonempty 0))

/-- Nonpositive evaluated security cannot repair the unchanged future row. -/
theorem patientOnly_no_evaluatedSecurityCertificate :
    ¬ Nonempty (DeadlineSecurityRewardCertificate patientOnlyReward) := by
  rintro ⟨certificate⟩
  exact patientOnly_future_impossible certificate.advanceWeight
    (certificate.future_row {0} (Finset.singleton_nonempty 0))

/-- Nor can positive terminal security repair the unchanged future row. -/
theorem patientOnly_no_terminalSecurityCertificate :
    ¬ Nonempty (DeadlineSecurityTerminalRewardCertificate patientOnlyReward) := by
  rintro ⟨certificate⟩
  exact patientOnly_future_impossible certificate.advanceWeight
    (certificate.future_row {0} (Finset.singleton_nonempty 0))

/-- Child labels zero and one occupy the first two bits; outsider none is bit four. -/
def twoChildCoalitionCode (A : Finset (Option (Fin 2))) : ℕ :=
  (if some 0 ∈ A then 1 else 0) + (if some 1 ∈ A then 2 else 0) +
    (if none ∈ A then 4 else 0)

/-- Complete literal deadline-only table: child-zero rewards on child one
and child joint exits are -1 and -2; outside joining gains are -1,0,1. -/
def deadlineOnlyReward
    (terminal : {A : Finset (Option (Fin 2)) // A.Nonempty})
    (who : Option (Fin 2)) : ℝ :=
  if who = some 0 then
    if twoChildCoalitionCode terminal.1 = 2 then -1
    else if twoChildCoalitionCode terminal.1 = 3 then -2 else 0
  else if who = none then
    if twoChildCoalitionCode terminal.1 = 5 then -1
    else if twoChildCoalitionCode terminal.1 = 7 then 1 else 0
  else 0

private abbrev passiveZeroUnique :
    Unique {A : Finset (Fin 2) // A.Nonempty ∧ (0 : Fin 2) ∉ A} where
  default := ⟨{1}, by decide⟩
  uniq A := by
    fin_cases A
    rfl

private theorem deadlineOnly_zeroFloor :
    deadlineWithdrawalZeroFloor deadlineOnlyReward 0 = -1 := by
  let := passiveZeroUnique
  have hpassive (B : {A : Finset (Fin 2) // A.Nonempty ∧ (0 : Fin 2) ∉ A}) :
      B.1 = {1} := congrArg Subtype.val (passiveZeroUnique.uniq B)
  norm_num [deadlineWithdrawalZeroFloor, Finset.univ_unique, hpassive,
    deadlineOnlyReward, twoChildCoalitionCode, childCoalition_image]

private theorem deadlineOnly_patientFloor :
    patientWithdrawalFloor deadlineOnlyReward 0 = -1 := by
  let := passiveZeroUnique
  have hpassive (B : {A : Finset (Fin 2) // A.Nonempty ∧ (0 : Fin 2) ∉ A}) :
      B.1 = {1} := congrArg Subtype.val (passiveZeroUnique.uniq B)
  norm_num [patientWithdrawalFloor, patientWithdrawalOwnNeverAlternative,
    Finset.univ_unique, hpassive, deadlineOnlyReward,
    twoChildCoalitionCode, childCoalition_image]

private theorem deadlineOnly_patientGain_singleton (i : Fin 2) :
    patientWithdrawalGainFloor deadlineOnlyReward i {0} (Finset.singleton_nonempty 0) =
      -(![1, 0] i) := by
  fin_cases i
  · change patientWithdrawalGainFloor deadlineOnlyReward (0 : Fin 2) {0}
      (Finset.singleton_nonempty 0) = -1
    unfold patientWithdrawalGainFloor
    rw [deadlineSecurityGainFloor_singletonWithRestart, deadlineOnly_patientFloor]
    norm_num [deadlineOnlyReward, twoChildCoalitionCode]
  · change patientWithdrawalGainFloor deadlineOnlyReward (1 : Fin 2) {0}
      (Finset.singleton_nonempty 0) = -(![1, 0] (1 : Fin 2))
    norm_num [patientWithdrawalGainFloor, deadlineSecurityGainFloorWithRestart,
      deadlineWithdrawalGainFloor]

private theorem deadlineOnly_patientGain_joint (i : Fin 2) :
    patientWithdrawalGainFloor deadlineOnlyReward i {0, 1} (by simp) = ![1, 0] i := by
  have hjoint : ({0, 1} : Finset (Fin 2)).Nontrivial := by decide
  have hmember : i ∈ ({0, 1} : Finset (Fin 2)) := by
    fin_cases i <;> simp
  unfold patientWithdrawalGainFloor deadlineSecurityGainFloorWithRestart
  rw [ite_eq_right hjoint.ne_singleton, add_zero]
  rw [deadlineWithdrawalGainFloor_of_erase_nonempty deadlineOnlyReward i {0, 1}
    hmember hjoint.erase_nonempty]
  fin_cases i
  · change deadlineOnlyReward
        ⟨cappedClockChildCoalition (({0, 1} : Finset (Fin 2)).erase 0),
          cappedClockChildCoalition_nonempty (by decide)⟩ (some 0) -
      deadlineOnlyReward
        ⟨cappedClockChildCoalition ({0, 1} : Finset (Fin 2)),
          cappedClockChildCoalition_nonempty (by decide)⟩ (some 0) = 1
    norm_num [deadlineOnlyReward, twoChildCoalitionCode, childCoalition_image]
  · change deadlineOnlyReward
        ⟨cappedClockChildCoalition (({0, 1} : Finset (Fin 2)).erase 1),
          cappedClockChildCoalition_nonempty (by decide)⟩ (some 1) -
      deadlineOnlyReward
        ⟨cappedClockChildCoalition ({0, 1} : Finset (Fin 2)),
          cappedClockChildCoalition_nonempty (by decide)⟩ (some 1) = 0
    norm_num [deadlineOnlyReward, twoChildCoalitionCode, childCoalition_image]

/-- Literal deadline weights a=(0,0), b=(1,0) satisfy the complete raw system. -/
def deadlineOnlyCertificate : DeadlineWithdrawalRewardCertificate deadlineOnlyReward where
  advanceWeight := 0
  withdrawalWeight := ![1, 0]
  advanceWeight_nonneg := by simp
  withdrawalWeight_nonneg := by intro i; fin_cases i <;> norm_num
  never_row := by norm_num [deadlineOnlyReward, twoChildCoalitionCode]
  future_row := by
    intro A hA
    fin_cases A <;> first
    | exact False.elim (Finset.not_nonempty_empty hA)
    | norm_num [deadlineOnlyReward, twoChildCoalitionCode, childCoalition_image]
  join_row := by
    intro A hA
    fin_cases A <;> first
    | exact False.elim (Finset.not_nonempty_empty hA)
    | norm_num [deadlineOnlyReward, twoChildCoalitionCode,
        childCoalition_image, cappedClockJoinedCoalition, Fin.sum_univ_two,
        deadlineWithdrawalGainFloor, deadlineOnly_zeroFloor, Finset.nontrivial_def]

/-- Original patient F at singleton zero forces mu-zero=0, whereas J at
the full child forces mu-zero>=1. No nonnegative patient weights can work. -/
theorem deadlineOnly_no_patientCertificate :
    ¬ Nonempty (PatientWithdrawalRewardCertificate deadlineOnlyReward) := by
  rintro ⟨certificate⟩
  have hfuture := certificate.future_row {0} (Finset.singleton_nonempty 0)
  have hjoin := certificate.join_row {0, 1} (by simp)
  norm_num [deadlineOnlyReward, twoChildCoalitionCode, childCoalition_image,
    deadlineOnly_patientGain_singleton, Fin.sum_univ_two] at hfuture
  norm_num [deadlineOnlyReward, twoChildCoalitionCode, childCoalition_image,
    cappedClockJoinedCoalition, deadlineOnly_patientGain_joint,
    Fin.sum_univ_two] at hjoin
  linarith [certificate.withdrawalWeight_nonneg 0]

/-- The patient-only table padded by the inert child player one. On child
coalitions containing zero, child zero and the outsider receive minus one;
child one and every outsider-containing terminal row receive zero. -/
def twoChildPatientOnlyReward
    (terminal : {A : Finset (Option (Fin 2)) // A.Nonempty})
    (who : Option (Fin 2)) : ℝ :=
  if who = some 1 then 0
  else if twoChildCoalitionCode terminal.1 = 1 ∨
      twoChildCoalitionCode terminal.1 = 3 then -1 else 0

/-- The added child's payoff is zero at every actual terminal coalition. -/
theorem twoChildPatientOnlyReward_dummy
    (terminal : {A : Finset (Option (Fin 2)) // A.Nonempty}) :
    twoChildPatientOnlyReward terminal (some 1) = 0 := by
  unfold twoChildPatientOnlyReward
  rw [ite_eq_left rfl]

/-- The patient floor of the active child is zero: both its passive child-one
exit and its own-Never alternative pay zero. -/
theorem twoChildPatientOnly_floor_zero :
    patientWithdrawalFloor twoChildPatientOnlyReward 0 = 0 := by
  let := passiveZeroUnique
  have hpassive (B : {A : Finset (Fin 2) // A.Nonempty ∧ (0 : Fin 2) ∉ A}) :
      B.1 = {1} := congrArg Subtype.val (passiveZeroUnique.uniq B)
  norm_num [patientWithdrawalFloor, patientWithdrawalOwnNeverAlternative,
    Finset.univ_unique, hpassive, twoChildPatientOnlyReward,
    twoChildCoalitionCode, childCoalition_image]

private theorem twoChildPatientOnly_gain_zero_singleton :
    patientWithdrawalGainFloor twoChildPatientOnlyReward 0 {0}
      (Finset.singleton_nonempty 0) = 1 := by
  unfold patientWithdrawalGainFloor
  rw [deadlineSecurityGainFloor_singletonWithRestart, twoChildPatientOnly_floor_zero]
  norm_num [twoChildPatientOnlyReward, twoChildCoalitionCode]

private theorem twoChildPatientOnly_gain_one_singleton :
    patientWithdrawalGainFloor twoChildPatientOnlyReward 0 {1}
      (Finset.singleton_nonempty 1) = 0 := by
  norm_num [patientWithdrawalGainFloor, deadlineSecurityGainFloorWithRestart,
    deadlineWithdrawalGainFloor]

private theorem twoChildPatientOnly_gain_joint :
    patientWithdrawalGainFloor twoChildPatientOnlyReward 0 {0, 1} (by simp) = 1 := by
  have hjoint : ({0, 1} : Finset (Fin 2)).Nontrivial := by decide
  unfold patientWithdrawalGainFloor deadlineSecurityGainFloorWithRestart
  rw [ite_eq_right hjoint.ne_singleton, add_zero]
  rw [deadlineWithdrawalGainFloor_of_erase_nonempty twoChildPatientOnlyReward 0 {0, 1}
    (by simp) hjoint.erase_nonempty]
  norm_num [twoChildPatientOnlyReward, twoChildCoalitionCode, childCoalition_image]

/-- The literal withdrawal-gain row on the three nonempty child coalitions
is one, zero, one, respectively. -/
theorem twoChildPatientOnly_withdrawalGain
    (A : Finset (Fin 2)) (hA : A.Nonempty) :
    patientWithdrawalGainFloor twoChildPatientOnlyReward 0 A hA =
      if 0 ∈ A then 1 else 0 := by
  fin_cases A
  · exact False.elim (Finset.not_nonempty_empty hA)
  · change patientWithdrawalGainFloor twoChildPatientOnlyReward 0 {0} hA = 1
    exact twoChildPatientOnly_gain_zero_singleton
  · change patientWithdrawalGainFloor twoChildPatientOnlyReward 0 {1} hA = 0
    exact twoChildPatientOnly_gain_one_singleton
  · change patientWithdrawalGainFloor twoChildPatientOnlyReward 0 {0, 1} hA = 1
    exact twoChildPatientOnly_gain_joint

/-- On this same two-player child, patient weights lambda=(0,0), mu=(1,0)
satisfy all original full N/F/J rows with the actual patient floor. -/
def twoChildPatientOnlyCertificate :
    PatientWithdrawalRewardCertificate twoChildPatientOnlyReward where
  advanceWeight := 0
  withdrawalWeight := ![1, 0]
  advanceWeight_nonneg := by simp
  withdrawalWeight_nonneg := by intro i; fin_cases i <;> norm_num
  never_row := by
    norm_num [twoChildPatientOnlyReward, twoChildCoalitionCode,
      patientWithdrawalOwnNeverAlternative, Fin.sum_univ_two]
  future_row := by
    intro A hA
    fin_cases A <;> first
    | exact False.elim (Finset.not_nonempty_empty hA)
    | norm_num [twoChildPatientOnlyReward, twoChildCoalitionCode,
        childCoalition_image, twoChildPatientOnly_withdrawalGain, Fin.sum_univ_two]
  join_row := by
    intro A hA
    fin_cases A <;> first
    | exact False.elim (Finset.not_nonempty_empty hA)
    | norm_num [twoChildPatientOnlyReward, twoChildCoalitionCode,
        childCoalition_image, cappedClockJoinedCoalition,
        twoChildPatientOnly_withdrawalGain, Fin.sum_univ_two]

private theorem twoChildPatientOnly_future_impossible (weight : Fin 2 → ℝ)
    (hfuture :
      twoChildPatientOnlyReward ⟨{none}, Finset.singleton_nonempty none⟩ none -
          twoChildPatientOnlyReward ⟨cappedClockChildCoalition {0},
            cappedClockChildCoalition_nonempty (Finset.singleton_nonempty 0)⟩ none ≤
        ∑ i, weight i *
          (twoChildPatientOnlyReward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) -
            twoChildPatientOnlyReward ⟨cappedClockChildCoalition {0},
              cappedClockChildCoalition_nonempty (Finset.singleton_nonempty 0)⟩
              (some i))) : False := by
  norm_num [twoChildPatientOnlyReward, twoChildCoalitionCode,
    childCoalition_image, Fin.sum_univ_two] at hfuture

/-- Deadline F at child singleton zero is one<=zero for every possible weight vector. -/
theorem twoChildPatientOnly_no_deadlineCertificate :
    ¬ Nonempty (DeadlineWithdrawalRewardCertificate twoChildPatientOnlyReward) := by
  rintro ⟨certificate⟩
  exact twoChildPatientOnly_future_impossible certificate.advanceWeight
    (certificate.future_row {0} (Finset.singleton_nonempty 0))

/-- Evaluated security has the same unchanged impossible future row. -/
theorem twoChildPatientOnly_no_evaluatedSecurityCertificate :
    ¬ Nonempty (DeadlineSecurityRewardCertificate twoChildPatientOnlyReward) := by
  rintro ⟨certificate⟩
  exact twoChildPatientOnly_future_impossible certificate.advanceWeight
    (certificate.future_row {0} (Finset.singleton_nonempty 0))

/-- Terminal security likewise cannot repair that original future row. -/
theorem twoChildPatientOnly_no_terminalSecurityCertificate :
    ¬ Nonempty (DeadlineSecurityTerminalRewardCertificate twoChildPatientOnlyReward) := by
  rintro ⟨certificate⟩
  exact twoChildPatientOnly_future_impossible certificate.advanceWeight
    (certificate.future_row {0} (Finset.singleton_nonempty 0))

/-- Patient and deadline full raw criteria are incomparable on one FIXED
child, namely Fin2 inside Option Fin2. The patient-only table also excludes
both security variants; the original deadline-only table has no patient weights.
These are raw-compiler exclusions, not nonexistence of equilibrium. -/
theorem patient_deadline_incomparable_on_fixed_twoPlayerChild :
    Nonempty (PatientWithdrawalRewardCertificate twoChildPatientOnlyReward) ∧
      ¬ Nonempty (DeadlineWithdrawalRewardCertificate twoChildPatientOnlyReward) ∧
      ¬ Nonempty (DeadlineSecurityRewardCertificate twoChildPatientOnlyReward) ∧
      ¬ Nonempty (DeadlineSecurityTerminalRewardCertificate twoChildPatientOnlyReward) ∧
      Nonempty (DeadlineWithdrawalRewardCertificate deadlineOnlyReward) ∧
      ¬ Nonempty (PatientWithdrawalRewardCertificate deadlineOnlyReward) :=
  ⟨⟨twoChildPatientOnlyCertificate⟩, twoChildPatientOnly_no_deadlineCertificate,
    twoChildPatientOnly_no_evaluatedSecurityCertificate,
    twoChildPatientOnly_no_terminalSecurityCertificate,
    ⟨deadlineOnlyCertificate⟩, deadlineOnly_no_patientCertificate⟩

end GameTheory.WithdrawalBoundaryExamples

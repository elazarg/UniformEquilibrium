import UniformEquilibrium.Quitting.Examples.StrictPatientWithdrawalQuietExtension
import UniformEquilibrium.Quitting.Classification.QuietExtension.PatientWithdrawalPerturbation

/-! # A full sixty-coordinate open strict patient class

The radius is the ordinary nested Pi sup distance on the entire reward table.
The weights remain fixed; all patient floors are recomputed from the actual
changed game. Never still has its canonical zero payoff.
-/

noncomputable section

namespace GameTheory.StrictPatientWithdrawal

open scoped BigOperators

theorem neverSlack_perturbation
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (error : ℝ)
    (hclose : ∀ terminal who, |other terminal who - reward terminal who| ≤ error) :
    |neverSlack other - neverSlack reward| ≤ (9 / 2) * error := by
  have hrestricted := abs_quittingChildWithOutsiderReward_sub_le
    reward other (· = 3) outside error hclose
  have hsolo := hrestricted ⟨{some (child 2)}, Finset.singleton_nonempty _⟩ (some (child 2))
  have hnever := hrestricted ⟨{none}, Finset.singleton_nonempty _⟩ none
  have hown := abs_patientWithdrawalOwnNeverAlternative_sub_le
    (childReward reward) (childReward other) error hrestricted (child 0)
  dsimp only [childReward, child] at hsolo hnever hown
  obtain ⟨hsoloLower, hsoloUpper⟩ := abs_le.mp hsolo
  obtain ⟨hneverLower, hneverUpper⟩ := abs_le.mp hnever
  obtain ⟨hownLower, hownUpper⟩ := abs_le.mp hown
  norm_num [child] at hsoloLower hsoloUpper hownLower hownUpper
  simp only [neverSlack, sum_child]
  dsimp only [childReward, child]
  norm_num [advanceWeight, withdrawalWeight, child]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem rowSlack_perturbation
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (error : ℝ)
    (hclose : ∀ terminal who, |other terminal who - reward terminal who| ≤ error)
    (joining : Bool) (A : Finset Child) (hA : A.Nonempty) :
    |rowSlack other joining A hA - rowSlack reward joining A hA| ≤ 9 * error := by
  have hrestricted := abs_quittingChildWithOutsiderReward_sub_le
    reward other (· = 3) outside error hclose
  let row : CappedClockExactLPRow Child :=
    if joining then .joining ⟨A, hA⟩ else .future ⟨A, hA⟩
  have hdelta := abs_cappedClockExactLPDelta_sub_le
    (childReward reward) (childReward other) error hrestricted row (child 2)
  have hbase := abs_cappedClockExactLPBase_sub_le
    (childReward reward) (childReward other) error hrestricted row
  have hgain := abs_patientWithdrawalGainFloor_sub_le
    (childReward reward) (childReward other) error hrestricted (child 0) A hA
  obtain ⟨hdeltaLower, hdeltaUpper⟩ := abs_le.mp hdelta
  obtain ⟨hbaseLower, hbaseUpper⟩ := abs_le.mp hbase
  obtain ⟨hgainLower, hgainUpper⟩ := abs_le.mp hgain
  norm_num [child] at hdeltaLower hdeltaUpper hgainLower hgainUpper
  change |(∑ who, (advanceWeight who * cappedClockExactLPDelta (childReward other) row who +
      withdrawalWeight who * patientWithdrawalGainFloor (childReward other) who A hA)) -
      cappedClockExactLPBase (childReward other) row -
      ((∑ who, (advanceWeight who * cappedClockExactLPDelta (childReward reward) row who +
        withdrawalWeight who * patientWithdrawalGainFloor (childReward reward) who A hA)) -
        cappedClockExactLPBase (childReward reward) row)| ≤ 9 * error
  simp only [sum_child]
  norm_num [advanceWeight, withdrawalWeight, child]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The actual raw-coordinate ball gives strict margins for every patient row. -/
theorem strict_slacks_of_dist_lt
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other reward < 1 / 100) :
    0 < neverSlack other ∧ ∀ joining A hA, 0 < rowSlack other joining A hA := by
  have hcoordinate : ∀ terminal who,
      |other terminal who - reward terminal who| ≤ dist other reward := by
    intro terminal who
    simpa only [Real.dist_eq] using
      (dist_le_pi_dist (other terminal) (reward terminal) who).trans
        (dist_le_pi_dist other reward terminal)
  constructor
  · have h := (abs_le.mp (neverSlack_perturbation other _ hcoordinate)).1
    rw [neverSlack_eq] at h
    linarith
  · intro joining A hA
    have h := (abs_le.mp (rowSlack_perturbation other _ hcoordinate joining A hA)).1
    have hcenter := rowSlack_one_le joining A hA
    linarith

/-- Same displayed weights, fresh actual floors, and no supplied row certificate. -/
def certificateOfDistLt
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other reward < 1 / 100) :
    PatientWithdrawalRewardCertificate (childReward other) :=
  certificateOfSlacks other (strict_slacks_of_dist_lt other hclose).1.le
    (fun joining A hA => ((strict_slacks_of_dist_lt other hclose).2 joining A hA).le)

def certificateFamilyOfDistLt
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other reward < 1 / 100) (who : {who : Fin 4 // who = 3}) :
    PatientWithdrawalRewardCertificate (quittingChildWithOutsiderReward other (· = 3) who) := by
  have heq : who = outside := Subtype.ext who.2
  subst who
  exact certificateOfDistLt other hclose

/-- Every actual child profile obeys the same half-plus-three full-debt bound. -/
theorem outsideDebt_le_of_dist_lt
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other reward < 1 / 100)
    (profile : (quittingGame (quittingDeleteReward other (· = 3))).BehaviorProfile) :
    quittingBehaviorDeviationPayoffCap other
          (quittingLiftDeletedProfile other (· = 3) profile) 3 -
        quittingTerminalPayoff other
          (quittingLiftDeletedProfile other (· = 3) profile) 3 ≤
      (1 / 2) * (quittingBehaviorDeviationPayoffCap
          (quittingDeleteReward other (· = 3)) profile (child 0) -
        quittingTerminalPayoff (quittingDeleteReward other (· = 3)) profile (child 0)) +
      3 * (quittingBehaviorDeviationPayoffCap
          (quittingDeleteReward other (· = 3)) profile (child 2) -
        quittingTerminalPayoff (quittingDeleteReward other (· = 3)) profile (child 2)) := by
  have h := quittingLiftDeletedProfile_outsideDebt_le_of_patientWithdrawal
    (· = 3) other outside (certificateOfDistLt other hclose) profile
  simpa [sum_child, PatientWithdrawalRewardCertificate.debtWeight, certificateOfDistLt,
    certificateOfSlacks, advanceWeight, withdrawalWeight, child, outside] using h

theorem lifted_exploitability_le_of_dist_lt
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other reward < 1 / 100)
    (profile : (quittingGame (quittingDeleteReward other (· = 3))).BehaviorProfile) :
    quittingTerminalExploitability other (quittingLiftDeletedProfile other (· = 3) profile) ≤
      (7 / 2) * quittingTerminalExploitability (quittingDeleteReward other (· = 3)) profile := by
  apply quittingTerminalExploitability_le_of_isεAsymptoticNash
  · exact mul_nonneg (by norm_num) (quittingTerminalExploitability_nonneg _ _)
  · apply isεAsymptoticNash_quietLift_of_outsideTerminalDebtBounds (· = 3) other
      (fun who => (certificateFamilyOfDistLt other hclose who).debtWeight)
      (fun who i => (certificateFamilyOfDistLt other hclose who).debtWeight_nonneg i)
      (7 / 2) (by norm_num) _ (quittingTerminalExploitability_nonneg _ _) profile _
      (isεAsymptoticNash_of_quittingTerminalExploitability_le profile le_rfl)
    · intro who
      have heq : who = outside := Subtype.ext who.2
      subst who
      norm_num [certificateFamilyOfDistLt, certificateOfDistLt, certificateOfSlacks,
        PatientWithdrawalRewardCertificate.debtWeight, sum_child,
        advanceWeight, withdrawalWeight, child]
    · intro who
      exact quittingLiftDeletedProfile_outsideDebt_le_of_patientWithdrawal
        (· = 3) other who (certificateFamilyOfDistLt other hclose who) profile

/-- A full reward neighborhood, not a perturbation of a supplied equilibrium. -/
theorem exists_uniformPayoff_of_dist_lt
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other reward < 1 / 100) :
    ∃ payoff : Payoff (Fin 4), (quittingGame other).IsUniformEquilibriumPayoff none payoff :=
  quittingGame_exists_uniformEquilibriumPayoff_of_finFour_patientWithdrawalFamily
    (· = 3) other (certificateFamilyOfDistLt other hclose)

end GameTheory.StrictPatientWithdrawal

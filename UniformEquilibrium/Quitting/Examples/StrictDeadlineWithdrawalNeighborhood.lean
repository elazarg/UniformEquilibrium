import UniformEquilibrium.Quitting.Examples.StrictDeadlineWithdrawalQuietExtension
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalPerturbation

/-! # The full sixty-coordinate strict deadline neighborhood

The radius 1/512 is the ordinary nested-Pi sup distance, including every free
terminal reward entry. Fixed displayed weights and freshly recomputed floors
produce actual certificates, full evaluated debt bounds and fixed-target UE.
No matrix operator-norm scope is opened on reward tables.
-/

noncomputable section

namespace GameTheory.StrictDeadlineWithdrawal

open FinFourLastPlayerChild
open scoped BigOperators

theorem neverSlack_perturbation
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (error : ℝ)
    (hclose : ∀ terminal who, |other terminal who - reward terminal who| ≤ error) :
    |neverSlack other - neverSlack reward| ≤ (25 / 8) * error := by
  have hrestricted := abs_quittingChildWithOutsiderReward_sub_le
    reward other (· = 3) outside error hclose
  have hzero := hrestricted ⟨{some (child 0)}, Finset.singleton_nonempty _⟩ (some (child 0))
  have htwo := hrestricted ⟨{some (child 2)}, Finset.singleton_nonempty _⟩ (some (child 2))
  have hnever := hrestricted ⟨{none}, Finset.singleton_nonempty _⟩ none
  obtain ⟨hzeroLower, hzeroUpper⟩ := abs_le.mp hzero
  obtain ⟨htwoLower, htwoUpper⟩ := abs_le.mp htwo
  obtain ⟨hneverLower, hneverUpper⟩ := abs_le.mp hnever
  rw [neverSlack_reduced, neverSlack_reduced]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem futureSlack_perturbation
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (error : ℝ)
    (hclose : ∀ terminal who, |other terminal who - reward terminal who| ≤ error)
    (A : Finset Child) (hA : A.Nonempty) :
    |futureSlack other A hA - futureSlack reward A hA| ≤ (25 / 4) * error := by
  have hrestricted := abs_quittingChildWithOutsiderReward_sub_le
    reward other (· = 3) outside error hclose
  have hzero := abs_cappedClockExactLPDelta_sub_le
    (childReward reward) (childReward other) error hrestricted (.future ⟨A, hA⟩) (child 0)
  have htwo := abs_cappedClockExactLPDelta_sub_le
    (childReward reward) (childReward other) error hrestricted (.future ⟨A, hA⟩) (child 2)
  have hbase := abs_cappedClockExactLPBase_sub_le
    (childReward reward) (childReward other) error hrestricted (.future ⟨A, hA⟩)
  obtain ⟨hzeroLower, hzeroUpper⟩ := abs_le.mp hzero
  obtain ⟨htwoLower, htwoUpper⟩ := abs_le.mp htwo
  obtain ⟨hbaseLower, hbaseUpper⟩ := abs_le.mp hbase
  rw [futureSlack_reduced, futureSlack_reduced]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem joiningSlack_perturbation
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (error : ℝ)
    (hclose : ∀ terminal who, |other terminal who - reward terminal who| ≤ error)
    (A : Finset Child) (hA : A.Nonempty) :
    |joiningSlack other A hA - joiningSlack reward A hA| ≤ (33 / 4) * error := by
  have hrestricted := abs_quittingChildWithOutsiderReward_sub_le
    reward other (· = 3) outside error hclose
  have hzero := abs_cappedClockExactLPDelta_sub_le
    (childReward reward) (childReward other) error hrestricted (.joining ⟨A, hA⟩) (child 0)
  have htwo := abs_cappedClockExactLPDelta_sub_le
    (childReward reward) (childReward other) error hrestricted (.joining ⟨A, hA⟩) (child 2)
  have hbase := abs_cappedClockExactLPBase_sub_le
    (childReward reward) (childReward other) error hrestricted (.joining ⟨A, hA⟩)
  have hgain := abs_deadlineWithdrawalGainFloor_sub_le
    (childReward reward) (childReward other) error hrestricted (child 0) A hA
  obtain ⟨hzeroLower, hzeroUpper⟩ := abs_le.mp hzero
  obtain ⟨htwoLower, htwoUpper⟩ := abs_le.mp htwo
  obtain ⟨hbaseLower, hbaseUpper⟩ := abs_le.mp hbase
  obtain ⟨hgainLower, hgainUpper⟩ := abs_le.mp hgain
  rw [joiningSlack_reduced, joiningSlack_reduced]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem coordinate_error_le_dist
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (who : Fin 4) :
    |other terminal who - reward terminal who| ≤ dist other reward := by
  simpa only [Real.dist_eq] using
    (dist_le_pi_dist (other terminal) (reward terminal) who).trans
      (dist_le_pi_dist other reward terminal)

theorem strict_slacks_of_dist_lt
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other reward < 1 / 512) :
    0 < neverSlack other ∧
      (∀ A hA, 0 < futureSlack other A hA) ∧ (∀ A hA, 0 < joiningSlack other A hA) := by
  have hcoordinate := coordinate_error_le_dist other
  refine ⟨?_, ?_, ?_⟩
  · have h := (abs_le.mp (neverSlack_perturbation other _ hcoordinate)).1
    rw [neverSlack_eq] at h
    linarith
  · intro A hA
    have h := (abs_le.mp (futureSlack_perturbation other _ hcoordinate A hA)).1
    have hcenter := futureSlack_five_eighths_le A hA
    linarith
  · intro A hA
    have h := (abs_le.mp (joiningSlack_perturbation other _ hcoordinate A hA)).1
    have hcenter := joiningSlack_half_le A hA
    linarith

def certificateOfDistLt
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other reward < 1 / 512) :
    DeadlineWithdrawalRewardCertificate (childReward other) :=
  certificateOfSlacks other (strict_slacks_of_dist_lt other hclose).1.le
    (fun A hA => ((strict_slacks_of_dist_lt other hclose).2.1 A hA).le)
    (fun A hA => ((strict_slacks_of_dist_lt other hclose).2.2 A hA).le)

/-- Same evaluated d3 ≤ d0+2d2 throughout the exact raw-table ball. -/
theorem outsideEvaluatedDebt_le_of_dist_lt
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other reward < 1 / 512)
    (evaluation : WithTop ℕ → ℝ)
    (hnonneg : ∀ clock, 0 ≤ evaluation clock) (hantitone : Antitone evaluation)
    (profile : (quittingGame (quittingDeleteReward other (· = 3))).BehaviorProfile) :
    quittingBehaviorEvaluatedDeviationPayoffCap other evaluation
          (quittingLiftDeletedProfile other (· = 3) profile) 3 -
        quittingBehaviorEvaluatedPayoff other evaluation
          (quittingLiftDeletedProfile other (· = 3) profile) 3 ≤
      (quittingBehaviorEvaluatedDeviationPayoffCap
          (quittingDeleteReward other (· = 3)) evaluation profile (child 0) -
        quittingBehaviorEvaluatedPayoff
          (quittingDeleteReward other (· = 3)) evaluation profile (child 0)) +
      2 * (quittingBehaviorEvaluatedDeviationPayoffCap
          (quittingDeleteReward other (· = 3)) evaluation profile (child 2) -
        quittingBehaviorEvaluatedPayoff
          (quittingDeleteReward other (· = 3)) evaluation profile (child 2)) := by
  have h := quittingLiftDeletedProfile_outsideEvaluatedDebt_le_of_deadlineWithdrawal
    (· = 3) other outside (certificateOfDistLt other hclose)
    evaluation hnonneg hantitone profile
  simpa [sum_child, DeadlineWithdrawalRewardCertificate.debtWeight, certificateOfDistLt,
    certificateOfSlacks, advanceWeight, withdrawalWeight, child, outside,
    max_eq_right (by norm_num : (8 : ℝ)⁻¹ ≤ 1)] using h

theorem familyMaxWeightOfDistLt_eq_three
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other reward < 1 / 512) :
    deadlineWithdrawalOutsiderMaxWeight (· = 3) other
      (certificateFamily other (certificateOfDistLt other hclose)) = 3 := by
  apply familyMaxWeight_eq_three_of_sum
  change (∑ who, max (advanceWeight who) (withdrawalWeight who)) = 3
  norm_num [sum_child, max_weights, child]

theorem lifted_evaluatedMaxDebt_le_of_dist_lt
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other reward < 1 / 512)
    (evaluation : WithTop ℕ → ℝ)
    (hnonneg : ∀ clock, 0 ≤ evaluation clock) (hantitone : Antitone evaluation)
    (profile : (quittingGame (quittingDeleteReward other (· = 3))).BehaviorProfile) :
    quittingBehaviorEvaluatedMaxDebt other evaluation
        (quittingLiftDeletedProfile other (· = 3) profile) ≤
      3 * quittingBehaviorEvaluatedMaxDebt
        (quittingDeleteReward other (· = 3)) evaluation profile := by
  have h := quittingBehaviorEvaluatedMaxDebt_liftDeletedProfile_le_of_deadlineWithdrawal
    (· = 3) other (certificateFamily other (certificateOfDistLt other hclose))
    evaluation hnonneg hantitone profile
  simpa only [familyMaxWeightOfDistLt_eq_three] using h

/-- Full sixty-coordinate neighborhood with internally produced actual fixed target. -/
theorem exists_uniformPayoff_of_dist_lt
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other reward < 1 / 512) :
    ∃ payoff : Payoff (Fin 4), (quittingGame other).IsUniformEquilibriumPayoff none payoff :=
  quittingGame_exists_uniformEquilibriumPayoff_of_finFour_deadlineWithdrawalFamily
    (· = 3) other (certificateFamily other (certificateOfDistLt other hclose))

end GameTheory.StrictDeadlineWithdrawal

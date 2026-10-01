import UniformEquilibrium.Quitting.Examples.StrictDeadlineWithdrawalCertificate
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalFamilyDebtBounds
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalFinFourExistence

/-! # Actual all-evaluation quiet lifts for the strict deadline table

Each actual child profile and its full behavioral caps are retained. The
weights use max(advance, withdrawal), not their sum. The uniform-payoff target
comes from actual low-cardinality child existence and the fixed-target lift.
-/

noncomputable section

namespace GameTheory.StrictDeadlineWithdrawal

open FinFourLastPlayerChild
open scoped BigOperators

def certificateFamily
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (source : DeadlineWithdrawalRewardCertificate (childReward table))
    (who : {who : Fin 4 // who = 3}) :
    DeadlineWithdrawalRewardCertificate (quittingChildWithOutsiderReward table (· = 3) who) := by
  have heq : who = outside := Subtype.ext who.2
  subst who
  exact source

/-- The unique actual outsider has the same supplied raw weight total as its family. -/
theorem familyMaxWeight_eq_three_of_sum
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (source : DeadlineWithdrawalRewardCertificate (childReward table))
    (hsum : (∑ who, source.debtWeight who) = 3) :
    deadlineWithdrawalOutsiderMaxWeight (· = 3) table (certificateFamily table source) = 3 := by
  have htotal (who : {who : Fin 4 // who = 3}) :
      deadlineWithdrawalOutsiderWeight (· = 3) table (certificateFamily table source) who = 3 := by
    have heq : who = outside := Subtype.ext who.2
    subst who
    exact hsum
  unfold deadlineWithdrawalOutsiderMaxWeight
  apply le_antisymm
  · apply max_le (by norm_num)
    apply Finset.sup'_le
    intro who _
    exact (htotal who).le
  · exact (htotal outside).symm.le.trans
      ((Finset.le_sup' (f := deadlineWithdrawalOutsiderWeight (· = 3) table
        (certificateFamily table source)) (Finset.mem_univ outside)).trans (le_max_right _ _))

theorem familyMaxWeight_eq_three :
    deadlineWithdrawalOutsiderMaxWeight (· = 3) reward (certificateFamily reward certificate) =
      3 := by
  exact familyMaxWeight_eq_three_of_sum reward certificate sum_certificate_debtWeight

/-- Literal d3 ≤ d0 + 2d2 for every actual child profile and allowed evaluation. -/
theorem outsideEvaluatedDebt_le
    (evaluation : WithTop ℕ → ℝ)
    (hnonneg : ∀ clock, 0 ≤ evaluation clock) (hantitone : Antitone evaluation)
    (profile : (quittingGame (quittingDeleteReward reward (· = 3))).BehaviorProfile) :
    quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
          (quittingLiftDeletedProfile reward (· = 3) profile) 3 -
        quittingBehaviorEvaluatedPayoff reward evaluation
          (quittingLiftDeletedProfile reward (· = 3) profile) 3 ≤
      (quittingBehaviorEvaluatedDeviationPayoffCap
          (quittingDeleteReward reward (· = 3)) evaluation profile (child 0) -
        quittingBehaviorEvaluatedPayoff
          (quittingDeleteReward reward (· = 3)) evaluation profile (child 0)) +
      2 * (quittingBehaviorEvaluatedDeviationPayoffCap
          (quittingDeleteReward reward (· = 3)) evaluation profile (child 2) -
        quittingBehaviorEvaluatedPayoff
          (quittingDeleteReward reward (· = 3)) evaluation profile (child 2)) := by
  have h := quittingLiftDeletedProfile_outsideEvaluatedDebt_le_of_deadlineWithdrawal
    (· = 3) reward outside certificate evaluation hnonneg hantitone profile
  simpa [sum_child, certificate_debtWeight, child, outside] using h

/-- The same actual full quiet lift has maximum evaluated debt at most three times the child. -/
theorem lifted_evaluatedMaxDebt_le
    (evaluation : WithTop ℕ → ℝ)
    (hnonneg : ∀ clock, 0 ≤ evaluation clock) (hantitone : Antitone evaluation)
    (profile : (quittingGame (quittingDeleteReward reward (· = 3))).BehaviorProfile) :
    quittingBehaviorEvaluatedMaxDebt reward evaluation
        (quittingLiftDeletedProfile reward (· = 3) profile) ≤
      3 * quittingBehaviorEvaluatedMaxDebt
        (quittingDeleteReward reward (· = 3)) evaluation profile := by
  have h := quittingBehaviorEvaluatedMaxDebt_liftDeletedProfile_le_of_deadlineWithdrawal
    (· = 3) reward (certificateFamily reward certificate) evaluation hnonneg hantitone profile
  simpa only [familyMaxWeight_eq_three] using h

/-- Source-produced fixed target, with actual quiet witnesses selected after the accuracy. -/
theorem exists_uniformPayoffWitnesses :
    ∃ payoff : Payoff (Fin 4), ∀ error : ℝ, 0 < error →
      ∃ (profile : (quittingGame (quittingDeleteReward reward (· = 3))).BehaviorProfile)
        (threshold : ℕ), ∀ horizon, threshold ≤ horizon →
        (quittingGame reward).IsεHorizonNash none horizon error
            (quittingLiftDeletedProfile reward (· = 3) profile) ∧
          ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon
            (quittingLiftDeletedProfile reward (· = 3) profile) who - payoff who| ≤ error :=
  quittingGame_exists_uniformPayoffWitnesses_of_finFour_deadlineWithdrawalFamily
    (· = 3) reward (certificateFamily reward certificate)

theorem exists_uniformPayoff :
    ∃ payoff : Payoff (Fin 4), (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  quittingGame_exists_uniformEquilibriumPayoff_of_finFour_deadlineWithdrawalFamily
    (· = 3) reward (certificateFamily reward certificate)

end GameTheory.StrictDeadlineWithdrawal

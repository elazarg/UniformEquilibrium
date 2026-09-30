import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalSecurityTerminalPlan
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalRestartFullBehavioralDebtCore
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockEvaluatedChildDeletionAdapter

/-!
# Exact terminal debt from untruncated stationary-security rows

The literal raw rows use gamma, while each actual response uses a privately
selected gamma-minus-error plan. The internal comparison retains the error
until after comparison with full behavioral caps, then lets it vanish.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Raw deadline N/F/J rows with the untruncated literal stationary-security
floor. Its fields are finite reward inequalities and nonnegative weights. -/
abbrev DeadlineSecurityTerminalRewardCertificate
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) :=
  DeadlineRestartRewardCertificate reward (deadlineWithdrawalSecurityFloor reward) 0

omit [Nonempty ι] in
/-- Lowering a singleton floor by error changes its withdrawal contribution
by at most that error. Nonsingleton and nonmember contributions do not change. -/
theorem deadlineSecurityGainFloorWithRestart_le_sub_error_add
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (floor error : ℝ) (herror : 0 ≤ error)
    (i : ι) (A : Finset ι) (hA : A.Nonempty) :
    deadlineSecurityGainFloorWithRestart reward floor i A hA ≤
      deadlineSecurityGainFloorWithRestart reward (floor - error) i A hA + error := by
  unfold deadlineSecurityGainFloorWithRestart
  by_cases hsingle : A = {i} <;> simp only [hsingle, ↓reduceIte] <;> linarith

/-- A raw gamma certificate produces the internal finite row error for any
requested approximation. It supplies no favorable profile or cap bound. -/
def DeadlineSecurityTerminalRewardCertificate.approximate
    {reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : DeadlineSecurityTerminalRewardCertificate reward)
    (error : ℝ) (herror : 0 ≤ error) :
    DeadlineRestartRewardCertificate reward
      (fun i => deadlineWithdrawalSecurityFloor reward i - error)
      (error * ∑ i, certificate.withdrawalWeight i) where
  advanceWeight := certificate.advanceWeight
  withdrawalWeight := certificate.withdrawalWeight
  advanceWeight_nonneg := certificate.advanceWeight_nonneg
  withdrawalWeight_nonneg := certificate.withdrawalWeight_nonneg
  never_row := certificate.never_row
  future_row := certificate.future_row
  join_row A hA := by
    calc
      _ ≤ ∑ i, (certificate.advanceWeight i *
          (reward ⟨cappedClockChildCoalition (insert i A),
              cappedClockChildCoalition_nonempty (Finset.insert_nonempty i A)⟩ (some i) -
            reward ⟨cappedClockChildCoalition A,
              cappedClockChildCoalition_nonempty hA⟩ (some i)) +
        certificate.withdrawalWeight i * deadlineSecurityGainFloorWithRestart
          reward (deadlineWithdrawalSecurityFloor reward i) i A hA) := by
        simpa using certificate.join_row A hA
      _ ≤ ∑ i, ((certificate.advanceWeight i *
          (reward ⟨cappedClockChildCoalition (insert i A),
              cappedClockChildCoalition_nonempty (Finset.insert_nonempty i A)⟩ (some i) -
            reward ⟨cappedClockChildCoalition A,
              cappedClockChildCoalition_nonempty hA⟩ (some i)) +
        certificate.withdrawalWeight i * deadlineSecurityGainFloorWithRestart
          reward (deadlineWithdrawalSecurityFloor reward i - error) i A hA) +
        error * certificate.withdrawalWeight i) := by
        apply Finset.sum_le_sum
        intro i _
        have hfloor := mul_le_mul_of_nonneg_left
          (deadlineSecurityGainFloorWithRestart_le_sub_error_add
            reward (deadlineWithdrawalSecurityFloor reward i) error herror i A hA)
          (certificate.withdrawalWeight_nonneg i)
        nlinarith
      _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Each proposed outsider law has the exact terminal maximum-coefficient
bound from literal gamma rows. Positive security is secured by actual finite
clocks; no attained optimal hazard or attained best response is assumed. -/
theorem deadlineSecurityTerminal_outsideStoppingLawGain_le_weighted_behaviorDebt
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : DeadlineSecurityTerminalRewardCertificate reward)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ)) :
    quittingStoppingLawExpectedPayoff reward
        (cappedClockParentSourceLaws childLaws outsideLaw) none -
      quittingStoppingLawExpectedPayoff reward (quietParentStoppingLaws childLaws) none ≤
      ∑ i, certificate.debtWeight i *
        (quittingBehaviorDeviationPayoffCap reward
            (quittingStoppingLawProfile reward (quietParentStoppingLaws childLaws)) (some i) -
          quittingStoppingLawExpectedPayoff reward
            (quietParentStoppingLaws childLaws) (some i)) := by
  refine le_of_forall_pos_le_add fun tolerance htolerance => ?_
  let total := ∑ i, certificate.withdrawalWeight i
  have htotal : 0 ≤ total :=
    Finset.sum_nonneg fun i _ => certificate.withdrawalWeight_nonneg i
  let error := tolerance / (total + 1)
  have hdenom : 0 < total + 1 := by linarith
  have herror : 0 < error := div_pos htolerance hdenom
  have hidentity : error * (total + 1) = tolerance := by
    exact div_mul_cancel₀ tolerance (ne_of_gt hdenom)
  have hbudget : error * total ≤ tolerance := by nlinarith
  have hzero : (0 : WithTop ℕ) ≠ ⊤ := by decide
  let approximate := certificate.approximate error herror.le
  let restart := fun i => deadlineSecurityTerminalRestartFamily reward i error herror
  have hbound := deadlineSecurity_outsideStoppingLawGain_le_weighted_behaviorDebtWithRestart
    reward restart approximate quittingTerminalEvaluation
    quittingTerminalEvaluation_nonneg quittingTerminalEvaluation_antitone
    childLaws outsideLaw (mul_nonneg herror.le htotal)
    (fun i date chosen hchosen => deadlineSecurityTerminalRestartFamily_before
      reward i error herror date chosen hchosen)
    (fun i date opponents hown hfuture => by
      simpa [quittingTerminalEvaluation,
        quittingPureClockEvaluatedPayoff_terminalEvaluation] using
          deadlineSecurityTerminalRestartFamily_floor
            reward i error herror date opponents hown hfuture)
  have hterminal : quittingStoppingLawExpectedPayoff reward
      (cappedClockParentSourceLaws childLaws outsideLaw) none -
      quittingStoppingLawExpectedPayoff reward (quietParentStoppingLaws childLaws) none ≤
      (∑ i, certificate.debtWeight i *
        (quittingBehaviorDeviationPayoffCap reward
            (quittingStoppingLawProfile reward (quietParentStoppingLaws childLaws)) (some i) -
          quittingStoppingLawExpectedPayoff reward
            (quietParentStoppingLaws childLaws) (some i))) + error * total := by
    simpa only [approximate, DeadlineSecurityTerminalRewardCertificate.approximate,
      DeadlineRestartRewardCertificate.debtWeight,
      quittingStoppingLawEvaluatedPayoff_terminalEvaluation,
      quittingBehaviorEvaluatedDeviationPayoffCap_terminalEvaluation,
      quittingTerminalEvaluation, hzero, ↓reduceIte, one_mul, total] using hbound
  exact hterminal.trans (add_le_add le_rfl hbudget)

/-- The unrestricted behavioral outsider cap obeys the exact terminal gamma
bound, after the privately selected plan error has vanished. -/
theorem deadlineSecurityTerminal_outsideBehaviorDebt_le_weighted_childDebt
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : DeadlineSecurityTerminalRewardCertificate reward)
    (childLaws : ι → PMF (Option ℕ)) :
    quittingBehaviorDeviationPayoffCap reward
        (quittingStoppingLawProfile reward (quietParentStoppingLaws childLaws)) none -
      quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward (quietParentStoppingLaws childLaws)) none ≤
      ∑ i, certificate.debtWeight i *
        (quittingBehaviorDeviationPayoffCap reward
            (quittingStoppingLawProfile reward (quietParentStoppingLaws childLaws)) (some i) -
          quittingTerminalPayoff reward
            (quittingStoppingLawProfile reward (quietParentStoppingLaws childLaws)) (some i)) := by
  have h := outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt_add_const_of_stoppingLaw
    reward certificate.debtWeight quittingTerminalEvaluation childLaws 0
    (fun outsideLaw => by
      simpa only [quittingStoppingLawEvaluatedPayoff_terminalEvaluation,
        quittingBehaviorEvaluatedDeviationPayoffCap_terminalEvaluation, add_zero] using
          deadlineSecurityTerminal_outsideStoppingLawGain_le_weighted_behaviorDebt
            reward certificate childLaws outsideLaw)
  simpa only [quittingBehaviorEvaluatedDeviationPayoffCap_terminalEvaluation,
    quittingBehaviorEvaluatedPayoff_terminalEvaluation, add_zero] using h

end GameTheory

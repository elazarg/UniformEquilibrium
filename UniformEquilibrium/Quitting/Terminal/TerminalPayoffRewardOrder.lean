import UniformEquilibrium.Quitting.PayoffProcess.TailStepSelector

/-! # Terminal payoff order and one-sided reward perturbations

The same behavioral profile and every unilateral replacement are used at both
tables. A nonnegative reward perturbation incurs only one perturbation error
when transferring Nash from the increased table back to the original table.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι]

/-- Ordering one player's rewards orders that player's payoff at the same profile. -/
theorem quittingTerminalPayoff_le_of_reward_le
    (first second : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame first).BehaviorProfile) (who : ι)
    (hle : ∀ terminal, first terminal who ≤ second terminal who) :
    quittingTerminalPayoff first profile who ≤
      quittingTerminalPayoff second profile who := by
  classical
  unfold quittingTerminalPayoff
  apply Finset.sum_le_sum
  intro terminal _
  rw [← quittingAbsorbedMassLimit_reward_irrelevant first second]
  exact mul_le_mul_of_nonneg_left (hle terminal)
    (quittingAbsorbedMassLimit_nonneg first profile terminal)

/-- Nash at an increased reward table gives Nash at the original table with
one additional reward-distance error, for every behavioral deviation. -/
theorem IsεAsymptoticNash.of_nonnegative_reward_perturbation
    [DecidableEq ι]
    (first second : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame first).BehaviorProfile)
    {error delta : ℝ} (hdelta : 0 ≤ delta)
    (hle : ∀ terminal who, first terminal who ≤ second terminal who)
    (hclose : ∀ terminal who, |second terminal who - first terminal who| ≤ delta)
    (hnash : (quittingGame second).IsεAsymptoticNash
      (quittingTerminalPayoff second) error profile) :
    (quittingGame first).IsεAsymptoticNash
      (quittingTerminalPayoff first) (error + delta) profile := by
  intro who deviation
  have hdev := quittingTerminalPayoff_le_of_reward_le first second
    (Function.update profile who deviation) who (fun terminal => hle terminal who)
  have hbase := abs_quittingTerminalPayoff_sub_le_of_forall_abs_sub_le
    second first profile who hdelta hclose
  have hnashWho := hnash who deviation
  have hbaseUpper := (abs_le.mp hbase).2
  calc
    quittingTerminalPayoff first (Function.update profile who deviation) who ≤
        quittingTerminalPayoff second profile who + error := hdev.trans hnashWho
    _ ≤ quittingTerminalPayoff first profile who + (error + delta) := by
      linarith only [hbaseUpper]

end GameTheory

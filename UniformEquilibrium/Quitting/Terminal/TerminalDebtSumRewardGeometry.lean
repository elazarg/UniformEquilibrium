import UniformEquilibrium.Quitting.Terminal.TerminalDebtSumInf
import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityRewardRobustness

/-! # Reward geometry of the literal SUM-debt infimum

The same actual behavioral profile is reused across reward tables. Total debt
and its literal behavioral infimum are Lipschitz in the reward table and
homogeneous under one common nonnegative reward scale.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Total debt of one actual profile changes by at most twice the player
count times the uniform coordinate error. -/
theorem abs_quittingTerminalDebtSum_sub_le_of_reward_close
    (first second : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame first).BehaviorProfile)
    {delta : ℝ}
    (hclose : ∀ terminal player,
      |first terminal player - second terminal player| ≤ delta) :
    |quittingTerminalDebtSum first profile -
        quittingTerminalDebtSum second profile| ≤ 2 * Fintype.card ι * delta := by
  classical
  have hplayer : ∀ player,
      |quittingTerminalDeviationDebt first profile player -
        quittingTerminalDeviationDebt second profile player| ≤ 2 * delta := by
    intro player
    have hdelta : 0 ≤ delta := (abs_nonneg _).trans
      (hclose ⟨{player}, Finset.singleton_nonempty player⟩ player)
    have hcap := abs_quittingContinuationBestResponseValue_sub_le_of_reward_close
      first second profile player hdelta hclose
    have hpay := abs_quittingTerminalPayoff_sub_le_of_forall_abs_sub_le
      first second profile player hdelta hclose
    unfold quittingTerminalDeviationDebt
    rw [abs_le] at hcap hpay ⊢
    constructor <;> linarith
  unfold quittingTerminalDebtSum
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ player, (quittingTerminalDeviationDebt first profile player -
        quittingTerminalDeviationDebt second profile player)| ≤
        ∑ player, |quittingTerminalDeviationDebt first profile player -
          quittingTerminalDeviationDebt second profile player| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _player : ι, 2 * delta :=
      Finset.sum_le_sum fun player _ => hplayer player
    _ = 2 * Fintype.card ι * delta := by simp; ring

private theorem quittingTerminalDebtSumInf_le_add_of_reward_close
    (first second : {S : Finset ι // S.Nonempty} → Payoff ι)
    {delta : ℝ}
    (hclose : ∀ terminal player,
      |first terminal player - second terminal player| ≤ delta) :
    quittingTerminalDebtSumInf second ≤
      quittingTerminalDebtSumInf first + 2 * Fintype.card ι * delta := by
  have hrange : (Set.range (quittingTerminalDebtSum first)).Nonempty :=
    ⟨_, quittingAlwaysContinueProfile first, rfl⟩
  have hlower : quittingTerminalDebtSumInf second - 2 * Fintype.card ι * delta ≤
      quittingTerminalDebtSumInf first := by
    apply (le_csInf_iff
      (bddBelow_range_quittingTerminalDebtSum (reward := first)) hrange).2
    rintro _ ⟨profile, rfl⟩
    have hpoint := abs_quittingTerminalDebtSum_sub_le_of_reward_close
      first second profile hclose
    have hinf := quittingTerminalDebtSumInf_le (reward := second) profile
    have hbound := (abs_le.mp hpoint).1
    linarith
  linarith

/-- The literal SUM-debt infimum is Lipschitz under a uniform reward error. -/
theorem abs_quittingTerminalDebtSumInf_sub_le_of_reward_close
    (first second : {S : Finset ι // S.Nonempty} → Payoff ι)
    {delta : ℝ}
    (hclose : ∀ terminal player,
      |first terminal player - second terminal player| ≤ delta) :
    |quittingTerminalDebtSumInf first - quittingTerminalDebtSumInf second| ≤
      2 * Fintype.card ι * delta := by
  have hsecond := quittingTerminalDebtSumInf_le_add_of_reward_close
    first second hclose
  have hreverse : ∀ terminal player,
      |second terminal player - first terminal player| ≤ delta := by
    intro terminal player
    simpa only [abs_sub_comm] using hclose terminal player
  have hfirst := quittingTerminalDebtSumInf_le_add_of_reward_close
    second first hreverse
  rw [abs_le]
  constructor <;> linarith

/-- The reward-table Lipschitz constant is twice the number of players. -/
theorem lipschitzWith_quittingTerminalDebtSumInf :
    LipschitzWith (2 * (Fintype.card ι : NNReal))
      (quittingTerminalDebtSumInf (ι := ι)) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  have hclose : ∀ terminal player,
      |first terminal player - second terminal player| ≤ dist first second := by
    intro terminal player
    rw [← Real.dist_eq]
    exact (dist_le_pi_dist (first terminal) (second terminal) player).trans
      (dist_le_pi_dist first second terminal)
  simpa only [Real.dist_eq, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast]
    using abs_quittingTerminalDebtSumInf_sub_le_of_reward_close
      first second hclose

/-- The literal SUM-debt infimum is continuous in the numerical table. -/
theorem continuous_quittingTerminalDebtSumInf :
    Continuous (quittingTerminalDebtSumInf (ι := ι)) :=
  lipschitzWith_quittingTerminalDebtSumInf.continuous

/-- One common nonnegative scale multiplies total actual-profile debt exactly. -/
theorem quittingTerminalDebtSum_scaleQuittingReward
    {scale : ℝ} (hscale : 0 ≤ scale)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalDebtSum (scaleQuittingReward scale reward) profile =
      scale * quittingTerminalDebtSum reward profile := by
  unfold quittingTerminalDebtSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro player _
  unfold quittingTerminalDeviationDebt
  rw [quittingContinuationBestResponseValue_scaleQuittingReward hscale,
    quittingTerminalPayoff_scaleQuittingReward]
  ring

/-- One common nonnegative scale multiplies the literal SUM infimum exactly. -/
theorem quittingTerminalDebtSumInf_scaleQuittingReward
    {scale : ℝ} (hscale : 0 ≤ scale)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingTerminalDebtSumInf (scaleQuittingReward scale reward) =
      scale * quittingTerminalDebtSumInf reward := by
  unfold quittingTerminalDebtSumInf
  change (⨅ profile, quittingTerminalDebtSum
      (scaleQuittingReward scale reward) profile) =
    scale * (⨅ profile, quittingTerminalDebtSum reward profile)
  rw [Real.mul_iInf_of_nonneg hscale]
  congr 1
  funext profile
  exact quittingTerminalDebtSum_scaleQuittingReward hscale reward profile

/-- Positive common scaling preserves zero SUM infimum. -/
theorem quittingTerminalDebtSumInf_scaleQuittingReward_eq_zero_iff
    {scale : ℝ} (hscale : 0 < scale)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingTerminalDebtSumInf (scaleQuittingReward scale reward) = 0 ↔
      quittingTerminalDebtSumInf reward = 0 := by
  rw [quittingTerminalDebtSumInf_scaleQuittingReward hscale.le]
  exact mul_eq_zero.trans (or_iff_right hscale.ne')

/-- Positive common scaling preserves positive SUM infimum. -/
theorem quittingTerminalDebtSumInf_scaleQuittingReward_pos_iff
    {scale : ℝ} (hscale : 0 < scale)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    0 < quittingTerminalDebtSumInf (scaleQuittingReward scale reward) ↔
      0 < quittingTerminalDebtSumInf reward := by
  rw [quittingTerminalDebtSumInf_scaleQuittingReward hscale.le]
  exact mul_pos_iff_of_pos_left hscale

end GameTheory

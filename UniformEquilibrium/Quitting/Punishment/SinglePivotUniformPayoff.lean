import UniformEquilibrium.Quitting.Punishment.SinglePivotTailLift
import UniformEquilibrium.Quitting.Punishment.SinglePivotProfileDebtTransport
import UniformEquilibrium.Quitting.Terminal.TargetTail.UniformTargetTerminalSequence

/-! # Exact fixed-target uniform payoff transport under single-pivot normalization -/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The terminal-only affine normalization transports an actual payoff limit
when the same profiles' joint Never mass vanishes. -/
theorem quittingTerminalPayoff_singlePivotNormalized_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile) (target : Payoff ι)
    (htarget : Tendsto (fun n ↦ quittingTerminalPayoff reward (profiles n)) atTop (nhds target))
    (hreach : Tendsto (fun n ↦ quittingLiveMassLimit reward (profiles n)) atTop (nhds 0)) :
    Tendsto (fun n ↦ quittingTerminalPayoff
      (quittingSinglePivotNormalizedReward reward pivot) (profiles n)) atTop
      (nhds (fun who ↦ (target who - quittingSinglePivotOffset reward pivot who) /
        quittingSoloReward reward pivot pivot)) := by
  apply tendsto_pi_nhds.mpr
  intro who
  have hcoordinate := tendsto_pi_nhds.mp htarget who
  have h := ((hcoordinate.sub_const (quittingSinglePivotOffset reward pivot who)).add
    (hreach.const_mul (quittingSinglePivotOffset reward pivot who))).div_const
      (quittingSoloReward reward pivot pivot)
  simpa only [mul_zero, add_zero, quittingTerminalPayoff_singlePivotNormalized] using h

/-- Forward transport keeps the target fixed and uses the unchanged actual
terminal approximants. The positive pivot makes their Never mass vanish. -/
theorem isUniformEquilibriumPayoff_singlePivotNormalized_of_original
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι) (target : Payoff ι)
    (hpivot : 0 < quittingSoloReward reward pivot pivot)
    (huniform : (quittingGame reward).IsUniformEquilibriumPayoff none target) :
    (quittingGame (quittingSinglePivotNormalizedReward reward pivot)).IsUniformEquilibriumPayoff
      none (fun who ↦ (target who - quittingSinglePivotOffset reward pivot who) /
        quittingSoloReward reward pivot pivot) := by
  letI : Nonempty ι := ⟨pivot⟩
  obtain ⟨profiles, htarget, herror⟩ :=
    exists_terminalProfile_sequence_exploitability_tendsto_zero_of_uniformPayoff
      reward target huniform
  let transformed := quittingSinglePivotNormalizedReward reward pivot
  have hreach : Tendsto (fun n ↦ quittingLiveMassLimit reward (profiles n)) atTop (nhds 0) := by
    apply squeeze_zero (fun n ↦ quittingLiveMassLimit_nonneg reward (profiles n))
      (fun n ↦ quittingLiveMassLimit_le_exploitability_div_singleton
        reward (profiles n) pivot hpivot)
    simpa only [zero_div] using herror.div_const (quittingSoloReward reward pivot pivot)
  have hnewError : Tendsto (fun n ↦ quittingTerminalExploitability transformed (profiles n))
      atTop (nhds 0) := by
    apply squeeze_zero (fun n ↦ quittingTerminalExploitability_nonneg transformed (profiles n))
      (fun n ↦ quittingTerminalExploitability_singlePivotNormalized_le reward pivot (profiles n)
        (abs_reward_le_quittingRewardBound reward) hpivot)
    simpa only [mul_zero] using herror.const_mul
      (1 / quittingSoloReward reward pivot pivot +
        quittingRewardBound reward / quittingSoloReward reward pivot pivot ^ 2)
  have hnewTarget : Tendsto (fun n ↦ quittingTerminalPayoff transformed (profiles n)) atTop
      (nhds (fun who ↦ (target who - quittingSinglePivotOffset reward pivot who) /
        quittingSoloReward reward pivot pivot)) :=
    quittingTerminalPayoff_singlePivotNormalized_tendsto
      reward pivot profiles target htarget hreach
  exact quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto transformed _
    (fun n ↦ quittingTerminalExploitability transformed (profiles n)) profiles hnewError
    (Eventually.of_forall fun n ↦
      isεAsymptoticNash_of_quittingTerminalExploitability_le
        (reward := transformed) (profiles n) le_rfl).frequently
    hnewTarget

/-- Reverse transport uses a new same-prefix lift at each accuracy; all
resulting original payoffs converge to the one affine image of the source target. -/
theorem isUniformEquilibriumPayoff_original_of_singlePivotNormalized
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι) (target : Payoff ι)
    (hpivot : 0 < quittingSoloReward reward pivot pivot)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤ quittingSoloReward reward who who)
    (huniform : (quittingGame
      (quittingSinglePivotNormalizedReward reward pivot)).IsUniformEquilibriumPayoff none target) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSinglePivotOffset reward pivot +
        quittingSoloReward reward pivot pivot • target) := by
  letI : Nonempty ι := ⟨pivot⟩
  let transformed := quittingSinglePivotNormalizedReward reward pivot
  obtain ⟨profiles, htarget, herror⟩ :=
    exists_terminalProfile_sequence_exploitability_tendsto_zero_of_uniformPayoff
      transformed target huniform
  let margin : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  let reach : ℕ → ℝ := fun n ↦ quittingTerminalExploitability transformed (profiles n) + margin n
  have hmargin : ∀ n, 0 < margin n := by intro n; dsimp [margin]; positivity
  have hmarginLimit : Tendsto margin atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hreachLimit : Tendsto reach atTop (nhds 0) := by
    simpa only [add_zero] using herror.add hmarginLimit
  have hexists (n : ℕ) := exists_singlePivot_samePrefix_terminal_lift
    reward pivot (profiles n) (abs_reward_le_quittingRewardBound reward) hpivot hnormal
    ((quittingLiveMassLimit_singlePivotNormalized_le_exploitability
      reward pivot (profiles n) hpivot.ne').trans_lt (lt_add_of_pos_right _ (hmargin n)))
    (hmargin n)
  choose cutoff payer root _ _ hbound hpayoff using hexists
  let original : ℕ → (quittingGame reward).BehaviorProfile := fun n ↦
    quittingStationaryTailSpliceProfile reward (profiles n) (cutoff n) (root n)
  have hnewError : Tendsto (fun n ↦ quittingTerminalExploitability reward (original n))
      atTop (nhds 0) := by
    apply squeeze_zero (fun n ↦ quittingTerminalExploitability_nonneg reward (original n)) hbound
    have h := ((herror.const_mul (quittingSoloReward reward pivot pivot)).add
      ((hreachLimit.add hreachLimit.sqrt).const_mul (2 * quittingRewardBound reward))).add
        hmarginLimit
    simpa only [Real.sqrt_zero, mul_zero, add_zero] using h
  have hpayoffError : Tendsto (fun n ↦ quittingTerminalPayoff reward (original n) -
        (quittingSinglePivotOffset reward pivot + quittingSoloReward reward pivot pivot •
          quittingTerminalPayoff transformed (profiles n))) atTop (nhds 0) := by
    apply squeeze_zero_norm hpayoff
    simpa only [mul_zero] using hreachLimit.const_mul (2 * quittingRewardBound reward)
  have hnewTarget : Tendsto (fun n ↦ quittingTerminalPayoff reward (original n)) atTop
      (nhds (quittingSinglePivotOffset reward pivot + quittingSoloReward reward pivot pivot •
        target)) := by
    have htranslated : Tendsto (fun n ↦ quittingSinglePivotOffset reward pivot +
        quittingSoloReward reward pivot pivot • quittingTerminalPayoff transformed (profiles n))
        atTop (nhds (quittingSinglePivotOffset reward pivot +
          quittingSoloReward reward pivot pivot • target)) :=
      tendsto_const_nhds.add (htarget.const_smul (quittingSoloReward reward pivot pivot))
    have h := hpayoffError.add htranslated
    simpa only [sub_add_cancel, zero_add] using h
  exact quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto reward _
    (fun n ↦ quittingTerminalExploitability reward (original n)) original hnewError
    (Eventually.of_forall fun n ↦
      isεAsymptoticNash_of_quittingTerminalExploitability_le (original n) le_rfl).frequently
    hnewTarget

/-- Literal equality of the fixed-target uniform payoff sets. The reverse
inclusion uses original punishment normality, not a translated Never payoff. -/
theorem uniformEquilibriumPayoffSet_singlePivotNormalized
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (hpivot : 0 < quittingSoloReward reward pivot pivot)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤ quittingSoloReward reward who who) :
    {target : Payoff ι | (quittingGame reward).IsUniformEquilibriumPayoff none target} =
      (fun target : Payoff ι ↦ quittingSinglePivotOffset reward pivot +
        quittingSoloReward reward pivot pivot • target) ''
      {target : Payoff ι |
        (quittingGame (quittingSinglePivotNormalizedReward reward pivot)).IsUniformEquilibriumPayoff
          none target} := by
  ext target
  constructor
  · intro htarget
    refine ⟨(fun who ↦ (target who - quittingSinglePivotOffset reward pivot who) /
      quittingSoloReward reward pivot pivot),
      isUniformEquilibriumPayoff_singlePivotNormalized_of_original
        reward pivot target hpivot htarget,
      ?_⟩
    funext who
    change quittingSinglePivotOffset reward pivot who + quittingSoloReward reward pivot pivot *
      ((target who - quittingSinglePivotOffset reward pivot who) /
        quittingSoloReward reward pivot pivot) = target who
    field_simp [ne_of_gt hpivot]
    ring
  · rintro ⟨normalizedTarget, htarget, rfl⟩
    exact isUniformEquilibriumPayoff_original_of_singlePivotNormalized
      reward pivot normalizedTarget hpivot hnormal htarget

end GameTheory

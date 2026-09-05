import UniformEquilibrium.Quitting.Punishment.FiniteReplyPrefixCompletion
import UniformEquilibrium.Quitting.Punishment.SinglePivotPunishment
import UniformEquilibrium.Quitting.Terminal.TerminalExploitability

/-! # Actual same-prefix lifting out of a zero-Never normalization -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem quittingLiveMassLimit_congr_reward
    (first second : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame first).BehaviorProfile) :
    quittingLiveMassLimit first profile = quittingLiveMassLimit second profile := by
  have hfirst := quittingLiveMassLimit_add_sum_absorbedMassLimit first profile
  have hsecond := quittingLiveMassLimit_add_sum_absorbedMassLimit second profile
  simp_rw [QuittingLCPClassification.quittingAbsorbedMassLimit_congr_reward
    first second profile] at hfirst
  linarith

/-- One fixed independently chosen punishment root lifts the actual normalized
source. Every source row before the cutoff is retained, and all complete
behavioral deviations are capped. Never still pays zero in both games. -/
theorem exists_singlePivot_samePrefix_terminal_lift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (profile : (quittingGame (quittingSinglePivotNormalizedReward reward pivot)).BehaviorProfile)
    {bound reach slack : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hpivot : 0 < quittingSoloReward reward pivot pivot)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤ quittingSoloReward reward who who)
    (hreach : quittingLiveMassLimit
      (quittingSinglePivotNormalizedReward reward pivot) profile < reach)
    (hslack : 0 < slack) :
    letI : Nonempty ι := ⟨pivot⟩
    ∃ cutoff : ℕ, ∃ target : ι, ∃ root : ι → PMF Bool,
      quittingStationaryUnilateralCap reward root target <
        quittingPunishmentValue reward target + slack / 2 ∧
      (∀ time < cutoff, ∀ who (history : (quittingGame reward).Hist time),
        quittingStationaryTailSpliceProfile reward profile cutoff root who time history =
          profile who time history) ∧
      quittingTerminalExploitability reward
          (quittingStationaryTailSpliceProfile reward profile cutoff root) ≤
        quittingSoloReward reward pivot pivot * quittingTerminalExploitability
            (quittingSinglePivotNormalizedReward reward pivot) profile +
          2 * bound * (reach + Real.sqrt reach) + slack ∧
      ‖quittingTerminalPayoff reward
          (quittingStationaryTailSpliceProfile reward profile cutoff root) -
        (quittingSinglePivotOffset reward pivot +
          quittingSoloReward reward pivot pivot •
            quittingTerminalPayoff (quittingSinglePivotNormalizedReward reward pivot) profile)‖ ≤
        2 * bound * reach := by
  letI : Nonempty ι := ⟨pivot⟩
  have hbound : 0 ≤ bound :=
    (abs_nonneg _).trans (hreward (quittingSingletonTerminal pivot) pivot)
  have hreach' : quittingLiveMassLimit reward profile < reach := by
    rwa [quittingLiveMassLimit_congr_reward
      (quittingSinglePivotNormalizedReward reward pivot) reward profile] at hreach
  have hreachpos : 0 < reach :=
    (quittingLiveMassLimit_nonneg reward profile).trans_lt hreach'
  let tolerance := slack / (4 * (bound + 1))
  have htolerance : 0 < tolerance := by dsimp [tolerance]; positivity
  have htolerance_bound : 2 * bound * tolerance + slack / 2 ≤ slack := by
    have hden : tolerance * (4 * (bound + 1)) = slack :=
      div_mul_cancel₀ _ (by positivity)
    nlinarith
  obtain ⟨cutoff, target, root, hroot, _, hprefix, hcap, hpayoff⟩ :=
    exists_stationaryTailSplice_finiteReply_completion reward profile hreward hnormal hreach'
      htolerance (half_pos hslack)
  have hvalue (who : ι) :
      quittingTerminalPayoff reward profile who +
          quittingSinglePivotOffset reward pivot who * quittingLiveMassLimit reward profile =
        quittingSinglePivotOffset reward pivot who + quittingSoloReward reward pivot pivot *
          quittingTerminalPayoff
            (quittingSinglePivotNormalizedReward reward pivot) profile who := by
    rw [quittingTerminalPayoff_singlePivotNormalized reward pivot who profile]
    field_simp [ne_of_gt hpivot]
    ring
  have hfinite (who : ι) : quittingFinitePureReplyValue reward profile who =
      quittingSinglePivotOffset reward pivot who + quittingSoloReward reward pivot pivot *
        quittingContinuationBestResponseValue (quittingSinglePivotNormalizedReward reward pivot)
          profile who := by
    rw [quittingContinuationBestResponseValue_singlePivotNormalized reward pivot who profile hpivot]
    field_simp [ne_of_gt hpivot]
    ring
  refine ⟨cutoff, target, root, hroot, hprefix, ?_, ?_⟩
  · rw [quittingTerminalExploitability_eq_max_debt]
    apply QuittingBoundaryHolonomy.finitePlayerMax_le
    intro who
    have hc := hcap who
    have hu := neg_le_of_abs_le (hpayoff who (quittingSinglePivotOffset reward pivot who)
      (abs_quittingSinglePivotOffset_le reward pivot who hreward))
    rw [hvalue who] at hu
    rw [hfinite who] at hc
    have hdebt := mul_le_mul_of_nonneg_left
      (quittingTerminalDeviationDebt_le_exploitability
        (quittingSinglePivotNormalizedReward reward pivot) profile who) hpivot.le
    change quittingContinuationBestResponseValue reward
        (quittingStationaryTailSpliceProfile reward profile cutoff root) who -
      quittingTerminalPayoff reward
        (quittingStationaryTailSpliceProfile reward profile cutoff root) who ≤ _
    change quittingSoloReward reward pivot pivot *
        (quittingContinuationBestResponseValue (quittingSinglePivotNormalizedReward reward pivot)
            profile who -
          quittingTerminalPayoff (quittingSinglePivotNormalizedReward reward pivot) profile who) ≤ _
      at hdebt
    linarith
  · apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * bound * reach)).mpr
    intro who
    have h := hpayoff who (quittingSinglePivotOffset reward pivot who)
      (abs_quittingSinglePivotOffset_le reward pivot who hreward)
    rw [hvalue who] at h
    exact h

end GameTheory

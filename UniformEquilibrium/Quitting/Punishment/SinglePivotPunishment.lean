import UniformEquilibrium.Quitting.Root.SinglePivotNormalization
import UniformEquilibrium.Quitting.Terminal.TerminalAffineReward
import UniformEquilibrium.Quitting.Punishment.FinitePureReplyPunishment

/-! # Exact punishment transport under single-pivot normalization -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- With a nonnegative own singleton, Never does not change the finite-only
punishment infimum. -/
theorem quittingFinitePureReplyPunishmentValue_eq_punishmentValue_of_solo_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    (hsolo : 0 ≤ reward (quittingSingletonTerminal who) who) :
    quittingFinitePureReplyPunishmentValue reward who = quittingPunishmentValue reward who := by
  unfold quittingFinitePureReplyPunishmentValue quittingPunishmentValue
  congr 1
  funext profile
  exact (quittingContinuationBestResponseValue_eq_finitePureReplyValue_of_solo_nonneg
    reward profile who hsolo).symm

omit [Fintype ι] in
theorem quittingSoloReward_singlePivotNormalized_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot who : ι)
    (hpivot : quittingSoloReward reward pivot pivot ≠ 0) :
    0 ≤ quittingSoloReward (quittingSinglePivotNormalizedReward reward pivot) who who := by
  change 0 ≤ quittingSinglePivotNormalizedReward reward pivot (quittingSingletonTerminal who) who
  rw [quittingSoloReward_singlePivotNormalized reward pivot who hpivot]
  split <;> norm_num

/-- Literal unchanged-profile payoff transport includes the original
all-Never probability. -/
theorem quittingTerminalPayoff_singlePivotNormalized
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot who : ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalPayoff (quittingSinglePivotNormalizedReward reward pivot) profile who =
      (quittingTerminalPayoff reward profile who - quittingSinglePivotOffset reward pivot who +
        quittingSinglePivotOffset reward pivot who * quittingLiveMassLimit reward profile) /
          quittingSoloReward reward pivot pivot := by
  rw [quittingSinglePivotNormalizedReward_eq_playerwiseAffine,
    quittingTerminalPayoff_playerwiseAffine]
  change (1 / quittingSoloReward reward pivot pivot) * _ +
    (-quittingSinglePivotOffset reward pivot who / quittingSoloReward reward pivot pivot) *
      (1 - quittingLiveMassLimit reward profile) = _
  ring

/-- Every complete source profile has this exact transformed unrestricted
behavioral cap, expressed through its original finite-date response supremum. -/
theorem quittingContinuationBestResponseValue_singlePivotNormalized
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot who : ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (hpivot : 0 < quittingSoloReward reward pivot pivot) :
    quittingContinuationBestResponseValue
        (quittingSinglePivotNormalizedReward reward pivot) profile who =
      (quittingFinitePureReplyValue reward profile who -
        quittingSinglePivotOffset reward pivot who) / quittingSoloReward reward pivot pivot := by
  rw [quittingContinuationBestResponseValue_eq_finitePureReplyValue_of_solo_nonneg
    (quittingSinglePivotNormalizedReward reward pivot) profile who
      (quittingSoloReward_singlePivotNormalized_nonneg reward pivot who hpivot.ne')]
  rw [quittingSinglePivotNormalizedReward_eq_playerwiseAffine,
    quittingFinitePureReplyValue_playerwiseAffine reward _ _ profile who
      (one_div_pos.mpr hpivot)]
  change (1 / quittingSoloReward reward pivot pivot) * _ +
    (-quittingSinglePivotOffset reward pivot who / quittingSoloReward reward pivot pivot) = _
  ring

/-- Normality is needed on the original coordinate; the conclusion concerns
the full behavioral punishment values, not a finite-menu approximation. -/
theorem quittingPunishmentValue_singlePivotNormalized
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot who : ι)
    (hpivot : 0 < quittingSoloReward reward pivot pivot)
    (hnormal : quittingPunishmentValue reward who ≤ quittingSoloReward reward who who) :
    quittingPunishmentValue (quittingSinglePivotNormalizedReward reward pivot) who =
      (quittingPunishmentValue reward who - quittingSinglePivotOffset reward pivot who) /
        quittingSoloReward reward pivot pivot := by
  rw [← quittingFinitePureReplyPunishmentValue_eq_punishmentValue_of_solo_nonneg
    _ who (quittingSoloReward_singlePivotNormalized_nonneg reward pivot who hpivot.ne')]
  rw [quittingSinglePivotNormalizedReward_eq_playerwiseAffine,
    quittingFinitePureReplyPunishmentValue_playerwiseAffine reward _ _ who
      (one_div_pos.mpr hpivot), quittingFinitePureReplyPunishmentValue_eq_min,
    min_eq_left hnormal]
  change (1 / quittingSoloReward reward pivot pivot) * _ +
    (-quittingSinglePivotOffset reward pivot who / quittingSoloReward reward pivot pivot) = _
  ring

/-- Original coordinatewise punishment normality is preserved. -/
theorem quittingPunishmentValue_singlePivotNormalized_le_solo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot who : ι)
    (hpivot : 0 < quittingSoloReward reward pivot pivot)
    (hnormal : quittingPunishmentValue reward who ≤ quittingSoloReward reward who who) :
    quittingPunishmentValue (quittingSinglePivotNormalizedReward reward pivot) who ≤
      quittingSoloReward (quittingSinglePivotNormalizedReward reward pivot) who who := by
  rw [quittingPunishmentValue_singlePivotNormalized reward pivot who hpivot hnormal]
  change _ ≤ (quittingSoloReward reward who who - quittingSinglePivotOffset reward pivot who) /
    quittingSoloReward reward pivot pivot
  exact div_le_div_of_nonneg_right (by linarith) hpivot.le

end GameTheory
